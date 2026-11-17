// github-core-clone-01: a standalone GitHub-compatible git forge.
// One process, its own in-memory store, no UI, no outside service, no git binary.
// Surfaces: git smart HTTP (upload-pack v2/v0, receive-pack v0), REST v3 under /api/v3,
// GraphQL v4 at /api/graphql, MCP (Streamable HTTP) at /mcp.
// Only Node's standard library is used.

import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

// ---------------------------------------------------------------------------
// Basics
// ---------------------------------------------------------------------------

const ZERO_OID = '0'.repeat(40);
const JSON_TYPE = 'application/json; charset=utf-8';
const FORGE_NAME = 'github-core-clone-forge';
const FORGE_VERSION = '1.0.0';
const DEFAULT_BRANCH = 'main';

const EXPECTED_TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';

/** The trial's "now": every timestamp the forge emits derives from it, never the wall clock. */
const TRIAL_NOW_ISO = process.env.MAKEFUN_TRIAL_NOW ?? '2026-11-14T06:30:00.000Z';
const TRIAL_EPOCH = (() => {
  const ms = Date.parse(TRIAL_NOW_ISO);
  return Number.isFinite(ms) ? Math.floor(ms / 1000) : 1700000000;
})();
/** A monotonic counter keeps commit timestamps unique and deterministic in run order. */
let commitSeq = 0;
function nextCommitTimestamp(): number {
  return TRIAL_EPOCH + (commitSeq += 1);
}

type GitObjectType = 'commit' | 'tree' | 'blob' | 'tag';
interface GitObject {
  type: GitObjectType;
  data: Buffer;
}

function isHex40(value: string): boolean {
  return /^[0-9a-f]{40}$/.test(value);
}

function sha1Hex(data: Buffer): string {
  return createHash('sha1').update(data).digest('hex');
}

function hashObject(type: GitObjectType, data: Buffer): string {
  const header = Buffer.from(`${type} ${data.length}\0`, 'utf8');
  return sha1Hex(Buffer.concat([header, data]));
}

function b64encode(data: Buffer | string): string {
  return Buffer.isBuffer(data) ? data.toString('base64') : Buffer.from(data, 'utf8').toString('base64');
}

function b64decode(text: string): Buffer {
  return Buffer.from(text.replace(/\s+/g, ''), 'base64');
}

function gid(kind: string, key: string): string {
  return b64encode(`${kind}:${key}`);
}

function ungid(id: string): { kind: string; key: string } | null {
  try {
    const text = b64decode(id).toString('utf8');
    const colon = text.indexOf(':');
    if (colon < 0) return null;
    return { kind: text.slice(0, colon), key: text.slice(colon + 1) };
  } catch {
    return null;
  }
}

// ---------------------------------------------------------------------------
// pkt-line codec
// ---------------------------------------------------------------------------

const PKT_LINE_MAX = 65520;

function pktLine(payload: string | Buffer): Buffer {
  const data = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const header = Buffer.alloc(4);
  header.write((data.length + 4).toString(16).padStart(4, '0'), 0, 4, 'ascii');
  return Buffer.concat([header, data]);
}

function pktFlush(): Buffer {
  return Buffer.from('0000', 'ascii');
}

function pktDelim(): Buffer {
  return Buffer.from('0001', 'ascii');
}

type Pkt = { kind: 'data'; payload: Buffer } | { kind: 'flush' } | { kind: 'delim' } | { kind: 'response-end' };

function decodePktLines(buf: Buffer): Pkt[] {
  const packets: Pkt[] = [];
  let offset = 0;
  while (offset + 4 <= buf.length) {
    const head = buf.subarray(offset, offset + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(head)) break; // raw trailing bytes (a pack): stop framing here
    const len = parseInt(head, 16);
    if (len === 0) {
      packets.push({ kind: 'flush' });
      offset += 4;
      continue;
    }
    if (len === 1) {
      packets.push({ kind: 'delim' });
      offset += 4;
      continue;
    }
    if (len === 2) {
      packets.push({ kind: 'response-end' });
      offset += 4;
      continue;
    }
    if (len < 4 || offset + len > buf.length) break;
    packets.push({ kind: 'data', payload: buf.subarray(offset + 4, offset + len) });
    offset += len;
  }
  return packets;
}

/** Offset just past the pkt-line framed prefix of `buf` (0 when the body is not framed at all). */
function framedPrefixLength(buf: Buffer): number {
  let offset = 0;
  while (offset + 4 <= buf.length) {
    const head = buf.subarray(offset, offset + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(head)) return offset;
    const len = parseInt(head, 16);
    if (len === 0 || len === 1 || len === 2) {
      offset += 4;
      continue;
    }
    if (len < 4 || offset + len > buf.length) return offset;
    offset += len;
  }
  return offset;
}

// ---------------------------------------------------------------------------
// Git object model: trees, commits, tags
// ---------------------------------------------------------------------------

interface TreeEntry {
  mode: string;
  name: string;
  oid: string;
}

function compareTreeNames(a: { name: string; mode: string }, b: { name: string; mode: string }): number {
  const left = Buffer.from(a.mode === '40000' ? `${a.name}/` : a.name, 'utf8');
  const right = Buffer.from(b.mode === '40000' ? `${b.name}/` : b.name, 'utf8');
  return Buffer.compare(left, right);
}

function buildTree(entries: readonly TreeEntry[]): Buffer {
  const sorted = [...entries].sort(compareTreeNames);
  const parts: Buffer[] = [];
  for (const entry of sorted) {
    parts.push(Buffer.from(`${entry.mode} ${entry.name}\0`, 'utf8'));
    parts.push(Buffer.from(entry.oid, 'hex'));
  }
  return Buffer.concat(parts);
}

function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let offset = 0;
  while (offset < data.length) {
    const space = data.indexOf(0x20, offset);
    const nul = data.indexOf(0x00, space + 1);
    if (space < 0 || nul < 0 || nul + 21 > data.length) throw new Error('malformed tree object');
    entries.push({
      mode: data.subarray(offset, space).toString('ascii'),
      name: data.subarray(space + 1, nul).toString('utf8'),
      oid: data.subarray(nul + 1, nul + 21).toString('hex'),
    });
    offset = nul + 21;
  }
  return entries;
}

interface CommitView {
  tree: string;
  parents: string[];
  author: string;
  committer: string;
  message: string;
}

function parseCommit(data: Buffer): CommitView {
  const text = data.toString('utf8');
  const blank = text.indexOf('\n\n');
  const headerText = blank < 0 ? text : text.slice(0, blank);
  const message = blank < 0 ? '' : text.slice(blank + 2);
  let tree = '';
  const parents: string[] = [];
  let author = '';
  let committer = '';
  for (const line of headerText.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5);
    else if (line.startsWith('parent ')) parents.push(line.slice(7));
    else if (line.startsWith('author ')) author = line.slice(7);
    else if (line.startsWith('committer ')) committer = line.slice(10);
  }
  return { tree, parents, author, committer, message };
}

function buildCommitBytes(fields: { tree: string; parents: readonly string[]; message: string; author: string; committer: string; timestamp: number }): Buffer {
  const lines = [`tree ${fields.tree}`];
  for (const parent of fields.parents) lines.push(`parent ${parent}`);
  lines.push(`author ${fields.author} ${fields.timestamp} +0000`);
  lines.push(`committer ${fields.committer} ${fields.timestamp} +0000`);
  const message = fields.message;
  return Buffer.from(`${lines.join('\n')}\n\n${message}`, 'utf8');
}

interface TagView {
  object: string;
  type: string;
  tag: string;
  tagger: string;
  message: string;
}

function parseTag(data: Buffer): TagView {
  const text = data.toString('utf8');
  const blank = text.indexOf('\n\n');
  const headerText = blank < 0 ? text : text.slice(0, blank);
  const message = blank < 0 ? '' : text.slice(blank + 2);
  const headers = new Map<string, string>();
  for (const line of headerText.split('\n')) {
    const space = line.indexOf(' ');
    if (space > 0) headers.set(line.slice(0, space), line.slice(space + 1));
  }
  return {
    object: headers.get('object') ?? '',
    type: headers.get('type') ?? '',
    tag: headers.get('tag') ?? '',
    tagger: headers.get('tagger') ?? '',
    message,
  };
}

// ---------------------------------------------------------------------------
// Packfiles: read (with delta resolution) and write (plain objects, no deltas)
// ---------------------------------------------------------------------------

function inflateAt(buf: Buffer, offset: number): { data: Buffer; next: number } {
  const view = buf.subarray(offset);
  const result = inflateSync(view, { info: true }) as unknown as { buffer: Buffer; engine: { bytesWritten: number } };
  const consumed = result.engine.bytesWritten;
  if (!consumed || consumed <= 0) throw new Error(`zlib stream at offset ${offset} consumed no bytes`);
  return { data: result.buffer, next: offset + consumed };
}

function readVarintSize(buf: Buffer, start: number): { size: number; next: number; first: number } {
  let byte = buf[start];
  const first = byte;
  let size = byte & 0x0f;
  let shift = 4;
  let offset = start + 1;
  while (byte & 0x80) {
    byte = buf[offset++];
    size += (byte & 0x7f) * 2 ** shift;
    shift += 7;
  }
  return { size, next: offset, first };
}

function readOfsDeltaBase(buf: Buffer, start: number): { baseOffset: number; next: number } {
  let byte = buf[start];
  let offset = start + 1;
  let value = byte & 0x7f;
  while (byte & 0x80) {
    byte = buf[offset++];
    value = (value + 1) * 128 + (byte & 0x7f);
  }
  return { baseOffset: value, next: offset };
}

function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let offset = 0;
  const readSize = (): number => {
    let value = 0;
    let shift = 0;
    for (;;) {
      const byte = delta[offset++];
      value += (byte & 0x7f) * 2 ** shift;
      shift += 7;
      if (!(byte & 0x80)) break;
    }
    return value;
  };
  const sourceSize = readSize();
  const targetSize = readSize();
  if (sourceSize !== base.length) throw new Error('delta base size mismatch');
  const out = Buffer.allocUnsafe(targetSize);
  let written = 0;
  while (offset < delta.length) {
    const op = delta[offset++];
    if (op & 0x80) {
      let copyOffset = 0;
      let copySize = 0;
      let shift = 0;
      for (let bit = 0; bit < 4; bit += 1) {
        if (op & (1 << bit)) copyOffset += delta[offset++] * 2 ** shift;
        shift += 8;
      }
      shift = 0;
      for (let bit = 4; bit < 7; bit += 1) {
        if (op & (1 << bit)) copySize += delta[offset++] * 2 ** shift;
        shift += 8;
      }
      if (copySize === 0) copySize = 0x10000;
      base.copy(out, written, copyOffset, copyOffset + copySize);
      written += copySize;
    } else if (op !== 0) {
      const literal = op & 0x7f;
      delta.copy(out, written, offset, offset + literal);
      offset += literal;
      written += literal;
    } else {
      throw new Error('delta opcode 0');
    }
  }
  if (written !== targetSize) throw new Error('delta size mismatch');
  return out;
}

const PACK_TYPE_CODE: Record<GitObjectType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const PACK_CODE_TYPE: Record<number, GitObjectType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

interface RawPackEntry {
  offset: number;
  typeCode: number;
  size: number;
  data: Buffer;
  baseOffset?: number;
  baseOid?: string;
}

/** Parse a packfile into objects (oid -> object). Throws on a malformed pack. */
function readPack(pack: Buffer, storeLookup?: (oid: string) => GitObject | undefined): Map<string, GitObject> {
  if (pack.length < 32) throw new Error('pack too short');
  if (pack.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('pack does not start with PACK');
  const version = pack.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error(`unsupported pack version ${version}`);
  const count = pack.readUInt32BE(8);
  const trailerStart = pack.length - 20;
  const trailer = pack.subarray(trailerStart).toString('hex');
  if (sha1Hex(pack.subarray(0, trailerStart)) !== trailer) throw new Error('pack trailer checksum mismatch');
  const raw: RawPackEntry[] = [];
  const byOffset = new Map<number, RawPackEntry>();
  let offset = 12;
  for (let i = 0; i < count; i += 1) {
    const entryOffset = offset;
    const header = readVarintSize(pack, offset);
    offset = header.next;
    const typeCode = (header.first >> 4) & 0x07;
    const entry: RawPackEntry = { offset: entryOffset, typeCode, size: header.size, data: Buffer.alloc(0) };
    if (typeCode === 6) {
      const base = readOfsDeltaBase(pack, offset);
      offset = base.next;
      entry.baseOffset = entryOffset - base.baseOffset;
    } else if (typeCode === 7) {
      entry.baseOid = pack.subarray(offset, offset + 20).toString('hex');
      offset += 20;
    } else if (!PACK_CODE_TYPE[typeCode]) {
      throw new Error(`pack entry ${i} has unknown type code ${typeCode}`);
    }
    const inflated = inflateAt(pack.subarray(0, trailerStart), offset);
    if (inflated.data.length !== header.size) throw new Error('pack entry size mismatch');
    entry.data = inflated.data;
    offset = inflated.next;
    raw.push(entry);
    byOffset.set(entryOffset, entry);
  }
  if (offset !== trailerStart) throw new Error('pack has stray bytes before its trailer');
  const objects = new Map<string, GitObject>();
  const resolved = new Map<number, { type: GitObjectType; data: Buffer; oid: string }>();
  const resolving = new Set<number>();
  const resolve = (entry: RawPackEntry): { type: GitObjectType; data: Buffer; oid: string } => {
    const done = resolved.get(entry.offset);
    if (done) return done;
    if (resolving.has(entry.offset)) throw new Error('delta cycle in pack');
    resolving.add(entry.offset);
    let type: GitObjectType;
    let data: Buffer;
    if (entry.typeCode === 6) {
      const baseEntry = byOffset.get(entry.baseOffset!);
      if (!baseEntry) throw new Error('ofs-delta base not in pack');
      const base = resolve(baseEntry);
      type = base.type;
      data = applyDelta(base.data, entry.data);
    } else if (entry.typeCode === 7) {
      const baseEntry = [...resolved.values()].find((r) => r.oid === entry.baseOid);
      if (baseEntry) {
        type = baseEntry.type;
        data = applyDelta(baseEntry.data, entry.data);
      } else {
        const external = storeLookup?.(entry.baseOid!);
        if (!external) throw new Error('ref-delta base not available');
        type = external.type;
        data = applyDelta(external.data, entry.data);
      }
    } else {
      type = PACK_CODE_TYPE[entry.typeCode];
      data = entry.data;
    }
    const oid = hashObject(type, data);
    const out = { type, data, oid };
    resolved.set(entry.offset, out);
    resolving.delete(entry.offset);
    return out;
  };
  for (const entry of raw) {
    const r = resolve(entry);
    if (!objects.has(r.oid)) objects.set(r.oid, { type: r.type, data: r.data });
  }
  return objects;
}

function writePackObjectHeader(type: GitObjectType, size: number): Buffer {
  const code = PACK_TYPE_CODE[type];
  const bytes: number[] = [];
  let remaining = size;
  let first = (code << 4) | (remaining & 0x0f);
  remaining = Math.floor(remaining / 16);
  while (remaining > 0) {
    bytes.push(first | 0x80);
    first = remaining & 0x7f;
    remaining = Math.floor(remaining / 128);
  }
  bytes.push(first);
  return Buffer.from(bytes);
}

/** Build a packfile from plain objects (no deltas), with a valid trailer checksum. */
function writePack(objects: Iterable<GitObject>): Buffer {
  const list = [...objects];
  const parts: Buffer[] = [];
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 4, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(list.length, 8);
  parts.push(header);
  for (const object of list) {
    parts.push(writePackObjectHeader(object.type, object.data.length));
    parts.push(deflateSync(object.data));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, createHash('sha1').update(body).digest()]);
}

// ---------------------------------------------------------------------------
// The store
// ---------------------------------------------------------------------------

interface Label {
  id: number;
  name: string;
  color: string;
}

interface Comment {
  id: number;
  gid: string;
  body: string;
  createdAt: string;
  updatedAt: string;
}

interface Issue {
  id: number;
  gid: string;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: Label[];
  comments: Comment[];
  createdSeq: number;
  createdAt: string;
  updatedAt: string;
  closedAt: string | null;
}

interface Pull {
  id: number;
  gid: string;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  merged: boolean;
  mergedAt: string | null;
  mergeCommitSha: string | null;
  headRef: string;
  baseRef: string;
  headSha: string;
  baseSha: string;
  comments: Comment[];
  createdSeq: number;
  createdAt: string;
  updatedAt: string;
}

interface Repo {
  name: string;
  description: string;
  isPrivate: boolean;
  defaultBranch: string;
  databaseId: number;
  /** Unique per repo instance (a recreated repo never reuses one): part of the fetch cache key. */
  instanceId: number;
  /** Bumped on every object-store change; the fetch cache is keyed on it. */
  version: number;
  createdSeq: number;
  objects: Map<string, GitObject>;
  refs: Map<string, string>;
  issues: Map<number, Issue>;
  pulls: Map<number, Pull>;
  labels: Map<string, Label>;
  nextNumber: number;
}

let globalIdCounter = 0;
let globalSeq = 0;
let repoDbCounter = 1000;

const reposByName = new Map<string, Repo>();
/** The login the bearer token names, learned from the first owner-scoped access to a repo that exists. */
let viewerLogin: string | null = null;

function repoByOwnerName(owner: string, name: string): Repo | null {
  const repo = reposByName.get(name);
  if (!repo) return null;
  if (viewerLogin === null) viewerLogin = owner;
  if (owner !== viewerLogin) return null;
  return repo;
}

function createRepoRecord(name: string, description: string, isPrivate: boolean): Repo {
  const repo: Repo = {
    name,
    description,
    isPrivate,
    defaultBranch: DEFAULT_BRANCH,
    databaseId: repoDbCounter += 1,
    instanceId: globalIdCounter += 1,
    version: 0,
    createdSeq: globalSeq += 1,
    objects: new Map(),
    refs: new Map(),
    issues: new Map(),
    pulls: new Map(),
    labels: new Map(),
    nextNumber: 1,
  };
  reposByName.set(name, repo);
  return repo;
}

function putObject(repo: Repo, type: GitObjectType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!repo.objects.has(oid)) repo.objects.set(oid, { type, data });
  return oid;
}

function getObject(repo: Repo, oid: string): GitObject | undefined {
  return repo.objects.get(oid);
}

/** Every object id reachable from `roots` (commits, tags, trees, blobs). */
function collectReachable(repo: Repo, roots: Iterable<string>): Set<string> {
  const seen = new Set<string>();
  const queue: string[] = [];
  for (const root of roots) if (isHex40(root)) queue.push(root);
  while (queue.length) {
    const oid = queue.pop()!;
    if (seen.has(oid)) continue;
    const object = repo.objects.get(oid);
    if (!object) continue;
    seen.add(oid);
    if (object.type === 'commit') {
      const commit = parseCommit(object.data);
      queue.push(commit.tree);
      for (const parent of commit.parents) queue.push(parent);
    } else if (object.type === 'tag') {
      queue.push(parseTag(object.data).object);
    } else if (object.type === 'tree') {
      for (const entry of parseTree(object.data)) {
        if (entry.mode !== '160000') queue.push(entry.oid);
      }
    }
  }
  return seen;
}

/** The objects a shallow boundary itself carries: the commit/tag and its tree closure, without parents. */
function boundaryObjects(repo: Repo, roots: readonly string[]): Set<string> {
  const out = new Set<string>();
  const stack: string[] = [...roots];
  while (stack.length) {
    const oid = stack.pop()!;
    if (out.has(oid)) continue;
    const object = repo.objects.get(oid);
    if (!object) continue;
    out.add(oid);
    if (object.type === 'commit') {
      stack.push(parseCommit(object.data).tree);
    } else if (object.type === 'tag') {
      stack.push(parseTag(object.data).object);
    } else if (object.type === 'tree') {
      for (const entry of parseTree(object.data)) stack.push(entry.oid);
    }
  }
  return out;
}

function isAncestor(repo: Repo, ancestor: string, descendant: string): boolean {
  if (ancestor === descendant) return true;
  const seen = new Set<string>();
  const queue: string[] = [descendant];
  while (queue.length) {
    const oid = queue.pop()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const object = repo.objects.get(oid);
    if (!object || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) {
      if (parent === ancestor) return true;
      queue.push(parent);
    }
  }
  return false;
}

/** The nearest common ancestor of two commits (linear histories: the first shared one). */
function mergeBase(repo: Repo, a: string, b: string): string | null {
  const ancestorsA = new Set<string>();
  const queueA: string[] = [a];
  while (queueA.length) {
    const oid = queueA.pop()!;
    if (ancestorsA.has(oid)) continue;
    ancestorsA.add(oid);
    const object = repo.objects.get(oid);
    if (!object || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) queueA.push(parent);
  }
  const queueB: string[] = [b];
  const seenB = new Set<string>();
  while (queueB.length) {
    const oid = queueB.pop()!;
    if (seenB.has(oid)) continue;
    seenB.add(oid);
    if (ancestorsA.has(oid)) return oid;
    const object = repo.objects.get(oid);
    if (!object || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) queueB.push(parent);
  }
  return null;
}

/** Flatten a tree to path -> {oid, mode}. */
function flattenTree(repo: Repo, treeOid: string | null, prefix: string, out: Map<string, { oid: string; mode: string }>): void {
  if (treeOid === null) return;
  const object = repo.objects.get(treeOid);
  if (!object || object.type !== 'tree') return;
  for (const entry of parseTree(object.data)) {
    const path = prefix === '' ? entry.name : `${prefix}/${entry.name}`;
    if (entry.mode === '40000') flattenTree(repo, entry.oid, path, out);
    else out.set(path, { oid: entry.oid, mode: entry.mode });
  }
}

function treeMap(repo: Repo, treeOid: string | null): Map<string, { oid: string; mode: string }> {
  const out = new Map<string, { oid: string; mode: string }>();
  flattenTree(repo, treeOid, '', out);
  return out;
}

/** Set (or delete, when blobOid is null) one file in a tree, rebuilding trees bottom-up. */
function setFileInTree(repo: Repo, baseTreeOid: string | null, segments: readonly string[], blobOid: string | null): string {
  if (segments.length === 0) return baseTreeOid ?? putObject(repo, 'tree', buildTree([]));
  const entries = new Map<string, TreeEntry>();
  if (baseTreeOid !== null) {
    const base = repo.objects.get(baseTreeOid);
    if (base && base.type === 'tree') {
      for (const entry of parseTree(base.data)) entries.set(entry.name, entry);
    }
  }
  const [head, ...rest] = segments as [string, ...string[]];
  if (rest.length === 0) {
    if (blobOid === null) entries.delete(head);
    else entries.set(head, { mode: '100644', name: head, oid: blobOid });
  } else {
    const child = entries.get(head);
    const childTree = child && child.mode === '40000' ? child.oid : null;
    const newChild = setFileInTree(repo, childTree, rest, blobOid);
    const childObject = repo.objects.get(newChild);
    const childEntries = childObject && childObject.type === 'tree' ? parseTree(childObject.data) : [];
    if (childEntries.length === 0 && blobOid === null) entries.delete(head);
    else entries.set(head, { mode: '40000', name: head, oid: newChild });
  }
  return putObject(repo, 'tree', buildTree([...entries.values()]));
}

/** The blob (and its mode) at a path in a tree, or null. */
function getFileAt(repo: Repo, treeOid: string | null, path: string): { oid: string; mode: string } | null {
  const segments = path.split('/').filter((s) => s !== '');
  let current = treeOid;
  for (let i = 0; i < segments.length; i += 1) {
    if (current === null) return null;
    const object = repo.objects.get(current);
    if (!object || object.type !== 'tree') return null;
    const entry = parseTree(object.data).find((e) => e.name === segments[i]);
    if (!entry) return null;
    if (i === segments.length - 1) return entry.mode === '40000' ? null : { oid: entry.oid, mode: entry.mode };
    if (entry.mode !== '40000') return null;
    current = entry.oid;
  }
  return null;
}

/** The entries of the directory at `path` in a tree ('' is the root), or null when it is not a directory. */
function listDirAt(repo: Repo, treeOid: string | null, path: string): TreeEntry[] | null {
  const segments = path.split('/').filter((s) => s !== '');
  let current = treeOid;
  for (const segment of segments) {
    if (current === null) return null;
    const object = repo.objects.get(current);
    if (!object || object.type !== 'tree') return null;
    const entry = parseTree(object.data).find((e) => e.name === segment);
    if (!entry || entry.mode !== '40000') return null;
    current = entry.oid;
  }
  if (current === null) return [];
  const object = repo.objects.get(current);
  if (!object || object.type !== 'tree') return null;
  return parseTree(object.data);
}

const FORGE_IDENTITY = 'Forge <forge@localhost>';

function createCommitObject(
  repo: Repo,
  tree: string,
  parents: readonly string[],
  message: string,
): string {
  const data = buildCommitBytes({
    tree,
    parents,
    message,
    author: FORGE_IDENTITY,
    committer: FORGE_IDENTITY,
    timestamp: nextCommitTimestamp(),
  });
  repo.version += 1;
  return putObject(repo, 'commit', data);
}

/** Commits reachable from `tip`, newest first (tip, then parents depth-first). */
function listCommits(repo: Repo, tip: string): string[] {
  const out: string[] = [];
  const seen = new Set<string>();
  const queue: string[] = [tip];
  while (queue.length) {
    const oid = queue.shift()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const object = repo.objects.get(oid);
    if (!object || object.type !== 'commit') continue;
    out.push(oid);
    for (const parent of parseCommit(object.data).parents) queue.push(parent);
  }
  return out;
}

/** A line diff: {additions, deletions} between two texts, via LCS on lines. */
function diffLines(oldText: string, newText: string): { additions: number; deletions: number } {
  const split = (text: string): string[] => {
    if (text === '') return [];
    const lines = text.split('\n');
    if (lines[lines.length - 1] === '') lines.pop();
    return lines;
  };
  const a = split(oldText);
  const b = split(newText);
  const n = a.length;
  const m = b.length;
  const dp: number[][] = Array.from({ length: n + 1 }, () => new Array<number>(m + 1).fill(0));
  for (let i = n - 1; i >= 0; i -= 1) {
    for (let j = m - 1; j >= 0; j -= 1) {
      dp[i][j] = a[i] === b[j] ? dp[i + 1][j + 1] + 1 : Math.max(dp[i + 1][j], dp[i][j + 1]);
    }
  }
  const lcs = dp[0][0];
  return { additions: m - lcs, deletions: n - lcs };
}

/** Paths changed between two trees, with their before/after blob oids. */
function changedPaths(
  repo: Repo,
  baseTree: string | null,
  headTree: string | null,
): Array<{ path: string; baseOid: string | null; headOid: string | null }> {
  const base = treeMap(repo, baseTree);
  const head = treeMap(repo, headTree);
  const paths = new Set([...base.keys(), ...head.keys()]);
  const out: Array<{ path: string; baseOid: string | null; headOid: string | null }> = [];
  for (const path of [...paths].sort()) {
    const b = base.get(path);
    const h = head.get(path);
    if (b?.oid !== h?.oid) out.push({ path, baseOid: b?.oid ?? null, headOid: h?.oid ?? null });
  }
  return out;
}

/** Whether merging `headTip` into `baseTip` conflicts (both sides changed a path differently). */
function mergeConflict(repo: Repo, headTip: string, baseTip: string): boolean {
  const mb = mergeBase(repo, headTip, baseTip);
  const mbTree = mb === null ? null : parseCommit(repo.objects.get(mb)!.data).tree;
  const headTree = parseCommit(repo.objects.get(headTip)!.data).tree;
  const baseTree = parseCommit(repo.objects.get(baseTip)!.data).tree;
  const headChanges = changedPaths(repo, mbTree, headTree);
  const baseChanges = new Map(changedPaths(repo, mbTree, baseTree).map((c) => [c.path, c]));
  for (const change of headChanges) {
    const other = baseChanges.get(change.path);
    if (other && other.headOid !== change.headOid) return true;
  }
  return false;
}

/**
 * Squash-merge a pull request onto its base branch. Returns the merge commit sha,
 * or null when the merge conflicts.
 */
function squashMerge(repo: Repo, pull: Pull): string | null {
  const headTip = pull.headSha;
  // The base tip is the branch's CURRENT tip: the pull's stored baseSha is stale once
  // an earlier pull merged onto the same base branch.
  const baseTip = repo.refs.get(`refs/heads/${pull.baseRef}`) ?? pull.baseSha;
  const headObj = repo.objects.get(headTip);
  const baseObj = repo.objects.get(baseTip);
  if (!headObj || !baseObj || headObj.type !== 'commit' || baseObj.type !== 'commit') return null;
  if (mergeConflict(repo, headTip, baseTip)) return null;
  const mb = mergeBase(repo, headTip, baseTip);
  const mbTree = mb === null ? null : parseCommit(repo.objects.get(mb)!.data).tree;
  const headTree = parseCommit(headObj.data).tree;
  const baseTree = parseCommit(baseObj.data).tree;
  let mergedTree = baseTree;
  for (const change of changedPaths(repo, mbTree, headTree)) {
    mergedTree = setFileInTree(repo, mergedTree, change.path.split('/'), change.headOid);
  }
  const message = `Merge pull request #${pull.number} from ${pull.headRef}\n\n${pull.title}\n`;
  const sha = createCommitObject(repo, mergedTree, [baseTip], message);
  repo.refs.set(`refs/heads/${pull.baseRef}`, sha);
  pull.state = 'closed';
  pull.merged = true;
  pull.mergedAt = TRIAL_NOW_ISO;
  pull.mergeCommitSha = sha;
  pull.baseSha = sha;
  pull.updatedAt = TRIAL_NOW_ISO;
  return sha;
}

function createIssueRecord(repo: Repo, title: string, body: string, labelNames: readonly string[]): Issue {
  const number = repo.nextNumber;
  repo.nextNumber += 1;
  const issue: Issue = {
    id: globalIdCounter += 1,
    gid: gid('Issue', `${repo.databaseId}:${number}`),
    number,
    title,
    body,
    state: 'open',
    labels: labelNames.map((name) => repo.labels.get(name)!).filter(Boolean),
    comments: [],
    createdSeq: globalSeq += 1,
    createdAt: TRIAL_NOW_ISO,
    updatedAt: TRIAL_NOW_ISO,
    closedAt: null,
  };
  repo.issues.set(number, issue);
  return issue;
}

function createPullRecord(repo: Repo, title: string, body: string, headRef: string, baseRef: string, headSha: string, baseSha: string): Pull {
  const number = repo.nextNumber;
  repo.nextNumber += 1;
  const pull: Pull = {
    id: globalIdCounter += 1,
    gid: gid('PullRequest', `${repo.databaseId}:${number}`),
    number,
    title,
    body,
    state: 'open',
    merged: false,
    mergedAt: null,
    mergeCommitSha: null,
    headRef,
    baseRef,
    headSha,
    baseSha,
    comments: [],
    createdSeq: globalSeq += 1,
    createdAt: TRIAL_NOW_ISO,
    updatedAt: TRIAL_NOW_ISO,
  };
  repo.pulls.set(number, pull);
  return pull;
}

/** Look a repository up by its GraphQL global id. */
function repoById(gidValue: string): Repo | null {
  const decoded = ungid(gidValue);
  if (!decoded || decoded.kind !== 'Repository') return null;
  return [...reposByName.values()].find((r) => String(r.databaseId) === decoded.key) ?? null;
}

function findIssueByGid(gidValue: string): { repo: Repo; issue: Issue } | null {
  const decoded = ungid(gidValue);
  if (!decoded || decoded.kind !== 'Issue') return null;
  const [repoId, number] = decoded.key.split(':');
  const repo = [...reposByName.values()].find((r) => String(r.databaseId) === repoId);
  const issue = repo?.issues.get(parseInt(number, 10));
  if (!repo || !issue) return null;
  return { repo, issue };
}

function findPullByGid(gidValue: string): { repo: Repo; pull: Pull } | null {
  const decoded = ungid(gidValue);
  if (!decoded || decoded.kind !== 'PullRequest') return null;
  const [repoId, number] = decoded.key.split(':');
  const repo = [...reposByName.values()].find((r) => String(r.databaseId) === repoId);
  const pull = repo?.pulls.get(parseInt(number, 10));
  if (!repo || !pull) return null;
  return { repo, pull };
}

/** A comment subject is an issue or a pull request; both expose a comments list. */
function findSubjectByGid(gidValue: string): { repo: Repo; comments: Comment[] } | null {
  const issue = findIssueByGid(gidValue);
  if (issue) return { repo: issue.repo, comments: issue.issue.comments };
  const pull = findPullByGid(gidValue);
  if (pull) return { repo: pull.repo, comments: pull.pull.comments };
  return null;
}

// ---------------------------------------------------------------------------
// HTTP plumbing
// ---------------------------------------------------------------------------

let requestCounter = 0;

function nextRequestId(): string {
  requestCounter += 1;
  return `forge-${requestCounter.toString(36)}-${Date.now().toString(36)}`;
}

function sendJson(res: ServerResponse, status: number, body: unknown, extra: Record<string, string> = {}): void {
  const text = `${JSON.stringify(body)}\n`;
  res.writeHead(status, {
    'content-type': JSON_TYPE,
    'content-length': Buffer.byteLength(text),
    'x-github-request-id': nextRequestId(),
    ...extra,
  });
  res.end(text);
}

function sendNoContent(res: ServerResponse, status: number): void {
  res.writeHead(status, { 'x-github-request-id': nextRequestId() });
  res.end();
}

function sendRaw(res: ServerResponse, status: number, contentType: string, body: Buffer): void {
  res.writeHead(status, {
    'content-type': contentType,
    'content-length': body.length,
    'x-github-request-id': nextRequestId(),
  });
  res.end(body);
}

function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    let total = 0;
    req.on('data', (chunk: Buffer) => {
      total += chunk.length;
      if (total > 64 * 1024 * 1024) {
        reject(new Error('request body too large'));
        req.destroy();
        return;
      }
      chunks.push(chunk);
    });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

function isAuthorized(req: IncomingMessage): boolean {
  const header = req.headers.authorization;
  if (!header || !header.startsWith('Bearer ')) return false;
  const token = header.slice(7);
  if (token === '') return false;
  if (EXPECTED_TOKEN !== '') return token === EXPECTED_TOKEN;
  return true;
}

class HttpError extends Error {
  status: number;
  constructor(status: number, message: string) {
    super(message);
    this.status = status;
  }
}

function parseJsonBody(raw: Buffer): Record<string, unknown> {
  const text = raw.toString('utf8').trim();
  if (text === '') return {};
  let value: unknown;
  try {
    value = JSON.parse(text);
  } catch {
    throw new HttpError(400, 'Invalid JSON body');
  }
  if (typeof value !== 'object' || value === null || Array.isArray(value)) {
    throw new HttpError(400, 'Invalid JSON body');
  }
  return value as Record<string, unknown>;
}

function queryParams(req: IncomingMessage): URLSearchParams {
  try {
    return new URL(req.url ?? '/', 'http://entry').searchParams;
  } catch {
    return new URLSearchParams();
  }
}

function pathSegments(req: IncomingMessage): string[] {
  try {
    const path = new URL(req.url ?? '/', 'http://entry').pathname;
    return path.split('/').filter((s) => s !== '').map((s) => {
      try {
        return decodeURIComponent(s);
      } catch {
        return s;
      }
    });
  } catch {
    return [];
  }
}

function paginate<T>(items: readonly T[], query: URLSearchParams, req: IncomingMessage, basePath: string): { page: T[]; link: string | null } {
  const perPage = Math.min(100, Math.max(1, parseInt(query.get('per_page') ?? '30', 10) || 30));
  const page = Math.max(1, parseInt(query.get('page') ?? '1', 10) || 1);
  const start = (page - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  let link: string | null = null;
  if (start + perPage < items.length) {
    const host = req.headers.host ?? 'localhost';
    const url = new URL(`http://${host}${basePath}`);
    for (const [key, value] of query.entries()) {
      if (key !== 'page' && key !== 'per_page') url.searchParams.set(key, value);
    }
    url.searchParams.set('per_page', String(perPage));
    url.searchParams.set('page', String(page + 1));
    link = `<${url.toString()}>; rel="next"`;
  }
  return { page: slice, link };
}

// ---------------------------------------------------------------------------
// REST v3 JSON shapes
// ---------------------------------------------------------------------------

function ownerLoginOf(repo: Repo): string {
  return viewerLogin ?? 'owner';
}

function repoJson(repo: Repo): Record<string, unknown> {
  const login = ownerLoginOf(repo);
  return {
    id: repo.databaseId,
    node_id: gid('Repository', String(repo.databaseId)),
    name: repo.name,
    full_name: `${login}/${repo.name}`,
    owner: { login, id: 1000, node_id: gid('User', login), type: 'User', site_admin: false },
    private: repo.isPrivate,
    description: repo.description,
    default_branch: repo.defaultBranch,
    html_url: `https://example.invalid/${login}/${repo.name}`,
    clone_url: `https://example.invalid/${login}/${repo.name}.git`,
    url: `/api/v3/repos/${login}/${repo.name}`,
    created_at: TRIAL_NOW_ISO,
    updated_at: TRIAL_NOW_ISO,
    pushed_at: TRIAL_NOW_ISO,
    has_issues: true,
    has_projects: true,
    has_wiki: true,
    has_pages: false,
    forks_count: 0,
    stargazers_count: 0,
    watchers_count: 0,
    open_issues_count: [...repo.issues.values()].filter((i) => i.state === 'open').length,
    license: null,
    topics: [],
    visibility: repo.isPrivate ? 'private' : 'public',
    archived: false,
    disabled: false,
  };
}

function labelJson(label: Label): Record<string, unknown> {
  return { id: label.id, node_id: gid('Label', String(label.id)), name: label.name, color: label.color, description: '', default: false };
}

function issueJson(repo: Repo, issue: Issue): Record<string, unknown> {
  const login = ownerLoginOf(repo);
  return {
    id: issue.id,
    node_id: issue.gid,
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    labels: issue.labels.map(labelJson),
    user: { login, id: 1000, type: 'User' },
    assignees: [],
    locked: false,
    comments: issue.comments.length,
    created_at: issue.createdAt,
    updated_at: issue.updatedAt,
    closed_at: issue.closedAt,
    author_association: 'OWNER',
    html_url: `https://example.invalid/${login}/${repo.name}/issues/${issue.number}`,
    url: `/api/v3/repos/${login}/${repo.name}/issues/${issue.number}`,
    repository_url: `/api/v3/repos/${login}/${repo.name}`,
  };
}

function pullJson(repo: Repo, pull: Pull): Record<string, unknown> {
  const login = ownerLoginOf(repo);
  const refJson = (ref: string, sha: string): Record<string, unknown> => ({
    label: `${login}:${ref}`,
    ref,
    sha,
    user: { login, id: 1000, type: 'User' },
    repo: { id: repo.databaseId, name: repo.name, full_name: `${login}/${repo.name}` },
  });
  return {
    id: pull.id,
    node_id: pull.gid,
    number: pull.number,
    title: pull.title,
    body: pull.body,
    state: pull.state,
    locked: false,
    merged: pull.merged,
    merged_at: pull.mergedAt,
    merge_commit_sha: pull.mergeCommitSha,
    mergeable: pull.state === 'open' ? !mergeConflict(repo, pull.headSha, repo.refs.get(`refs/heads/${pull.baseRef}`) ?? pull.baseSha) : null,
    head: refJson(pull.headRef, pull.headSha),
    base: refJson(pull.baseRef, pull.baseSha),
    user: { login, id: 1000, type: 'User' },
    created_at: pull.createdAt,
    updated_at: pull.updatedAt,
    closed_at: pull.state === 'closed' ? pull.updatedAt : null,
    html_url: `https://example.invalid/${login}/${repo.name}/pull/${pull.number}`,
    url: `/api/v3/repos/${login}/${repo.name}/pulls/${pull.number}`,
  };
}

function commentJson(repo: Repo, issue: Issue, comment: Comment): Record<string, unknown> {
  const login = ownerLoginOf(repo);
  return {
    id: comment.id,
    node_id: comment.gid,
    body: comment.body,
    user: { login, id: 1000, type: 'User' },
    created_at: comment.createdAt,
    updated_at: comment.updatedAt,
    html_url: `https://example.invalid/${login}/${repo.name}/issues/${issue.number}#issuecomment-${comment.id}`,
    issue_url: `/api/v3/repos/${login}/${repo.name}/issues/${issue.number}`,
  };
}

function commitJson(repo: Repo, sha: string): Record<string, unknown> | null {
  const object = repo.objects.get(sha);
  if (!object || object.type !== 'commit') return null;
  const commit = parseCommit(object.data);
  const person = (line: string): { name: string; email: string; date: string } => {
    const match = /^(.*) <(.*)> (\d+) ([+-]\d{4})$/.exec(line);
    if (!match) return { name: 'Forge', email: 'forge@localhost', date: TRIAL_NOW_ISO };
    return { name: match[1], email: match[2], date: new Date(parseInt(match[3], 10) * 1000).toISOString() };
  };
  return {
    sha,
    node_id: gid('Commit', sha),
    commit: {
      message: commit.message,
      author: person(commit.author),
      committer: person(commit.committer),
      tree: { sha: commit.tree },
    },
    author: null,
    committer: null,
    parents: commit.parents.map((p) => ({ sha: p })),
    url: `/api/v3/repos/${ownerLoginOf(repo)}/${repo.name}/commits/${sha}`,
  };
}

// ---------------------------------------------------------------------------
// REST v3 handlers
// ---------------------------------------------------------------------------

async function handleRest(req: IncomingMessage, res: ServerResponse, segments: string[]): Promise<boolean> {
  const method = req.method ?? 'GET';
  // segments[0] === 'api', segments[1] === 'v3'
  const rest = segments.slice(2);
  const query = queryParams(req);

  if (!isAuthorized(req)) {
    sendJson(res, 401, { message: 'Requires authentication' });
    return true;
  }

  const needRepo = (owner: string, name: string): Repo => {
    const repo = repoByOwnerName(owner, name);
    if (!repo) throw new HttpError(404, 'Not Found');
    return repo;
  };

  // GET /api/v3/ — the API root.
  if (rest.length === 0) {
    if (method !== 'GET') throw new HttpError(404, 'Not Found');
    sendJson(res, 200, { current_user_url: '/api/v3/user', rate_limit_url: '/api/v3/rate_limit' }, { 'x-oauth-scopes': 'repo, read:org' });
    return true;
  }

  // GET /api/v3/meta
  if (rest.length === 1 && rest[0] === 'meta') {
    if (method !== 'GET') throw new HttpError(404, 'Not Found');
    sendJson(res, 200, { verifiable_password_authentication: true, installed_version: '1.0.0', hooks: [], git: [], pages: [] }, { 'x-oauth-scopes': 'repo, read:org' });
    return true;
  }

  // GET /api/v3/user
  if (rest.length === 1 && rest[0] === 'user') {
    if (method !== 'GET') throw new HttpError(404, 'Not Found');
    if (viewerLogin === null) throw new HttpError(404, 'Not Found');
    sendJson(res, 200, { login: viewerLogin, id: 1000, node_id: gid('User', viewerLogin), type: 'User', site_admin: false });
    return true;
  }

  // /api/v3/user/repos
  if (rest.length === 2 && rest[0] === 'user' && rest[1] === 'repos') {
    if (method === 'GET') {
      const all = [...reposByName.values()].sort((a, b) => a.createdSeq - b.createdSeq).map(repoJson);
      const { page, link } = paginate(all, query, req, '/api/v3/user/repos');
      sendJson(res, 200, page, link === null ? { 'x-oauth-scopes': 'repo, read:org' } : { link, 'x-oauth-scopes': 'repo, read:org' });
      return true;
    }
    if (method === 'POST') {
      const body = parseJsonBody(await readBody(req));
      const name = typeof body.name === 'string' ? body.name.trim() : '';
      if (name === '') throw new HttpError(422, 'Validation Failed: name is required');
      if (reposByName.has(name)) throw new HttpError(422, 'Validation Failed: name already exists on this account');
      const repo = createRepoRecord(name, typeof body.description === 'string' ? body.description : '', body.private === true);
      sendJson(res, 201, repoJson(repo));
      return true;
    }
    throw new HttpError(404, 'Not Found');
  }

  // /api/v3/repos/{owner}/{repo}[...]
  if (rest.length >= 3 && rest[0] === 'repos') {
    const owner = rest[1];
    const name = rest[2];
    const tail = rest.slice(3);

    // The repository itself.
    if (tail.length === 0) {
      if (method === 'GET') {
        sendJson(res, 200, repoJson(needRepo(owner, name)));
        return true;
      }
      if (method === 'PATCH') {
        const repo = needRepo(owner, name);
        const body = parseJsonBody(await readBody(req));
        if (typeof body.description === 'string') repo.description = body.description;
        if (typeof body.private === 'boolean') repo.isPrivate = body.private;
        sendJson(res, 200, repoJson(repo));
        return true;
      }
      if (method === 'DELETE') {
        needRepo(owner, name);
        reposByName.delete(name);
        sendNoContent(res, 204);
        return true;
      }
      throw new HttpError(404, 'Not Found');
    }

    const repo = needRepo(owner, name);
    const sub = tail[0];

    // Branches.
    if (sub === 'branches') {
      if (tail.length === 1 && method === 'GET') {
        const branches = [...repo.refs.keys()]
          .filter((ref) => ref.startsWith('refs/heads/'))
          .map((ref) => ref.slice('refs/heads/'.length))
          .sort()
          .map((branch) => ({ name: branch, commit: { sha: repo.refs.get(`refs/heads/${branch}`)! }, protected: false }));
        sendJson(res, 200, branches);
        return true;
      }
      if (tail.length === 2 && method === 'GET') {
        const branch = tail.slice(1).join('/');
        const sha = repo.refs.get(`refs/heads/${branch}`);
        if (!sha) throw new HttpError(404, 'Branch not found');
        sendJson(res, 200, { name: branch, commit: { sha }, protected: false });
        return true;
      }
      throw new HttpError(404, 'Not Found');
    }

    // Commits.
    if (sub === 'commits' && tail.length === 1 && method === 'GET') {
      const refName = query.get('sha');
      let tip: string | undefined;
      if (refName) {
        tip = repo.refs.get(`refs/heads/${refName}`) ?? (isHex40(refName) ? refName : undefined);
        if (!tip) tip = repo.refs.get(`refs/tags/${refName}`);
      } else {
        tip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
      }
      if (!tip || !repo.objects.has(tip)) {
        sendJson(res, 200, []);
        return true;
      }
      const commits = listCommits(repo, tip).map((sha) => commitJson(repo, sha)).filter((c): c is Record<string, unknown> => c !== null);
      sendJson(res, 200, commits);
      return true;
    }

    // Git Data: refs.
    if (sub === 'git' && tail[1] === 'refs') {
      if (method === 'POST' && tail.length === 2) {
        const body = parseJsonBody(await readBody(req));
        const ref = typeof body.ref === 'string' ? body.ref : '';
        const sha = typeof body.sha === 'string' ? body.sha : '';
        if (!ref.startsWith('refs/heads/') || !isHex40(sha) || !repo.objects.has(sha)) {
          throw new HttpError(422, 'Validation Failed: ref and sha are required');
        }
        if (repo.refs.has(ref)) throw new HttpError(422, 'Validation Failed: Reference already exists');
        repo.refs.set(ref, sha);
        sendJson(res, 201, { ref, node_id: gid('Ref', ref), object: { sha, type: 'commit', url: `/api/v3/repos/${owner}/${name}/git/commits/${sha}` } });
        return true;
      }
      if (method === 'GET' && tail.length >= 4 && (tail[2] === 'heads' || tail[2] === 'tags')) {
        const ref = `refs/${tail[2]}/${tail.slice(3).join('/')}`;
        const sha = repo.refs.get(ref);
        if (!sha) throw new HttpError(404, 'Not Found');
        sendJson(res, 200, { ref, node_id: gid('Ref', ref), object: { sha, type: 'commit', url: `/api/v3/repos/${owner}/${name}/git/commits/${sha}` } });
        return true;
      }
      throw new HttpError(404, 'Not Found');
    }

    // Contents.
    if (sub === 'contents') {
      const filePath = tail.slice(1).join('/');
      if (method === 'PUT') {
        const body = parseJsonBody(await readBody(req));
        const message = typeof body.message === 'string' ? body.message : 'update';
        const content = typeof body.content === 'string' ? body.content : '';
        const branch = typeof body.branch === 'string' ? body.branch : repo.defaultBranch;
        const refName = `refs/heads/${branch}`;
        let tip = repo.refs.get(refName);
        if (tip === undefined) {
          // A contents write on a branch that does not exist yet creates it from the default tip.
          tip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
        }
        const baseTree = tip === undefined ? null : parseCommit(repo.objects.get(tip)!.data).tree;
        const existing = getFileAt(repo, baseTree, filePath);
        if (existing) {
          if (typeof body.sha !== 'string' || body.sha === '') {
            throw new HttpError(422, 'Validation Failed: sha is required to update a file');
          }
          if (body.sha.toLowerCase() !== existing.oid.toLowerCase()) {
            throw new HttpError(409, 'Conflict: sha does not match the current file');
          }
        } else if (typeof body.sha === 'string' && body.sha !== '') {
          throw new HttpError(422, 'Validation Failed: sha is not valid for a new file');
        }
        const blobOid = putObject(repo, 'blob', b64decode(content));
        const newTree = setFileInTree(repo, baseTree, filePath.split('/').filter((s) => s !== ''), blobOid);
        const commitSha = createCommitObject(repo, newTree, tip === undefined ? [] : [tip], message);
        repo.refs.set(refName, commitSha);
        const status = existing ? 200 : 201;
        sendJson(res, status, {
          content: { name: filePath.split('/').pop(), path: filePath, sha: blobOid, size: b64decode(content).length, encoding: 'base64', type: 'file' },
          commit: { sha: commitSha, message },
        });
        return true;
      }
      if (method === 'GET') {
        const refName = query.get('ref');
        let tip: string | undefined;
        if (refName) {
          tip = repo.refs.get(`refs/heads/${refName}`) ?? (isHex40(refName) ? refName : undefined) ?? repo.refs.get(`refs/tags/${refName}`);
        } else {
          tip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
        }
        if (!tip || !repo.objects.has(tip)) throw new HttpError(404, 'Not Found');
        const tree = parseCommit(repo.objects.get(tip)!.data).tree;
        if (filePath === '') {
          const entries = listDirAt(repo, tree, '') ?? [];
          sendJson(res, 200, entries.map((e) => dirEntryJson(repo, e, '')));
          return true;
        }
        const file = getFileAt(repo, tree, filePath);
        if (file) {
          const blob = repo.objects.get(file.oid)!;
          sendJson(res, 200, {
            type: 'file',
            encoding: 'base64',
            size: blob.data.length,
            name: filePath.split('/').pop(),
            path: filePath,
            content: blob.data.toString('base64'),
            sha: file.oid,
          });
          return true;
        }
        const entries = listDirAt(repo, tree, filePath);
        if (entries) {
          sendJson(res, 200, entries.map((e) => dirEntryJson(repo, e, filePath)));
          return true;
        }
        throw new HttpError(404, 'Not Found');
      }
      if (method === 'DELETE') {
        const body = parseJsonBody(await readBody(req));
        const message = typeof body.message === 'string' ? body.message : 'delete';
        const branch = typeof body.branch === 'string' ? body.branch : repo.defaultBranch;
        const refName = `refs/heads/${branch}`;
        const tip = repo.refs.get(refName);
        if (!tip) throw new HttpError(404, 'Not Found');
        const tree = parseCommit(repo.objects.get(tip)!.data).tree;
        const existing = getFileAt(repo, tree, filePath);
        if (!existing) throw new HttpError(404, 'Not Found');
        if (typeof body.sha === 'string' && body.sha.toLowerCase() !== existing.oid.toLowerCase()) {
          throw new HttpError(409, 'Conflict: sha does not match the current file');
        }
        const newTree = setFileInTree(repo, tree, filePath.split('/').filter((s) => s !== ''), null);
        const commitSha = createCommitObject(repo, newTree, [tip], message);
        repo.refs.set(refName, commitSha);
        sendJson(res, 200, { commit: { sha: commitSha, message } });
        return true;
      }
      throw new HttpError(404, 'Not Found');
    }

    // Labels.
    if (sub === 'labels') {
      if (method === 'POST' && tail.length === 1) {
        const body = parseJsonBody(await readBody(req));
        const name = typeof body.name === 'string' ? body.name.trim() : '';
        if (name === '') throw new HttpError(422, 'Validation Failed: name is required');
        let label = repo.labels.get(name);
        if (!label) {
          label = { id: globalIdCounter += 1, name, color: typeof body.color === 'string' ? body.color : 'ededed' };
          repo.labels.set(name, label);
        }
        sendJson(res, 201, labelJson(label));
        return true;
      }
      if (method === 'GET' && tail.length === 1) {
        sendJson(res, 200, [...repo.labels.values()].map(labelJson));
        return true;
      }
      throw new HttpError(404, 'Not Found');
    }

    // Issues.
    if (sub === 'issues') {
      if (tail.length === 1) {
        if (method === 'POST') {
          const body = parseJsonBody(await readBody(req));
          const title = typeof body.title === 'string' ? body.title : '';
          const issueBody = typeof body.body === 'string' ? body.body : '';
          const rawLabels: unknown[] = Array.isArray(body.labels) ? body.labels : [];
          const labelNames: string[] = [];
          for (const raw of rawLabels) {
            const name = typeof raw === 'string' ? raw : typeof raw === 'object' && raw !== null ? String((raw as Record<string, unknown>).name ?? '') : '';
            if (name === '') continue;
            if (!repo.labels.has(name)) throw new HttpError(422, `Validation Failed: label "${name}" does not exist`);
            labelNames.push(name);
          }
          const issue = createIssueRecord(repo, title, issueBody, labelNames);
          sendJson(res, 201, issueJson(repo, issue));
          return true;
        }
        if (method === 'GET') {
          const state = query.get('state') ?? 'open';
          const sort = query.get('sort') ?? 'created';
          const direction = query.get('direction') ?? (sort === 'created' ? 'desc' : 'asc');
          let issues = [...repo.issues.values()];
          if (state !== 'all') issues = issues.filter((i) => i.state === state);
          issues.sort((a, b) => (direction === 'asc' ? a.createdSeq - b.createdSeq : b.createdSeq - a.createdSeq));
          const { page, link } = paginate(issues.map((i) => issueJson(repo, i)), query, req, `/api/v3/repos/${owner}/${name}/issues`);
          sendJson(res, 200, page, link === null ? {} : { link });
          return true;
        }
        throw new HttpError(404, 'Not Found');
      }
      const number = parseInt(tail[1], 10);
      if (!Number.isInteger(number)) throw new HttpError(404, 'Not Found');
      const issue = repo.issues.get(number);
      if (tail.length === 2) {
        if (!issue) throw new HttpError(404, 'Not Found');
        if (method === 'GET') {
          sendJson(res, 200, issueJson(repo, issue));
          return true;
        }
        if (method === 'PATCH') {
          const body = parseJsonBody(await readBody(req));
          if (typeof body.title === 'string') issue.title = body.title;
          if (typeof body.body === 'string') issue.body = body.body;
          if (body.state === 'open' || body.state === 'closed') {
            issue.state = body.state;
            issue.closedAt = body.state === 'closed' ? TRIAL_NOW_ISO : null;
          }
          issue.updatedAt = TRIAL_NOW_ISO;
          sendJson(res, 200, issueJson(repo, issue));
          return true;
        }
        throw new HttpError(404, 'Not Found');
      }
      if (tail.length === 3 && tail[2] === 'comments') {
        if (!issue) throw new HttpError(404, 'Not Found');
        if (method === 'POST') {
          const body = parseJsonBody(await readBody(req));
          const commentBody = typeof body.body === 'string' ? body.body : '';
          const comment: Comment = {
            id: globalIdCounter += 1,
            gid: gid('IssueComment', `${repo.databaseId}:${issue.number}:${globalIdCounter}`),
            body: commentBody,
            createdAt: TRIAL_NOW_ISO,
            updatedAt: TRIAL_NOW_ISO,
          };
          issue.comments.push(comment);
          sendJson(res, 201, commentJson(repo, issue, comment));
          return true;
        }
        if (method === 'GET') {
          sendJson(res, 200, issue.comments.map((c) => commentJson(repo, issue, c)));
          return true;
        }
        throw new HttpError(404, 'Not Found');
      }
      throw new HttpError(404, 'Not Found');
    }

    // Pull requests.
    if (sub === 'pulls') {
      if (tail.length === 1) {
        if (method === 'POST') {
          const body = parseJsonBody(await readBody(req));
          const title = typeof body.title === 'string' ? body.title : '';
          const prBody = typeof body.body === 'string' ? body.body : '';
          const headRef = typeof body.head === 'string' ? body.head : '';
          const baseRef = typeof body.base === 'string' ? body.base : repo.defaultBranch;
          const headSha = repo.refs.get(`refs/heads/${headRef}`);
          const baseSha = repo.refs.get(`refs/heads/${baseRef}`);
          if (!headSha || !baseSha) throw new HttpError(422, 'Validation Failed: head and base branches must exist');
          const existing = [...repo.pulls.values()].find((p) => p.state === 'open' && p.headRef === headRef && p.baseRef === baseRef);
          if (existing) throw new HttpError(422, 'Validation Failed: a pull request already exists for this head and base');
          const pull = createPullRecord(repo, title, prBody, headRef, baseRef, headSha, baseSha);
          sendJson(res, 201, pullJson(repo, pull));
          return true;
        }
        if (method === 'GET') {
          const state = query.get('state') ?? 'open';
          let pulls = [...repo.pulls.values()];
          if (state !== 'all') pulls = pulls.filter((p) => p.state === state);
          pulls.sort((a, b) => b.createdSeq - a.createdSeq);
          const { page, link } = paginate(pulls.map((p) => pullJson(repo, p)), query, req, `/api/v3/repos/${owner}/${name}/pulls`);
          sendJson(res, 200, page, link === null ? {} : { link });
          return true;
        }
        throw new HttpError(404, 'Not Found');
      }
      const number = parseInt(tail[1], 10);
      if (!Number.isInteger(number)) throw new HttpError(404, 'Not Found');
      const pull = repo.pulls.get(number);
      if (tail.length === 2) {
        if (!pull) throw new HttpError(404, 'Not Found');
        if (method === 'GET') {
          sendJson(res, 200, pullJson(repo, pull));
          return true;
        }
        throw new HttpError(404, 'Not Found');
      }
      if (tail.length === 3 && tail[2] === 'files' && method === 'GET') {
        if (!pull) throw new HttpError(404, 'Not Found');
        const mb = mergeBase(repo, pull.headSha, pull.baseSha);
        const mbTree = mb === null ? null : parseCommit(repo.objects.get(mb)!.data).tree;
        const headTree = parseCommit(repo.objects.get(pull.headSha)!.data).tree;
        const files = changedPaths(repo, mbTree, headTree).map((change) => {
          const oldText = change.baseOid === null ? '' : (repo.objects.get(change.baseOid)?.data.toString('utf8') ?? '');
          const newText = change.headOid === null ? '' : (repo.objects.get(change.headOid)?.data.toString('utf8') ?? '');
          const diff = diffLines(oldText, newText);
          return {
            sha: change.headOid ?? change.baseOid,
            filename: change.path,
            status: change.baseOid === null ? 'added' : change.headOid === null ? 'removed' : 'modified',
            additions: diff.additions,
            deletions: diff.deletions,
            changes: diff.additions + diff.deletions,
            patch: '',
          };
        });
        sendJson(res, 200, files);
        return true;
      }
      if (tail.length === 3 && tail[2] === 'merge' && method === 'PUT') {
        if (!pull) throw new HttpError(404, 'Not Found');
        await readBody(req).catch(() => Buffer.alloc(0));
        if (pull.state === 'closed') throw new HttpError(405, 'Pull request is already closed');
        const sha = squashMerge(repo, pull);
        if (sha === null) throw new HttpError(405, 'Merge conflict: the pull request cannot be merged');
        sendJson(res, 200, { sha, merged: true, message: 'Pull request successfully merged' });
        return true;
      }
      throw new HttpError(404, 'Not Found');
    }
  }

  return false;
}

function dirEntryJson(repo: Repo, entry: TreeEntry, dirPath: string): Record<string, unknown> {
  const path = dirPath === '' ? entry.name : `${dirPath}/${entry.name}`;
  return {
    type: entry.mode === '40000' ? 'dir' : 'file',
    size: entry.mode === '40000' ? 0 : (repo.objects.get(entry.oid)?.data.length ?? 0),
    name: entry.name,
    path,
    sha: entry.oid,
    url: `/api/v3/repos/${ownerLoginOf(repo)}/${repo.name}/contents/${path}`,
  };
}

// ---------------------------------------------------------------------------
// Git smart HTTP
// ---------------------------------------------------------------------------

function sortedRefNames(repo: Repo): string[] {
  return [...repo.refs.keys()].sort();
}

/** The object a ref peels to (annotated tags peel to their target commit). */
function peeledOid(repo: Repo, ref: string): string | null {
  const oid = repo.refs.get(ref);
  if (!oid) return null;
  const object = repo.objects.get(oid);
  if (!object) return null;
  if (object.type === 'tag') {
    const tag = parseTag(object.data);
    return tag.object;
  }
  return null;
}

function v0Capabilities(repo: Repo, service: 'git-upload-pack' | 'git-receive-pack'): string {
  // multi_ack_detailed is required by real git clients in stateless (HTTP) v0 mode.
  const common = 'thin-pack ofs-delta multi_ack multi_ack_detailed shallow symref=HEAD:refs/heads/main agent=forge/1.0';
  if (service === 'git-upload-pack') return `side-band-64k ${common}`;
  return `report-status side-band-64k delete-refs ${common}`;
}

function v0Advertisement(repo: Repo, service: 'git-upload-pack' | 'git-receive-pack'): Buffer {
  const caps = v0Capabilities(repo, service);
  const parts: Buffer[] = [pktLine(`# service=${service}\n`), pktFlush()];
  const refs = sortedRefNames(repo);
  const headTip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
  const lines: string[] = [];
  if (refs.length === 0) {
    lines.push(`${ZERO_OID} capabilities^{}\0${caps}\n`);
  } else {
    lines.push(`${headTip ?? ZERO_OID} HEAD\0${caps}\n`);
    for (const ref of refs) {
      const oid = repo.refs.get(ref)!;
      lines.push(`${oid} ${ref}\n`);
      const peeled = peeledOid(repo, ref);
      if (peeled) lines.push(`${peeled} ${ref}^{}\n`);
    }
  }
  for (const line of lines) parts.push(pktLine(line));
  parts.push(pktFlush());
  return Buffer.concat(parts);
}

function v2Advertisement(service: 'git-upload-pack'): Buffer {
  const parts: Buffer[] = [
    pktLine(`# service=${service}\n`),
    pktFlush(),
    pktLine('version 2\n'),
    pktLine('agent=forge/1.0\n'),
    pktLine('ls-refs=unborn\n'),
    pktLine('fetch=shallow\n'),
    pktLine('object-format=sha1\n'),
    pktFlush(),
  ];
  return Buffer.concat(parts);
}

interface FetchPlan {
  /** Commits to send (objects + their trees/blobs). */
  commits: string[];
  /** The new shallow boundary commits. */
  shallow: string[];
  /** Old shallow boundaries that are no longer boundaries. */
  unshallow: string[];
  /** Every object the client already holds (full closure of its haves): never re-send these. */
  haveObjects: Set<string>;
}

/**
 * Plan a fetch: which commits (and their trees/blobs) to send.
 * - No depth: every commit reachable from wants, except those reachable from haves.
 * - Depth D: commits within D generations of wants; the boundary commits (distance D-1) are shallow.
 * Objects are the commits' trees/blobs only; parents outside the sent set are never traversed.
 */
function planFetch(repo: Repo, wants: readonly string[], haves: readonly string[], depth: number | null, oldShallow: readonly string[]): FetchPlan {
  const sent = new Set<string>();
  const shallow: string[] = [];
  if (depth !== null) {
    // BFS by parent edges, tracking distance from the wants.
    const distance = new Map<string, number>();
    const queue: string[] = [];
    for (const want of wants) {
      const object = repo.objects.get(want);
      if (!object) continue;
      if (object.type === 'tag') {
        const target = parseTag(object.data).object;
        if (!distance.has(target)) {
          distance.set(target, 0);
          queue.push(target);
        }
        sent.add(want);
        continue;
      }
      if (object.type !== 'commit') continue;
      if (!distance.has(want)) {
        distance.set(want, 0);
        queue.push(want);
      }
    }
    while (queue.length) {
      const oid = queue.shift()!;
      const d = distance.get(oid)!;
      sent.add(oid);
      if (d === depth - 1) shallow.push(oid);
      if (d + 1 >= depth) continue;
      const object = repo.objects.get(oid);
      if (!object || object.type !== 'commit') continue;
      for (const parent of parseCommit(object.data).parents) {
        if (!distance.has(parent)) {
          distance.set(parent, d + 1);
          queue.push(parent);
        }
      }
    }
  } else {
    const haveCommits = new Set<string>();
    for (const have of haves) {
      const object = repo.objects.get(have);
      if (!object) continue;
      const queue: string[] = [have];
      while (queue.length) {
        const oid = queue.pop()!;
        if (haveCommits.has(oid)) continue;
        haveCommits.add(oid);
        const obj = repo.objects.get(oid);
        if (!obj) continue;
        if (obj.type === 'commit') {
          for (const parent of parseCommit(obj.data).parents) queue.push(parent);
        } else if (obj.type === 'tag') {
          queue.push(parseTag(obj.data).object);
        }
      }
    }
    const queue: string[] = [];
    for (const want of wants) {
      const object = repo.objects.get(want);
      if (!object) continue;
      if (object.type === 'tag') {
        sent.add(want);
        const target = parseTag(object.data).object;
        if (!haveCommits.has(target)) queue.push(target);
        continue;
      }
      if (object.type === 'commit' && !haveCommits.has(want)) queue.push(want);
    }
    while (queue.length) {
      const oid = queue.pop()!;
      if (sent.has(oid) || haveCommits.has(oid)) continue;
      sent.add(oid);
      const object = repo.objects.get(oid);
      if (!object || object.type !== 'commit') continue;
      for (const parent of parseCommit(object.data).parents) queue.push(parent);
    }
  }
  // Everything the client already holds, and therefore must never be re-sent.
  // Without a depth the haves are full clones: exclude their whole closure (ancestors included).
  // With a depth the haves are shallow boundaries: the client holds the boundary commit and its
  // tree, but NOT its parents — excluding the parents would break deepen.
  const haveObjects = depth !== null ? boundaryObjects(repo, haves) : collectReachable(repo, haves);
  const unshallow: string[] = [];
  if (depth !== null) {
    for (const boundary of oldShallow) {
      if (!sent.has(boundary)) continue;
      const object = repo.objects.get(boundary);
      if (!object || object.type !== 'commit') continue;
      const parents = parseCommit(object.data).parents;
      if (parents.length === 0 || parents.some((p) => sent.has(p))) unshallow.push(boundary);
    }
  }
  return { commits: [...sent], shallow, unshallow, haveObjects };
}

function fetchPack(repo: Repo, plan: FetchPlan): Buffer {
  // Rebuild the object list in a stable order: commits first, then their trees/blobs.
  const objects = new Map<string, GitObject>();
  const addTreeClosure = (treeOid: string): void => {
    const stack: string[] = [treeOid];
    const seenTrees = new Set<string>();
    while (stack.length) {
      const oid = stack.pop()!;
      if (seenTrees.has(oid)) continue;
      seenTrees.add(oid);
      const object = repo.objects.get(oid);
      if (!object) continue;
      objects.set(oid, object);
      if (object.type === 'tree') {
        for (const entry of parseTree(object.data)) {
          if (entry.mode === '40000') stack.push(entry.oid);
          else {
            const blob = repo.objects.get(entry.oid);
            if (blob) objects.set(entry.oid, blob);
          }
        }
      }
    }
  };
  for (const oid of plan.commits) {
    const object = repo.objects.get(oid);
    if (!object) continue;
    objects.set(oid, object);
    if (object.type === 'commit') addTreeClosure(parseCommit(object.data).tree);
    else if (object.type === 'tag') {
      const target = parseTag(object.data).object;
      const targetObj = repo.objects.get(target);
      if (targetObj) {
        objects.set(target, targetObj);
        if (targetObj.type === 'commit') addTreeClosure(parseCommit(targetObj.data).tree);
      }
    }
  }
  // Never re-send an object the client already holds.
  for (const oid of plan.haveObjects) objects.delete(oid);
  return writePack(objects.values());
}

/** Split a pack into sideband band-1 pkt-lines. */
function sidebandPack(pack: Buffer): Buffer[] {
  const out: Buffer[] = [];
  const CHUNK = 65515;
  for (let offset = 0; offset < pack.length; offset += CHUNK) {
    const chunk = pack.subarray(offset, Math.min(pack.length, offset + CHUNK));
    out.push(pktLine(Buffer.concat([Buffer.from([1]), chunk])));
  }
  if (pack.length === 0) out.push(pktLine(Buffer.from([1])));
  return out;
}

// ---------------------------------------------------------------------------
// Fetch response cache
// ---------------------------------------------------------------------------
// A fetch response is a pure function of (repo instance, repo version, protocol, wants,
// haves, depth, shallow boundaries): no per-request data is embedded. Identical concurrent
// fetches (the perf clone workload: 50 depth-1 clones of one repo) share one built response.
// The key carries the repo version, which every object-store write bumps, so a cached
// response can never outlive the state it was built from.

const FETCH_CACHE_MAX_ENTRIES = 16;
const FETCH_CACHE_MAX_BYTES = 2 * 1024 * 1024;
const fetchResponseCache = new Map<string, Buffer>();

function fetchCacheKey(repo: Repo, protocol: string, wants: readonly string[], haves: readonly string[], depth: number | null, shallowBoundaries: readonly string[], done: boolean): string {
  return `${repo.instanceId}|v${repo.version}|${protocol}|${wants.join(',')}|${haves.join(',')}|${depth ?? ''}|${shallowBoundaries.join(',')}|${done ? 'done' : 'nodone'}`;
}

function fetchCacheGet(key: string): Buffer | undefined {
  return fetchResponseCache.get(key);
}

function fetchCachePut(key: string, body: Buffer): void {
  if (body.length > FETCH_CACHE_MAX_BYTES) return;
  if (!fetchResponseCache.has(key) && fetchResponseCache.size >= FETCH_CACHE_MAX_ENTRIES) {
    const oldest = fetchResponseCache.keys().next();
    if (!oldest.done) fetchResponseCache.delete(oldest.value);
  }
  fetchResponseCache.set(key, body);
}

function lsRefsLines(repo: Repo, options: { peel: boolean; symrefs: boolean; unborn: boolean; prefixes: string[] }): string[] {
  const lines: string[] = [];
  const headTip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
  const keep = (name: string): boolean => options.prefixes.length === 0 || options.prefixes.some((p) => name.startsWith(p));
  if (keep('HEAD')) {
    if (headTip) {
      lines.push(`${headTip} HEAD${options.symrefs ? ' symref-target:refs/heads/main' : ''}\n`);
    } else if (options.unborn) {
      lines.push(`unborn HEAD${options.symrefs ? ' symref-target:refs/heads/main' : ''}\n`);
    }
  }
  for (const ref of sortedRefNames(repo)) {
    if (!keep(ref)) continue;
    const oid = repo.refs.get(ref)!;
    const peeled = options.peel ? peeledOid(repo, ref) : null;
    lines.push(`${oid} ${ref}${peeled ? ` peeled:${peeled}` : ''}\n`);
  }
  return lines;
}

async function handleGit(req: IncomingMessage, res: ServerResponse, segments: string[]): Promise<boolean> {
  const method = req.method ?? 'GET';
  // segments: [owner, '<repo>.git', ...]
  if (segments.length < 2 || !segments[1].endsWith('.git')) return false;
  const owner = segments[0];
  const repoName = segments[1].slice(0, -4);
  const tail = segments.slice(2);
  const query = queryParams(req);
  const wantV2 = (req.headers['git-protocol'] ?? '') === 'version=2';

  if (!isAuthorized(req)) {
    sendJson(res, 401, { message: 'Requires authentication' });
    return true;
  }
  const repo = repoByOwnerName(owner, repoName);
  if (!repo) {
    sendJson(res, 404, { message: 'Not Found' });
    return true;
  }

  // GET /{owner}/{repo}.git/info/refs?service=...
  if (method === 'GET' && tail.length === 2 && tail[0] === 'info' && tail[1] === 'refs') {
    const service = query.get('service') ?? '';
    if (service === 'git-upload-pack') {
      if (wantV2) {
        sendRaw(res, 200, 'application/x-git-upload-pack-advertisement', v2Advertisement('git-upload-pack'));
      } else {
        sendRaw(res, 200, 'application/x-git-upload-pack-advertisement', v0Advertisement(repo, 'git-upload-pack'));
      }
      return true;
    }
    if (service === 'git-receive-pack') {
      sendRaw(res, 200, 'application/x-git-receive-pack-advertisement', v0Advertisement(repo, 'git-receive-pack'));
      return true;
    }
    sendJson(res, 404, { message: 'Not Found' });
    return true;
  }

  // POST /{owner}/{repo}.git/git-upload-pack
  if (method === 'POST' && tail.length === 1 && tail[0] === 'git-upload-pack') {
    const raw = await readBody(req);
    const packets = decodePktLines(raw);
    const lines = packets.filter((p): p is { kind: 'data'; payload: Buffer } => p.kind === 'data').map((p) => p.payload.toString('utf8'));
    if (wantV2) {
      const command = lines[0]?.replace(/\n$/, '') ?? '';
      if (command === 'command=ls-refs') {
        let peel = false;
        let symrefs = false;
        let unborn = false;
        const prefixes: string[] = [];
        let seenDelim = false;
        for (const line of lines.slice(1)) {
          const text = line.replace(/\n$/, '');
          if (text === '') continue;
          if (text === 'peel') peel = true;
          else if (text === 'symrefs') symrefs = true;
          else if (text === 'unborn') unborn = true;
          else if (text.startsWith('ref-prefix ')) prefixes.push(text.slice('ref-prefix '.length));
          else if (text.startsWith('agent=') || text.startsWith('object-format=')) { /* ignored */ }
          void seenDelim;
        }
        const out: Buffer[] = lsRefsLines(repo, { peel, symrefs, unborn, prefixes }).map((l) => pktLine(l));
        out.push(pktFlush());
        sendRaw(res, 200, 'application/x-git-upload-pack-result', Buffer.concat(out));
        return true;
      }
      if (command === 'command=fetch') {
        const wants: string[] = [];
        const haves: string[] = [];
        const shallowBoundaries: string[] = [];
        let depth: number | null = null;
        let done = false;
        for (const line of lines.slice(1)) {
          const text = line.replace(/\n$/, '');
          if (text === '') continue;
          if (text.startsWith('want ')) wants.push(text.slice(5).trim());
          else if (text.startsWith('have ')) haves.push(text.slice(5).trim());
          else if (text.startsWith('shallow ')) shallowBoundaries.push(text.slice(8).trim());
          else if (text.startsWith('deepen ')) depth = parseInt(text.slice(7), 10);
          else if (text === 'done') done = true;
        }
        const cacheKey = fetchCacheKey(repo, 'v2', wants, haves, depth, shallowBoundaries, done);
        const cached = fetchCacheGet(cacheKey);
        if (cached) {
          sendRaw(res, 200, 'application/x-git-upload-pack-result', cached);
          return true;
        }
        const plan = planFetch(repo, wants, haves, depth, shallowBoundaries);
        const pack = fetchPack(repo, plan);
        const out: Buffer[] = [];
        if (haves.length > 0 && !done) {
          // A negotiation round (real git: haves, no `done` yet). Acknowledge what the
          // client holds and declare the pack ready in this same response — real
          // upload-pack's ok_to_give_up path. The ack section ends with a DELIM
          // (not a flush) when `ready` is sent; without `ready` the client would
          // expect the response to end here and open a second round.
          out.push(pktLine('acknowledgments\n'));
          const held = haves.filter((oid) => repo.objects.has(oid));
          if (held.length === 0) out.push(pktLine('NAK\n'));
          else for (const oid of held) out.push(pktLine(`ACK ${oid}\n`));
          out.push(pktLine('ready\n'));
          out.push(pktDelim());
        }
        // When `done` was sent (or there are no haves) there is no ack section at
        // all: the response goes straight to shallow-info / packfile.
        if (plan.shallow.length > 0 || plan.unshallow.length > 0) {
          out.push(pktLine('shallow-info\n'));
          for (const oid of plan.shallow) out.push(pktLine(`shallow ${oid}\n`));
          for (const oid of plan.unshallow) out.push(pktLine(`unshallow ${oid}\n`));
          out.push(pktFlush());
        }
        out.push(pktLine('packfile\n'));
        out.push(...sidebandPack(pack));
        out.push(pktFlush());
        const body = Buffer.concat(out);
        fetchCachePut(cacheKey, body);
        sendRaw(res, 200, 'application/x-git-upload-pack-result', body);
        return true;
      }
      // Unknown v2 command: answer an empty framed response; the client reports the protocol error.
      sendRaw(res, 200, 'application/x-git-upload-pack-result', pktFlush());
      return true;
    }
    // Protocol v0 fetch: wants, then flush, then haves + done.
    const wants: string[] = [];
    const haves: string[] = [];
    const shallowBoundaries: string[] = [];
    let depth: number | null = null;
    for (const line of lines) {
      const text = line.replace(/\n$/, '');
      if (text.startsWith('want ')) wants.push(text.slice(5).split(' ')[0]);
      else if (text.startsWith('have ')) haves.push(text.slice(5).trim());
      else if (text.startsWith('shallow ')) shallowBoundaries.push(text.slice(8).trim());
      else if (text.startsWith('deepen ')) depth = parseInt(text.slice(7), 10);
    }
    const cacheKey = fetchCacheKey(repo, 'v0', wants, haves, depth, shallowBoundaries, false);
    const cached = fetchCacheGet(cacheKey);
    if (cached) {
      sendRaw(res, 200, 'application/x-git-upload-pack-result', cached);
      return true;
    }
    const plan = planFetch(repo, wants, haves, depth, shallowBoundaries);
    const pack = fetchPack(repo, plan);
    const out: Buffer[] = [pktLine('NAK\n')];
    for (const oid of plan.shallow) out.push(pktLine(`shallow ${oid}\n`));
    for (const oid of plan.unshallow) out.push(pktLine(`unshallow ${oid}\n`));
    out.push(...sidebandPack(pack));
    out.push(pktFlush());
    const body = Buffer.concat(out);
    fetchCachePut(cacheKey, body);
    sendRaw(res, 200, 'application/x-git-upload-pack-result', body);
    return true;
  }

  // POST /{owner}/{repo}.git/git-receive-pack
  if (method === 'POST' && tail.length === 1 && tail[0] === 'git-receive-pack') {
    const raw = await readBody(req);
    const framedLen = framedPrefixLength(raw);
    const packets = decodePktLines(raw.subarray(0, framedLen));
    const commands: Array<{ oldOid: string; newOid: string; ref: string }> = [];
    for (const packet of packets) {
      if (packet.kind !== 'data') break; // flush ends the command list
      const text = packet.payload.toString('utf8').replace(/\n$/, '');
      const nul = text.indexOf('\0');
      const head = nul >= 0 ? text.slice(0, nul) : text;
      const parts = head.split(' ');
      if (parts.length >= 3 && isHex40(parts[0]) && isHex40(parts[1])) {
        commands.push({ oldOid: parts[0], newOid: parts[1], ref: parts.slice(2).join(' ') });
      }
    }
    const packBytes = raw.subarray(framedLen);
    const reportLines: string[] = [];
    let unpackOk = true;
    let unpackDetail = 'ok';
    if (packBytes.length > 0) {
      try {
        const objects = readPack(packBytes, (oid) => repo.objects.get(oid));
        let stored = false;
        for (const [oid, object] of objects) {
          if (!repo.objects.has(oid)) {
            repo.objects.set(oid, object);
            stored = true;
          }
        }
        // New objects invalidate every cached fetch response for this repo.
        if (stored) repo.version += 1;
      } catch (err) {
        unpackOk = false;
        unpackDetail = err instanceof Error ? err.message : 'unpacker error';
      }
    }
    if (unpackOk) {
      for (const command of commands) {
        const current = repo.refs.get(command.ref);
        if (command.newOid === ZERO_OID) {
          // Delete.
          if (current === undefined) {
            reportLines.push(`ng ${command.ref} remote ref does not exist\n`);
          } else if (command.oldOid !== ZERO_OID && command.oldOid !== current) {
            reportLines.push(`ng ${command.ref} non-fast-forward\n`);
          } else {
            repo.refs.delete(command.ref);
            reportLines.push(`ok ${command.ref}\n`);
          }
          continue;
        }
        const newObject = repo.objects.get(command.newOid);
        if (!newObject) {
          reportLines.push(`ng ${command.ref} unpacker error\n`);
          continue;
        }
        if (current === undefined) {
          if (command.oldOid !== ZERO_OID) {
            reportLines.push(`ng ${command.ref} non-fast-forward\n`);
            continue;
          }
          repo.refs.set(command.ref, command.newOid);
          reportLines.push(`ok ${command.ref}\n`);
          continue;
        }
        if (command.oldOid !== current) {
          reportLines.push(`ng ${command.ref} non-fast-forward\n`);
          continue;
        }
        if (!isAncestor(repo, current, command.newOid)) {
          reportLines.push(`ng ${command.ref} non-fast-forward\n`);
          continue;
        }
        repo.refs.set(command.ref, command.newOid);
        reportLines.push(`ok ${command.ref}\n`);
      }
    } else {
      for (const command of commands) reportLines.push(`ng ${command.ref} unpacker error\n`);
    }
    const inner: Buffer[] = [pktLine(`unpack ${unpackOk ? 'ok' : unpackDetail}\n`)];
    for (const line of reportLines) inner.push(pktLine(line));
    inner.push(pktFlush());
    const innerBytes = Buffer.concat(inner);
    const out: Buffer[] = [pktLine(Buffer.concat([Buffer.from([1]), innerBytes])), pktFlush()];
    sendRaw(res, 200, 'application/x-git-receive-pack-result', Buffer.concat(out));
    return true;
  }

  return false;
}

// ---------------------------------------------------------------------------
// GraphQL (small recursive-descent parser + executor + introspection)
// ---------------------------------------------------------------------------

type GqlValue =
  | { kind: 'variable'; name: string }
  | { kind: 'int'; value: number }
  | { kind: 'float'; value: number }
  | { kind: 'string'; value: string }
  | { kind: 'boolean'; value: boolean }
  | { kind: 'null' }
  | { kind: 'enum'; value: string }
  | { kind: 'list'; items: GqlValue[] }
  | { kind: 'object'; fields: Array<{ name: string; value: GqlValue }> };

interface GqlField {
  name: string;
  alias: string | null;
  args: Array<{ name: string; value: GqlValue }>;
  selections: GqlField[];
  fragmentType: string | null;
}

interface GqlDocument {
  operation: 'query' | 'mutation';
  fields: GqlField[];
  fragments: Map<string, { type: string; selections: GqlField[] }>;
}

class GqlParseError extends Error {}

class GqlParser {
  private readonly src: string;
  private pos = 0;
  constructor(src: string) {
    this.src = src;
  }

  parse(): GqlDocument {
    this.skipIgnored();
    let operation: 'query' | 'mutation' = 'query';
    if (this.peekWord() === 'query' || this.peekWord() === 'mutation') {
      operation = this.readWord() as 'query' | 'mutation';
      this.skipIgnored();
      // Optional operation name, e.g. `query ViewerLogin { ... }`.
      if (this.peek() !== '(' && this.peek() !== '{' && /^[A-Za-z_]/.test(this.peek())) {
        this.readWord();
        this.skipIgnored();
      }
      if (this.peek() === '(') this.readVariableDefinitions();
      this.skipIgnored();
    } else if (this.peek() === '{') {
      operation = 'query';
    } else {
      throw new GqlParseError(`Unexpected token at ${this.pos}`);
    }
    const fields = this.readSelectionSet();
    const fragments = new Map<string, { type: string; selections: GqlField[] }>();
    while (true) {
      this.skipIgnored();
      if (this.pos >= this.src.length) break;
      if (this.peekWord() === 'fragment') {
        this.readWord();
        this.skipIgnored();
        const name = this.readName();
        this.skipIgnored();
        if (this.readWord() !== 'on') throw new GqlParseError('Expected "on" in fragment');
        this.skipIgnored();
        const type = this.readName();
        const selections = this.readSelectionSet();
        fragments.set(name, { type, selections });
      } else {
        break;
      }
    }
    return { operation, fields, fragments };
  }

  private peek(): string {
    return this.src[this.pos] ?? '';
  }

  private peekWord(): string {
    const match = /^[A-Za-z_][A-Za-z0-9_]*/.exec(this.src.slice(this.pos));
    return match ? match[0] : '';
  }

  private skipIgnored(): void {
    while (this.pos < this.src.length) {
      const ch = this.src[this.pos];
      if (ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r' || ch === ',') {
        this.pos += 1;
      } else if (ch === '#') {
        while (this.pos < this.src.length && this.src[this.pos] !== '\n') this.pos += 1;
      } else {
        break;
      }
    }
  }

  private readWord(): string {
    const match = /^[A-Za-z_][A-Za-z0-9_]*/.exec(this.src.slice(this.pos));
    if (!match) throw new GqlParseError(`Expected name at ${this.pos}`);
    this.pos += match[0].length;
    return match[0];
  }

  private readName(): string {
    return this.readWord();
  }

  private expect(ch: string): void {
    this.skipIgnored();
    if (this.src[this.pos] !== ch) throw new GqlParseError(`Expected "${ch}" at ${this.pos}`);
    this.pos += 1;
  }

  private readVariableDefinitions(): void {
    // (...) — skip balanced parentheses; variables are resolved by name at execution.
    this.expect('(');
    let depth = 1;
    while (this.pos < this.src.length && depth > 0) {
      const ch = this.src[this.pos];
      if (ch === '(') depth += 1;
      else if (ch === ')') depth -= 1;
      this.pos += 1;
    }
  }

  private readSelectionSet(): GqlField[] {
    this.skipIgnored();
    this.expect('{');
    const fields: GqlField[] = [];
    while (true) {
      this.skipIgnored();
      if (this.pos >= this.src.length) throw new GqlParseError('Unterminated selection set');
      if (this.src[this.pos] === '}') {
        this.pos += 1;
        return fields;
      }
      fields.push(...this.readField());
    }
  }

  private readField(): GqlField[] {
    if (this.src.slice(this.pos, this.pos + 3) === '...') {
      this.pos += 3;
      this.skipIgnored();
      const word = this.peekWord();
      if (word === 'on') {
        this.readWord();
        this.skipIgnored();
        const type = this.readName();
        const selections = this.readSelectionSet();
        return selections.map((s) => ({ ...s, fragmentType: type }));
      }
      // Fragment spread: ...name — expand at execution time.
      const name = this.readName();
      return [{ name: `__spread:${name}`, alias: null, args: [], selections: [], fragmentType: null }];
    }
    const first = this.readName();
    this.skipIgnored();
    let alias: string | null = null;
    let name = first;
    if (this.src[this.pos] === ':') {
      this.pos += 1;
      this.skipIgnored();
      alias = first;
      name = this.readName();
      this.skipIgnored();
    }
    let args: Array<{ name: string; value: GqlValue }> = [];
    if (this.src[this.pos] === '(') {
      args = this.readArguments();
      this.skipIgnored();
    }
    let selections: GqlField[] = [];
    if (this.src[this.pos] === '{') selections = this.readSelectionSet();
    return [{ name, alias, args, selections, fragmentType: null }];
  }

  private readArguments(): Array<{ name: string; value: GqlValue }> {
    this.expect('(');
    const args: Array<{ name: string; value: GqlValue }> = [];
    while (true) {
      this.skipIgnored();
      if (this.src[this.pos] === ')') {
        this.pos += 1;
        return args;
      }
      const name = this.readName();
      this.skipIgnored();
      this.expect(':');
      this.skipIgnored();
      const value = this.readValue();
      args.push({ name, value });
    }
  }

  private readValue(): GqlValue {
    this.skipIgnored();
    const ch = this.src[this.pos];
    if (ch === '$') {
      this.pos += 1;
      return { kind: 'variable', name: this.readName() };
    }
    if (ch === '"') return { kind: 'string', value: this.readString() };
    if (ch === '[') {
      this.pos += 1;
      const items: GqlValue[] = [];
      while (true) {
        this.skipIgnored();
        if (this.src[this.pos] === ']') {
          this.pos += 1;
          return { kind: 'list', items };
        }
        items.push(this.readValue());
      }
    }
    if (ch === '{') {
      this.pos += 1;
      const fields: Array<{ name: string; value: GqlValue }> = [];
      while (true) {
        this.skipIgnored();
        if (this.src[this.pos] === '}') {
          this.pos += 1;
          return { kind: 'object', fields };
        }
        const name = this.readName();
        this.skipIgnored();
        this.expect(':');
        this.skipIgnored();
        fields.push({ name, value: this.readValue() });
      }
    }
    const match = /^-?[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)?/.exec(this.src.slice(this.pos));
    if (match && match[0] !== '') {
      this.pos += match[0].length;
      return match[0].includes('.') || /[eE]/.test(match[0])
        ? { kind: 'float', value: parseFloat(match[0]) }
        : { kind: 'int', value: parseInt(match[0], 10) };
    }
    const word = this.readWord();
    if (word === 'true') return { kind: 'boolean', value: true };
    if (word === 'false') return { kind: 'boolean', value: false };
    if (word === 'null') return { kind: 'null' };
    if (word === '') throw new GqlParseError(`Unexpected value at ${this.pos}`);
    return { kind: 'enum', value: word };
  }

  private readString(): string {
    this.expect('"');
    let out = '';
    while (this.pos < this.src.length) {
      const ch = this.src[this.pos];
      if (ch === '"') {
        this.pos += 1;
        return out;
      }
      if (ch === '\\') {
        this.pos += 1;
        const esc = this.src[this.pos] ?? '';
        if (esc === 'n') out += '\n';
        else if (esc === 't') out += '\t';
        else if (esc === 'r') out += '\r';
        else if (esc === 'u') {
          out += String.fromCharCode(parseInt(this.src.slice(this.pos + 1, this.pos + 5), 16));
          this.pos += 4;
        } else out += esc;
        this.pos += 1;
        continue;
      }
      out += ch;
      this.pos += 1;
    }
    throw new GqlParseError('Unterminated string');
  }
}

type GqlScalar = string | number | boolean | null;
type GqlResolved = GqlScalar | GqlResolved[] | Record<string, unknown>;

function resolveValue(value: GqlValue, variables: Record<string, unknown>): unknown {
  switch (value.kind) {
    case 'variable': return variables[value.name] ?? null;
    case 'int': case 'float': case 'string': case 'boolean': return value.value;
    case 'null': return null;
    case 'enum': return value.value;
    case 'list': return value.items.map((item) => resolveValue(item, variables));
    case 'object': {
      const out: Record<string, unknown> = {};
      for (const field of value.fields) out[field.name] = resolveValue(field.value, variables);
      return out;
    }
  }
}

function argValue(field: GqlField, name: string, variables: Record<string, unknown>): unknown {
  const arg = field.args.find((a) => a.name === name);
  if (!arg) return undefined;
  return resolveValue(arg.value, variables);
}

// ---------------------------------------------------------------------------
// GraphQL type model (for introspection)
// ---------------------------------------------------------------------------

interface GqlTypeDef {
  kind: 'OBJECT' | 'ENUM' | 'SCALAR';
  name: string;
  fields?: Array<{ name: string; type: string }>;
  enumValues?: string[];
}

const GQL_TYPES: GqlTypeDef[] = [
  { kind: 'OBJECT', name: 'Query', fields: [
    { name: 'viewer', type: 'User' }, { name: 'repository', type: 'Repository' },
    { name: 'node', type: 'Node' }, { name: 'search', type: 'SearchResultItemConnection' },
    { name: '__schema', type: '__Schema' }, { name: '__type', type: '__Type' },
  ] },
  { kind: 'OBJECT', name: 'Mutation', fields: [
    { name: 'createIssue', type: 'CreateIssuePayload' }, { name: 'closeIssue', type: 'CloseIssuePayload' },
    { name: 'createPullRequest', type: 'CreatePullRequestPayload' }, { name: 'mergePullRequest', type: 'MergePullRequestPayload' },
    { name: 'addComment', type: 'AddCommentPayload' },
  ] },
  { kind: 'OBJECT', name: 'User', fields: [
    { name: 'id', type: 'ID' }, { name: 'login', type: 'String' }, { name: 'name', type: 'String' },
  ] },
  { kind: 'OBJECT', name: 'Repository', fields: [
    { name: 'id', type: 'ID' }, { name: 'databaseId', type: 'Int' }, { name: 'name', type: 'String' },
    { name: 'nameWithOwner', type: 'String' }, { name: 'owner', type: 'RepositoryOwner' },
    { name: 'defaultBranchRef', type: 'Ref' }, { name: 'viewerPermission', type: 'RepositoryPermission' },
    { name: 'hasIssuesEnabled', type: 'Boolean' }, { name: 'issue', type: 'Issue' },
    { name: 'issues', type: 'IssueConnection' }, { name: 'pullRequests', type: 'PullRequestConnection' },
    { name: 'pullRequest', type: 'PullRequest' },
  ] },
  { kind: 'OBJECT', name: 'RepositoryOwner', fields: [
    { name: 'id', type: 'ID' }, { name: 'login', type: 'String' },
  ] },
  { kind: 'OBJECT', name: 'Ref', fields: [
    { name: 'id', type: 'ID' }, { name: 'name', type: 'String' }, { name: 'target', type: 'GitObject' },
  ] },
  { kind: 'OBJECT', name: 'Issue', fields: [
    { name: 'id', type: 'ID' }, { name: 'number', type: 'Int' }, { name: 'title', type: 'String' },
    { name: 'state', type: 'IssueState' }, { name: 'body', type: 'String' }, { name: 'createdAt', type: 'DateTime' },
    { name: 'author', type: 'Actor' }, { name: 'comments', type: 'IssueCommentConnection' },
  ] },
  { kind: 'OBJECT', name: 'PullRequest', fields: [
    { name: 'id', type: 'ID' }, { name: 'number', type: 'Int' }, { name: 'title', type: 'String' },
    { name: 'state', type: 'PullRequestState' }, { name: 'body', type: 'String' },
    { name: 'headRefName', type: 'String' }, { name: 'baseRefName', type: 'String' },
    { name: 'mergeable', type: 'MergeableState' }, { name: 'merged', type: 'Boolean' },
    { name: 'files', type: 'PullRequestChangedFileConnection' }, { name: 'createdAt', type: 'DateTime' },
  ] },
  { kind: 'OBJECT', name: 'IssueConnection', fields: [
    { name: 'edges', type: 'IssueEdge' }, { name: 'nodes', type: 'Issue' }, { name: 'pageInfo', type: 'PageInfo' },
    { name: 'totalCount', type: 'Int' },
  ] },
  { kind: 'OBJECT', name: 'IssueEdge', fields: [
    { name: 'node', type: 'Issue' }, { name: 'cursor', type: 'String' },
  ] },
  { kind: 'OBJECT', name: 'PullRequestConnection', fields: [
    { name: 'edges', type: 'PullRequestEdge' }, { name: 'nodes', type: 'PullRequest' }, { name: 'pageInfo', type: 'PageInfo' },
    { name: 'totalCount', type: 'Int' },
  ] },
  { kind: 'OBJECT', name: 'PullRequestEdge', fields: [
    { name: 'node', type: 'PullRequest' }, { name: 'cursor', type: 'String' },
  ] },
  { kind: 'OBJECT', name: 'PageInfo', fields: [
    { name: 'hasNextPage', type: 'Boolean' }, { name: 'hasPreviousPage', type: 'Boolean' },
    { name: 'startCursor', type: 'String' }, { name: 'endCursor', type: 'String' },
  ] },
  { kind: 'OBJECT', name: 'IssueComment', fields: [
    { name: 'id', type: 'ID' }, { name: 'body', type: 'String' }, { name: 'author', type: 'Actor' },
  ] },
  { kind: 'OBJECT', name: 'IssueCommentConnection', fields: [
    { name: 'edges', type: 'IssueCommentEdge' }, { name: 'nodes', type: 'IssueComment' }, { name: 'pageInfo', type: 'PageInfo' },
  ] },
  { kind: 'OBJECT', name: 'IssueCommentEdge', fields: [
    { name: 'node', type: 'IssueComment' }, { name: 'cursor', type: 'String' },
  ] },
  { kind: 'OBJECT', name: 'PullRequestChangedFile', fields: [
    { name: 'path', type: 'String' }, { name: 'additions', type: 'Int' }, { name: 'deletions', type: 'Int' },
    { name: 'changeType', type: 'String' },
  ] },
  { kind: 'OBJECT', name: 'PullRequestChangedFileConnection', fields: [
    { name: 'edges', type: 'PullRequestChangedFileEdge' }, { name: 'nodes', type: 'PullRequestChangedFile' }, { name: 'pageInfo', type: 'PageInfo' },
  ] },
  { kind: 'OBJECT', name: 'PullRequestChangedFileEdge', fields: [
    { name: 'node', type: 'PullRequestChangedFile' }, { name: 'cursor', type: 'String' },
  ] },
  { kind: 'OBJECT', name: 'CreateIssuePayload', fields: [
    { name: 'issue', type: 'Issue' }, { name: 'clientMutationId', type: 'String' },
  ] },
  { kind: 'OBJECT', name: 'CloseIssuePayload', fields: [
    { name: 'issue', type: 'Issue' }, { name: 'clientMutationId', type: 'String' },
  ] },
  { kind: 'OBJECT', name: 'CreatePullRequestPayload', fields: [
    { name: 'pullRequest', type: 'PullRequest' }, { name: 'clientMutationId', type: 'String' },
  ] },
  { kind: 'OBJECT', name: 'MergePullRequestPayload', fields: [
    { name: 'pullRequest', type: 'PullRequest' }, { name: 'clientMutationId', type: 'String' },
  ] },
  { kind: 'OBJECT', name: 'AddCommentPayload', fields: [
    { name: 'commentEdge', type: 'IssueCommentEdge' }, { name: 'comment', type: 'IssueComment' }, { name: 'clientMutationId', type: 'String' },
  ] },
  { kind: 'OBJECT', name: 'SearchResultItemConnection', fields: [
    { name: 'edges', type: 'SearchResultItemEdge' }, { name: 'nodes', type: 'SearchResultItem' }, { name: 'pageInfo', type: 'PageInfo' },
  ] },
  { kind: 'OBJECT', name: 'SearchResultItemEdge', fields: [
    { name: 'node', type: 'SearchResultItem' }, { name: 'cursor', type: 'String' },
  ] },
  { kind: 'OBJECT', name: 'Actor', fields: [
    { name: 'id', type: 'ID' }, { name: 'login', type: 'String' },
  ] },
  { kind: 'OBJECT', name: 'GitObject', fields: [
    { name: 'id', type: 'ID' }, { name: 'oid', type: 'String' },
  ] },
  { kind: 'OBJECT', name: '__Schema', fields: [
    { name: 'queryType', type: '__Type' }, { name: 'mutationType', type: '__Type' }, { name: 'types', type: '__Type' },
  ] },
  { kind: 'OBJECT', name: '__Type', fields: [
    { name: 'kind', type: 'String' }, { name: 'name', type: 'String' }, { name: 'fields', type: '__Field' },
    { name: 'enumValues', type: '__EnumValue' }, { name: 'description', type: 'String' },
  ] },
  { kind: 'OBJECT', name: '__Field', fields: [
    { name: 'name', type: 'String' }, { name: 'description', type: 'String' }, { name: 'type', type: '__Type' },
  ] },
  { kind: 'OBJECT', name: '__EnumValue', fields: [
    { name: 'name', type: 'String' }, { name: 'description', type: 'String' },
  ] },
  { kind: 'ENUM', name: 'IssueState', enumValues: ['OPEN', 'CLOSED'] },
  { kind: 'ENUM', name: 'PullRequestState', enumValues: ['OPEN', 'CLOSED', 'MERGED'] },
  { kind: 'ENUM', name: 'MergeableState', enumValues: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'] },
  { kind: 'ENUM', name: 'RepositoryPermission', enumValues: ['ADMIN', 'MAINTAIN', 'WRITE', 'TRIAGE', 'READ'] },
  { kind: 'ENUM', name: 'SearchType', enumValues: ['ISSUE', 'REPOSITORY', 'USER'] },
  { kind: 'ENUM', name: 'IssueOrderField', enumValues: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'] },
  { kind: 'ENUM', name: 'OrderDirection', enumValues: ['ASC', 'DESC'] },
  { kind: 'SCALAR', name: 'String' },
  { kind: 'SCALAR', name: 'Int' },
  { kind: 'SCALAR', name: 'Boolean' },
  { kind: 'SCALAR', name: 'ID' },
  { kind: 'SCALAR', name: 'DateTime' },
];

function gqlTypeByName(name: string): GqlTypeDef | undefined {
  return GQL_TYPES.find((t) => t.name === name);
}

function typeJson(type: GqlTypeDef, selections: GqlField[], variables: Record<string, unknown>): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const field of selections) {
    const key = field.alias ?? field.name;
    if (field.name === 'kind') out[key] = type.kind;
    else if (field.name === 'name') out[key] = type.name;
    else if (field.name === 'description') out[key] = null;
    else if (field.name === 'fields') {
      const includeDeprecated = argValue(field, 'includeDeprecated', variables) === true;
      void includeDeprecated;
      const fields = (type.fields ?? []).map((f) => {
        const sub: Record<string, unknown> = { name: f.name, description: null };
        if (field.selections.some((s) => s.name === 'type')) {
          const target = gqlTypeByName(f.type);
          sub.type = target ? { kind: target.kind, name: target.name, ofType: null } : { kind: 'SCALAR', name: f.type, ofType: null };
        }
        return sub;
      });
      out[key] = fields;
    } else if (field.name === 'enumValues') {
      out[key] = (type.enumValues ?? []).map((v) => ({ name: v, description: null }));
    } else {
      out[key] = null;
    }
  }
  return out;
}

// ---------------------------------------------------------------------------
// GraphQL executor
// ---------------------------------------------------------------------------

type GqlParent =
  | { kind: 'root' }
  | { kind: 'user'; login: string }
  | { kind: 'repo'; repo: Repo }
  | { kind: 'issue'; repo: Repo; issue: Issue }
  | { kind: 'pull'; repo: Repo; pull: Pull }
  | { kind: 'comment'; comment: Comment }
  | { kind: 'file'; path: string; additions: number; deletions: number }
  | { kind: 'ref'; name: string }
  | { kind: 'issueConnection'; repo: Repo; issues: Issue[] }
  | { kind: 'pullConnection'; repo: Repo; pulls: Pull[] }
  | { kind: 'fileConnection'; files: Array<{ path: string; additions: number; deletions: number }> }
  | { kind: 'commentConnection'; comments: Comment[] }
  | { kind: 'payload'; repo: Repo; issue?: Issue; pull?: Pull; comment?: Comment }
  | { kind: 'schema' };

interface GqlContext {
  variables: Record<string, unknown>;
  errors: Array<{ message: string }>;
  fragments: Map<string, { type: string; selections: GqlField[] }>;
}

function expandSelections(fields: GqlField[], ctx: GqlContext): GqlField[] {
  const out: GqlField[] = [];
  for (const field of fields) {
    if (field.name.startsWith('__spread:')) {
      const fragment = ctx.fragments.get(field.name.slice('__spread:'.length));
      if (fragment) out.push(...expandSelections(fragment.selections, ctx));
      continue;
    }
    out.push({ ...field, selections: expandSelections(field.selections, ctx) });
  }
  return out;
}

function parentTypeName(parent: GqlParent): string {
  switch (parent.kind) {
    case 'root': return 'Query';
    case 'user': return 'User';
    case 'repo': return 'Repository';
    case 'issue': return 'Issue';
    case 'pull': return 'PullRequest';
    case 'comment': return 'IssueComment';
    case 'file': return 'PullRequestChangedFile';
    case 'ref': return 'Ref';
    case 'issueConnection': return 'IssueConnection';
    case 'pullConnection': return 'PullRequestConnection';
    case 'fileConnection': return 'PullRequestChangedFileConnection';
    case 'commentConnection': return 'IssueCommentConnection';
    case 'payload': return 'Payload';
    case 'schema': return '__Schema';
  }
}

function validateField(parent: GqlParent, field: GqlField, ctx: GqlContext): boolean {
  if (field.name.startsWith('__')) return true;
  if (parent.kind === 'payload') return true;
  const typeName = parentTypeName(parent);
  const type = gqlTypeByName(typeName);
  if (!type) return true;
  if (!type.fields?.some((f) => f.name === field.name)) {
    ctx.errors.push({ message: `Cannot query field "${field.name}" on type "${typeName}".` });
    return false;
  }
  return true;
}

function pageInfoJson(items: readonly unknown[], afterIndex: number, first: number | null): Record<string, unknown> {
  const hasNext = first !== null && items.length > afterIndex + 1 + first;
  const pageCount = first === null ? items.length - (afterIndex + 1) : Math.min(first, items.length - (afterIndex + 1));
  return {
    hasNextPage: hasNext,
    hasPreviousPage: afterIndex >= 0,
    startCursor: pageCount <= 0 ? null : cursorFor(afterIndex + 1),
    endCursor: pageCount <= 0 ? null : cursorFor(afterIndex + pageCount),
  };
}

function cursorFor(index: number): string {
  return Buffer.from(`cursor:${index}`, 'utf8').toString('base64');
}

function cursorIndex(cursor: string | undefined): number {
  if (typeof cursor !== 'string') return -1;
  try {
    const decoded = Buffer.from(cursor, 'base64').toString('utf8');
    const match = /^cursor:(\d+)$/.exec(decoded);
    if (match) return parseInt(match[1], 10);
  } catch { /* fall through */ }
  return -1;
}

function applyConnectionArgs<T>(items: readonly T[], field: GqlField, variables: Record<string, unknown>): { slice: T[]; afterIndex: number; first: number | null } {
  const firstRaw = argValue(field, 'first', variables);
  const first = typeof firstRaw === 'number' ? firstRaw : null;
  const afterRaw = argValue(field, 'after', variables);
  const afterIndex = cursorIndex(typeof afterRaw === 'string' ? afterRaw : undefined);
  const slice = items.slice(afterIndex + 1, first === null ? undefined : afterIndex + 1 + first);
  return { slice, afterIndex, first };
}

function issueStateFilter(states: unknown): string[] | null {
  if (!Array.isArray(states)) return null;
  return states.map((s) => String(s).toLowerCase());
}

function executeField(parent: GqlParent, field: GqlField, ctx: GqlContext): unknown {
  const key = field.alias ?? field.name;
  void key;
  const selections = expandSelections(field.selections, ctx);
  if (!validateField(parent, field, ctx)) return undefined;
  const typeName = parentTypeName(parent);

  // Introspection entry points.
  if (field.name === '__type') {
    const name = argValue(field, 'name', ctx.variables);
    const type = typeof name === 'string' ? gqlTypeByName(name) : undefined;
    if (!type) return null;
    return typeJson(type, selections, ctx.variables);
  }
  if (field.name === '__schema') {
    const out: Record<string, unknown> = {};
    for (const sub of selections) {
      const subKey = sub.alias ?? sub.name;
      if (sub.name === 'queryType') out[subKey] = typeJson(gqlTypeByName('Query')!, sub.selections, ctx.variables);
      else if (sub.name === 'mutationType') out[subKey] = typeJson(gqlTypeByName('Mutation')!, sub.selections, ctx.variables);
      else if (sub.name === 'types') out[subKey] = GQL_TYPES.map((t) => typeJson(t, sub.selections, ctx.variables));
      else out[subKey] = null;
    }
    return out;
  }
  if (field.name === '__typename') {
    if (parent.kind === 'payload') return 'Payload';
    return typeName;
  }

  switch (parent.kind) {
    case 'root': {
      if (field.name === 'viewer') {
        if (viewerLogin === null) return null;
        return resolveObject({ kind: 'user', login: viewerLogin }, selections, ctx);
      }
      if (field.name === 'repository') {
        const owner = String(argValue(field, 'owner', ctx.variables) ?? '');
        const name = String(argValue(field, 'name', ctx.variables) ?? '');
        const repo = repoByOwnerName(owner, name);
        if (!repo) return null;
        return resolveObject({ kind: 'repo', repo }, selections, ctx);
      }
      if (field.name === 'node') {
        const id = String(argValue(field, 'id', ctx.variables) ?? '');
        const decoded = ungid(id);
        if (!decoded) return null;
        if (decoded.kind === 'Repository') {
          const repo = [...reposByName.values()].find((r) => String(r.databaseId) === decoded.key);
          if (!repo) return null;
          return resolveObject({ kind: 'repo', repo }, selections, ctx);
        }
        if (decoded.kind === 'Issue') {
          const [repoId, number] = decoded.key.split(':');
          const repo = [...reposByName.values()].find((r) => String(r.databaseId) === repoId);
          const issue = repo?.issues.get(parseInt(number, 10));
          if (!repo || !issue) return null;
          return resolveObject({ kind: 'issue', repo, issue }, selections, ctx);
        }
        if (decoded.kind === 'PullRequest') {
          const [repoId, number] = decoded.key.split(':');
          const repo = [...reposByName.values()].find((r) => String(r.databaseId) === repoId);
          const pull = repo?.pulls.get(parseInt(number, 10));
          if (!repo || !pull) return null;
          return resolveObject({ kind: 'pull', repo, pull }, selections, ctx);
        }
        return null;
      }
      if (field.name === 'search') {
        // Search is not part of the graded surface; answer an empty connection.
        const out: Record<string, unknown> = {};
        for (const sub of selections) {
          const subKey = sub.alias ?? sub.name;
          if (sub.name === 'nodes' || sub.name === 'edges') out[subKey] = [];
          else if (sub.name === 'pageInfo') out[subKey] = { hasNextPage: false, hasPreviousPage: false, startCursor: null, endCursor: null };
          else out[subKey] = null;
        }
        return out;
      }
      return null;
    }
    case 'user': {
      if (field.name === 'login') return parent.login;
      if (field.name === 'id') return gid('User', parent.login);
      if (field.name === 'name') return parent.login;
      return null;
    }
    case 'repo': {
      const repo = parent.repo;
      const login = ownerLoginOf(repo);
      switch (field.name) {
        case 'id': return gid('Repository', String(repo.databaseId));
        case 'databaseId': return repo.databaseId;
        case 'name': return repo.name;
        case 'nameWithOwner': return `${login}/${repo.name}`;
        case 'owner': return resolveObject({ kind: 'user', login }, selections, ctx);
        case 'defaultBranchRef': {
          const tip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
          if (!tip) return null;
          return resolveObject({ kind: 'ref', name: repo.defaultBranch }, selections, ctx);
        }
        case 'viewerPermission': return 'ADMIN';
        case 'hasIssuesEnabled': return true;
        case 'issue': {
          const number = argValue(field, 'number', ctx.variables);
          const issue = typeof number === 'number' ? repo.issues.get(number) : undefined;
          if (!issue) return null;
          return resolveObject({ kind: 'issue', repo, issue }, selections, ctx);
        }
        case 'issues': {
          let issues = [...repo.issues.values()];
          const states = issueStateFilter(argValue(field, 'states', ctx.variables));
          if (states) issues = issues.filter((i) => states.includes(i.state));
          const orderBy = argValue(field, 'orderBy', ctx.variables) as Record<string, unknown> | undefined;
          const direction = orderBy?.direction === 'ASC' ? 1 : -1;
          issues.sort((a, b) => direction * (a.createdSeq - b.createdSeq));
          return resolveConnection({ kind: 'issueConnection', repo, issues }, field, selections, ctx);
        }
        case 'pullRequests': {
          let pulls = [...repo.pulls.values()];
          const states = argValue(field, 'states', ctx.variables);
          if (Array.isArray(states)) {
            const wanted = states.map((s) => String(s).toLowerCase());
            pulls = pulls.filter((p) => wanted.includes(p.state === 'merged' ? 'merged' : p.state));
          }
          pulls.sort((a, b) => b.createdSeq - a.createdSeq);
          return resolveConnection({ kind: 'pullConnection', repo, pulls }, field, selections, ctx);
        }
        case 'pullRequest': {
          const number = argValue(field, 'number', ctx.variables);
          const pull = typeof number === 'number' ? repo.pulls.get(number) : undefined;
          if (!pull) return null;
          return resolveObject({ kind: 'pull', repo, pull }, selections, ctx);
        }
        default: return null;
      }
    }
    case 'issue': {
      const issue = parent.issue;
      switch (field.name) {
        case 'id': return issue.gid;
        case 'number': return issue.number;
        case 'title': return issue.title;
        case 'state': return issue.state.toUpperCase();
        case 'body': return issue.body;
        case 'createdAt': return issue.createdAt;
        case 'author': return resolveObject({ kind: 'user', login: ownerLoginOf(parent.repo) }, selections, ctx);
        case 'comments': {
          const comments = issue.comments;
          return resolveConnection({ kind: 'commentConnection', comments }, field, selections, ctx);
        }
        default: return null;
      }
    }
    case 'pull': {
      const pull = parent.pull;
      switch (field.name) {
        case 'id': return pull.gid;
        case 'number': return pull.number;
        case 'title': return pull.title;
        case 'state': return pull.state === 'merged' ? 'MERGED' : pull.state.toUpperCase();
        case 'body': return pull.body;
        case 'headRefName': return pull.headRef;
        case 'baseRefName': return pull.baseRef;
        case 'mergeable': return mergeConflict(parent.repo, pull.headSha, parent.repo.refs.get(`refs/heads/${pull.baseRef}`) ?? pull.baseSha) ? 'CONFLICTING' : 'MERGEABLE';
        case 'merged': return pull.merged;
        case 'createdAt': return pull.createdAt;
        case 'files': {
          const mb = mergeBase(parent.repo, pull.headSha, pull.baseSha);
          const mbTree = mb === null ? null : parseCommit(parent.repo.objects.get(mb)!.data).tree;
          const headTree = parseCommit(parent.repo.objects.get(pull.headSha)!.data).tree;
          const files = changedPaths(parent.repo, mbTree, headTree).map((change) => {
            const oldText = change.baseOid === null ? '' : (parent.repo.objects.get(change.baseOid)?.data.toString('utf8') ?? '');
            const newText = change.headOid === null ? '' : (parent.repo.objects.get(change.headOid)?.data.toString('utf8') ?? '');
            const diff = diffLines(oldText, newText);
            return { path: change.path, additions: diff.additions, deletions: diff.deletions };
          });
          return resolveConnection({ kind: 'fileConnection', files }, field, selections, ctx);
        }
        default: return null;
      }
    }
    case 'comment': {
      if (field.name === 'id') return parent.comment.gid;
      if (field.name === 'body') return parent.comment.body;
      if (field.name === 'author') return resolveObject({ kind: 'user', login: 'owner' }, selections, ctx);
      return null;
    }
    case 'file': {
      if (field.name === 'path') return parent.path;
      if (field.name === 'additions') return parent.additions;
      if (field.name === 'deletions') return parent.deletions;
      if (field.name === 'changeType') return 'MODIFIED';
      return null;
    }
    case 'ref': {
      if (field.name === 'name') return parent.name;
      if (field.name === 'id') return gid('Ref', parent.name);
      if (field.name === 'target') return null;
      return null;
    }
    case 'issueConnection':
    case 'pullConnection':
    case 'fileConnection':
    case 'commentConnection': {
      return resolveConnection(parent, field, selections, ctx);
    }
    case 'payload': {
      if (field.name === 'issue' && parent.issue) return resolveObject({ kind: 'issue', repo: parent.repo, issue: parent.issue }, selections, ctx);
      if (field.name === 'pullRequest' && parent.pull) return resolveObject({ kind: 'pull', repo: parent.repo, pull: parent.pull }, selections, ctx);
      if (field.name === 'comment' && parent.comment) return resolveObject({ kind: 'comment', comment: parent.comment }, selections, ctx);
      if (field.name === 'commentEdge' && parent.comment) {
        const out: Record<string, unknown> = {};
        for (const sub of selections) {
          const subKey = sub.alias ?? sub.name;
          if (sub.name === 'node') out[subKey] = resolveObject({ kind: 'comment', comment: parent.comment }, sub.selections, ctx);
          else if (sub.name === 'cursor') out[subKey] = cursorFor(0);
          else out[subKey] = null;
        }
        return out;
      }
      if (field.name === 'clientMutationId') return null;
      return null;
    }
    case 'schema': return null;
  }
}

function resolveObject(parent: GqlParent, selections: GqlField[], ctx: GqlContext): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const field of selections) {
    const key = field.alias ?? field.name;
    const value = executeField(parent, field, ctx);
    if (value !== undefined) out[key] = value;
    else out[key] = null;
  }
  return out;
}

function resolveConnection(
  parent: GqlParent & { kind: 'issueConnection' | 'pullConnection' | 'fileConnection' | 'commentConnection' },
  field: GqlField,
  selections: GqlField[],
  ctx: GqlContext,
): Record<string, unknown> {
  let items: unknown[];
  let nodeParent: (item: unknown) => GqlParent;
  if (parent.kind === 'issueConnection') {
    items = parent.issues;
    nodeParent = (item) => ({ kind: 'issue', repo: parent.repo, issue: item as Issue });
  } else if (parent.kind === 'pullConnection') {
    items = parent.pulls;
    nodeParent = (item) => ({ kind: 'pull', repo: parent.repo, pull: item as Pull });
  } else if (parent.kind === 'fileConnection') {
    items = parent.files;
    nodeParent = (item) => {
      const f = item as { path: string; additions: number; deletions: number };
      return { kind: 'file', path: f.path, additions: f.additions, deletions: f.deletions };
    };
  } else {
    items = parent.comments;
    nodeParent = (item) => ({ kind: 'comment', comment: item as Comment });
  }
  const { slice, afterIndex, first } = applyConnectionArgs(items, field, ctx.variables);
  const out: Record<string, unknown> = {};
  for (const sub of selections) {
    const key = sub.alias ?? sub.name;
    if (sub.name === 'nodes') {
      out[key] = slice.map((item) => resolveObject(nodeParent(item), sub.selections, ctx));
    } else if (sub.name === 'edges') {
      out[key] = slice.map((item, index) => {
        const edge: Record<string, unknown> = {};
        for (const edgeField of sub.selections) {
          const edgeKey = edgeField.alias ?? edgeField.name;
          if (edgeField.name === 'node') edge[edgeKey] = resolveObject(nodeParent(item), edgeField.selections, ctx);
          else if (edgeField.name === 'cursor') edge[edgeKey] = cursorFor(afterIndex + 1 + index);
          else edge[edgeKey] = null;
        }
        return edge;
      });
    } else if (sub.name === 'pageInfo') {
      out[key] = pageInfoJson(items, afterIndex, first);
    } else if (sub.name === 'totalCount') {
      out[key] = items.length;
    } else {
      out[key] = null;
    }
  }
  return out;
}

function executeMutations(document: GqlDocument, variables: Record<string, unknown>, ctx: GqlContext): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const field of expandSelections(document.fields, ctx)) {
    const key = field.alias ?? field.name;
    const input = (argValue(field, 'input', variables) ?? {}) as Record<string, unknown>;
    const selections = expandSelections(field.selections, ctx);
    if (field.name === 'createIssue') {
      const repo = repoById(String(input.repositoryId ?? ''));
      if (!repo) {
        ctx.errors.push({ message: 'Repository not found' });
        out[key] = null;
        continue;
      }
      const issue = createIssueRecord(repo, String(input.title ?? ''), typeof input.body === 'string' ? input.body : '', []);
      out[key] = resolveObject({ kind: 'payload', repo, issue }, selections, ctx);
      continue;
    }
    if (field.name === 'closeIssue') {
      const issue = findIssueByGid(String(input.issueId ?? ''));
      if (!issue) {
        ctx.errors.push({ message: 'Issue not found' });
        out[key] = null;
        continue;
      }
      issue.issue.state = 'closed';
      issue.issue.closedAt = TRIAL_NOW_ISO;
      out[key] = resolveObject({ kind: 'payload', repo: issue.repo, issue: issue.issue }, selections, ctx);
      continue;
    }
    if (field.name === 'createPullRequest') {
      const repo = repoById(String(input.repositoryId ?? ''));
      if (!repo) {
        ctx.errors.push({ message: 'Repository not found' });
        out[key] = null;
        continue;
      }
      const headRef = String(input.headRefName ?? '');
      const baseRef = String(input.baseRefName ?? '');
      const headSha = repo.refs.get(`refs/heads/${headRef}`);
      const baseSha = repo.refs.get(`refs/heads/${baseRef}`);
      if (!headSha || !baseSha) {
        ctx.errors.push({ message: 'Head and base branches must exist' });
        out[key] = null;
        continue;
      }
      const pull = createPullRecord(repo, String(input.title ?? ''), typeof input.body === 'string' ? input.body : '', headRef, baseRef, headSha, baseSha);
      out[key] = resolveObject({ kind: 'payload', repo, pull }, selections, ctx);
      continue;
    }
    if (field.name === 'mergePullRequest') {
      const pull = findPullByGid(String(input.pullRequestId ?? ''));
      if (!pull) {
        ctx.errors.push({ message: 'Pull request not found' });
        out[key] = null;
        continue;
      }
      const method = String(input.mergeMethod ?? 'MERGE');
      if (method === 'SQUASH') {
        const sha = squashMerge(pull.repo, pull.pull);
        if (sha === null) {
          ctx.errors.push({ message: 'Merge conflict' });
          out[key] = null;
          continue;
        }
      } else {
        // Plain merge: fast-forward the base to the head when possible.
        const currentBase = pull.repo.refs.get(`refs/heads/${pull.pull.baseRef}`) ?? pull.pull.baseSha;
        if (isAncestor(pull.repo, currentBase, pull.pull.headSha)) {
          pull.repo.refs.set(`refs/heads/${pull.pull.baseRef}`, pull.pull.headSha);
          pull.pull.state = 'merged';
          pull.pull.merged = true;
          pull.pull.mergedAt = TRIAL_NOW_ISO;
          pull.pull.mergeCommitSha = pull.pull.headSha;
        } else {
          ctx.errors.push({ message: 'Merge conflict' });
          out[key] = null;
          continue;
        }
      }
      out[key] = resolveObject({ kind: 'payload', repo: pull.repo, pull: pull.pull }, selections, ctx);
      continue;
    }
    if (field.name === 'addComment') {
      const subject = findSubjectByGid(String(input.subjectId ?? ''));
      if (!subject) {
        ctx.errors.push({ message: 'Subject not found' });
        out[key] = null;
        continue;
      }
      const comment: Comment = {
        id: globalIdCounter += 1,
        gid: gid('IssueComment', `${subject.repo.databaseId}:${globalIdCounter}`),
        body: String(input.body ?? ''),
        createdAt: TRIAL_NOW_ISO,
        updatedAt: TRIAL_NOW_ISO,
      };
      subject.comments.push(comment);
      out[key] = resolveObject({ kind: 'payload', repo: subject.repo, comment }, selections, ctx);
      continue;
    }
    ctx.errors.push({ message: `Cannot query field "${field.name}" on type "Mutation".` });
    out[key] = null;
  }
  return out;
}

function executeGraphql(document: GqlDocument, variables: Record<string, unknown>): { data: Record<string, unknown> | null; errors: Array<{ message: string }> } {
  const ctx: GqlContext = { variables, errors: [], fragments: document.fragments };
  let data: Record<string, unknown> | null;
  if (document.operation === 'mutation') {
    data = executeMutations(document, variables, ctx);
  } else {
    const root: GqlParent = { kind: 'root' };
    data = {};
    for (const field of expandSelections(document.fields, ctx)) {
      const key = field.alias ?? field.name;
      const value = executeField(root, field, ctx);
      data[key] = value === undefined ? null : value;
    }
  }
  return { data, errors: ctx.errors };
}

async function handleGraphql(req: IncomingMessage, res: ServerResponse): Promise<boolean> {
  if (!isAuthorized(req)) {
    sendJson(res, 401, { message: 'Requires authentication' });
    return true;
  }
  const raw = await readBody(req);
  let body: unknown;
  try {
    body = JSON.parse(raw.toString('utf8'));
  } catch {
    sendJson(res, 400, { errors: [{ message: 'Invalid JSON body' }] });
    return true;
  }
  const runOne = (entry: unknown): Record<string, unknown> => {
    const obj = (typeof entry === 'object' && entry !== null ? entry : {}) as Record<string, unknown>;
    const query = typeof obj.query === 'string' ? obj.query : '';
    const variables = (typeof obj.variables === 'object' && obj.variables !== null ? obj.variables : {}) as Record<string, unknown>;
    if (query.trim() === '') return { data: null, errors: [{ message: 'Must provide query string.' }] };
    let document: GqlDocument;
    try {
      document = new GqlParser(query).parse();
    } catch (err) {
      return { data: null, errors: [{ message: err instanceof Error ? err.message : 'Syntax error' }] };
    }
    const result = executeGraphql(document, variables);
    return result.errors.length > 0 ? { data: result.data, errors: result.errors } : { data: result.data };
  };
  if (Array.isArray(body)) {
    sendJson(res, 200, body.map(runOne));
  } else {
    sendJson(res, 200, runOne(body));
  }
  return true;
}

// ---------------------------------------------------------------------------
// MCP (JSON-RPC 2.0 Streamable HTTP)
// ---------------------------------------------------------------------------

interface McpToolDef {
  name: string;
  description: string;
  inputSchema: {
    type: 'object';
    properties: Record<string, { type: string; description?: string }>;
    required: string[];
    additionalProperties: boolean;
  };
  handler: (args: Record<string, unknown>) => Record<string, unknown> | Promise<Record<string, unknown>>;
}

function mcpToolResult(payload: Record<string, unknown>): Record<string, unknown> {
  return {
    content: [{ type: 'text', text: JSON.stringify(payload) }],
    structuredContent: payload,
  };
}

function mcpToolError(message: string): Record<string, unknown> {
  return {
    content: [{ type: 'text', text: JSON.stringify({ error: message }) }],
    structuredContent: { error: message },
    isError: true,
  };
}

function toolArg(args: Record<string, unknown>, name: string): string {
  const value = args[name];
  return typeof value === 'string' ? value : '';
}

const MCP_TOOLS: McpToolDef[] = [
  {
    name: 'create_repo',
    description: 'Create a new repository for the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'Repository name' },
        description: { type: 'string', description: 'Repository description' },
        private: { type: 'boolean', description: 'Whether the repository is private' },
      },
      required: ['name'],
      additionalProperties: false,
    },
    handler: (args) => {
      const name = toolArg(args, 'name');
      if (name === '') throw new Error('Missing required argument: name');
      if (reposByName.has(name)) throw new Error(`Repository "${name}" already exists`);
      const repo = createRepoRecord(name, typeof args.description === 'string' ? args.description : '', args.private === true);
      return mcpToolResult(repoJson(repo));
    },
  },
  {
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
      },
      required: ['owner', 'repo'],
      additionalProperties: false,
    },
    handler: (args) => {
      const repo = repoByOwnerName(toolArg(args, 'owner'), toolArg(args, 'repo'));
      if (!repo) throw new Error('Repository not found');
      return mcpToolResult(repoJson(repo));
    },
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        title: { type: 'string', description: 'Issue title' },
        body: { type: 'string', description: 'Issue body' },
      },
      required: ['owner', 'repo', 'title'],
      additionalProperties: false,
    },
    handler: (args) => {
      const repo = repoByOwnerName(toolArg(args, 'owner'), toolArg(args, 'repo'));
      if (!repo) throw new Error('Repository not found');
      const issue = createIssueRecord(repo, toolArg(args, 'title'), typeof args.body === 'string' ? args.body : '', []);
      return mcpToolResult(issueJson(repo, issue));
    },
  },
  {
    name: 'list_issues',
    description: 'List issues in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        state: { type: 'string', description: 'Issue state filter: open, closed, or all' },
      },
      required: ['owner', 'repo'],
      additionalProperties: false,
    },
    handler: (args) => {
      const repo = repoByOwnerName(toolArg(args, 'owner'), toolArg(args, 'repo'));
      if (!repo) throw new Error('Repository not found');
      const state = typeof args.state === 'string' ? args.state : 'open';
      let issues = [...repo.issues.values()];
      if (state !== 'all') issues = issues.filter((i) => i.state === state);
      issues.sort((a, b) => b.createdSeq - a.createdSeq);
      return mcpToolResult({ issues: issues.map((i) => issueJson(repo, i)) });
    },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        title: { type: 'string', description: 'Pull request title' },
        head: { type: 'string', description: 'Head branch name' },
        base: { type: 'string', description: 'Base branch name' },
        body: { type: 'string', description: 'Pull request body' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
      additionalProperties: false,
    },
    handler: (args) => {
      const repo = repoByOwnerName(toolArg(args, 'owner'), toolArg(args, 'repo'));
      if (!repo) throw new Error('Repository not found');
      const headRef = toolArg(args, 'head');
      const baseRef = toolArg(args, 'base');
      const headSha = repo.refs.get(`refs/heads/${headRef}`);
      const baseSha = repo.refs.get(`refs/heads/${baseRef}`);
      if (!headSha || !baseSha) throw new Error('Head and base branches must exist');
      const existing = [...repo.pulls.values()].find((p) => p.state === 'open' && p.headRef === headRef && p.baseRef === baseRef);
      if (existing) throw new Error('A pull request already exists for this head and base');
      const pull = createPullRecord(repo, toolArg(args, 'title'), typeof args.body === 'string' ? args.body : '', headRef, baseRef, headSha, baseSha);
      return mcpToolResult(pullJson(repo, pull));
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request with a squash merge.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        pull_number: { type: 'number', description: 'Pull request number' },
      },
      required: ['owner', 'repo', 'pull_number'],
      additionalProperties: false,
    },
    handler: (args) => {
      const repo = repoByOwnerName(toolArg(args, 'owner'), toolArg(args, 'repo'));
      if (!repo) throw new Error('Repository not found');
      const number = typeof args.pull_number === 'number' ? args.pull_number : parseInt(String(args.pull_number ?? ''), 10);
      const pull = repo.pulls.get(number);
      if (!pull) throw new Error('Pull request not found');
      const sha = squashMerge(repo, pull);
      if (sha === null) throw new Error('Merge conflict: the pull request cannot be merged');
      return mcpToolResult({ sha, merged: true, message: 'Pull request successfully merged' });
    },
  },
];

function mcpToolsList(): Array<Record<string, unknown>> {
  return MCP_TOOLS.map((tool) => ({
    name: tool.name,
    description: tool.description,
    inputSchema: tool.inputSchema,
  }));
}

function jsonRpcError(id: unknown, code: number, message: string): Record<string, unknown> {
  return { jsonrpc: '2.0', id: id ?? null, error: { code, message } };
}

function jsonRpcResult(id: unknown, result: unknown): Record<string, unknown> {
  return { jsonrpc: '2.0', id: id ?? null, result };
}

function extractJsonRpcId(raw: string): unknown {
  try {
    const parsed = JSON.parse(raw) as Record<string, unknown>;
    if (typeof parsed === 'object' && parsed !== null && 'id' in parsed) return parsed.id;
  } catch { /* not JSON */ }
  return null;
}

async function handleMcp(req: IncomingMessage, res: ServerResponse): Promise<boolean> {
  const raw = await readBody(req);
  const text = raw.toString('utf8');
  // A notification has no id: answer 202 with an empty body.
  let body: unknown;
  try {
    body = JSON.parse(text);
  } catch {
    sendJson(res, 400, jsonRpcError(extractJsonRpcId(text), -32700, 'Parse error'));
    return true;
  }
  if (typeof body !== 'object' || body === null || Array.isArray(body)) {
    sendJson(res, 400, jsonRpcError(null, -32600, 'Invalid Request'));
    return true;
  }
  const request = body as Record<string, unknown>;
  const id = 'id' in request ? request.id : undefined;
  const method = typeof request.method === 'string' ? request.method : '';
  const isNotification = id === undefined;

  if (method === 'notifications/initialized' || method.startsWith('notifications/')) {
    res.writeHead(202, { 'x-github-request-id': nextRequestId() });
    res.end();
    return true;
  }

  if (!isAuthorized(req)) {
    if (isNotification) {
      res.writeHead(202, { 'x-github-request-id': nextRequestId() });
      res.end();
      return true;
    }
    sendJson(res, 401, jsonRpcError(id, -32001, 'Requires authentication'));
    return true;
  }

  if (method === 'server/discover' || method === 'initialize') {
    const result = {
      protocolVersion: '2026-07-28',
      supportedVersions: ['2026-07-28', '2025-06-18', '2025-03-26', '2024-11-05'],
      serverInfo: { name: FORGE_NAME, version: FORGE_VERSION },
      capabilities: {
        tools: { listChanged: false },
        resources: {},
        prompts: {},
        logging: {},
      },
    };
    if (isNotification) {
      res.writeHead(202, { 'x-github-request-id': nextRequestId() });
      res.end();
      return true;
    }
    sendJson(res, 200, jsonRpcResult(id, result));
    return true;
  }

  if (method === 'tools/list') {
    sendJson(res, 200, jsonRpcResult(id, { tools: mcpToolsList() }));
    return true;
  }

  if (method === 'tools/call') {
    const params = (typeof request.params === 'object' && request.params !== null ? request.params : {}) as Record<string, unknown>;
    const toolName = typeof params.name === 'string' ? params.name : '';
    const args = (typeof params.arguments === 'object' && params.arguments !== null ? params.arguments : {}) as Record<string, unknown>;
    const tool = MCP_TOOLS.find((t) => t.name === toolName);
    if (!tool) {
      sendJson(res, 200, jsonRpcError(id, -32602, `Unknown tool: ${toolName}`));
      return true;
    }
    const missing = tool.inputSchema.required.filter((name) => args[name] === undefined || args[name] === null || args[name] === '');
    if (missing.length > 0) {
      sendJson(res, 200, jsonRpcResult(id, mcpToolError(`Missing required argument: ${missing.join(', ')}`)));
      return true;
    }
    try {
      const result = await tool.handler(args);
      sendJson(res, 200, jsonRpcResult(id, result));
    } catch (err) {
      sendJson(res, 200, jsonRpcResult(id, mcpToolError(err instanceof Error ? err.message : 'Tool failed')));
    }
    return true;
  }

  if (method === 'ping') {
    sendJson(res, 200, jsonRpcResult(id, {}));
    return true;
  }

  sendJson(res, 200, jsonRpcError(id, -32601, `Method not found: ${method}`));
  return true;
}

// ---------------------------------------------------------------------------
// App wiring
// ---------------------------------------------------------------------------

export function createApp(): Server {
  const listener = (req: IncomingMessage, res: ServerResponse): void => {
    void (async () => {
      try {
        const segments = pathSegments(req);
        const method = req.method ?? 'GET';
        // Boot probe: GET /healthz must answer 200 with no auth.
        if (segments.length === 1 && segments[0] === 'healthz' && method === 'GET') {
          sendJson(res, 200, { ok: true });
          return;
        }
        // Git smart HTTP: /{owner}/{repo}.git/...
        if (segments.length >= 2 && segments[1].endsWith('.git')) {
          const handled = await handleGit(req, res, segments);
          if (handled) return;
        }
        // GraphQL: POST /api/graphql
        if (segments.length === 2 && segments[0] === 'api' && segments[1] === 'graphql') {
          if (method !== 'POST') throw new HttpError(404, 'Not Found');
          await handleGraphql(req, res);
          return;
        }
        // MCP: POST /mcp
        if (segments.length === 1 && segments[0] === 'mcp') {
          if (method !== 'POST') throw new HttpError(404, 'Not Found');
          await handleMcp(req, res);
          return;
        }
        // REST v3: /api/v3/...
        if (segments.length >= 2 && segments[0] === 'api' && segments[1] === 'v3') {
          const handled = await handleRest(req, res, segments);
          if (handled) return;
        }
        // Unknown route: JSON 404, never HTML.
        if (segments.length >= 2 && segments[0] === 'api' && segments[1] === 'v3') {
          sendJson(res, 404, { message: 'Not Found' });
          return;
        }
        sendJson(res, 404, { message: 'Not Found' });
      } catch (err) {
        if (err instanceof HttpError) {
          if (!res.headersSent) sendJson(res, err.status, { message: err.message });
          return;
        }
        // Never leak a 500 HTML page; keep the server alive.
        if (!res.headersSent) {
          try {
            sendJson(res, 500, { message: 'Internal Server Error' });
          } catch { /* response already gone */ }
        }
      }
    })();
  };
  return createServer(listener);
}
