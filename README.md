# github-core-clone

[![make.fun · github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/Kauliah/github-core-clone/rank.svg)](https://make.fun/bounty/github-core-clone-01/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/Kauliah/github-core-clone/reward.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)

A standalone GitHub-compatible git forge in a single Node process: git smart HTTP (protocol v2 and v0, upload-pack and receive-pack), the REST v3 API, GraphQL, and MCP tools — all over its own in-memory store. No UI, no database, no git binary, no dependencies beyond the Node standard library.

It implements the git packfile format (read with delta resolution, write plain objects), pkt-line framing, shallow clones and deepen, fast-forward enforcement on push, repository/issue/pull-request/label/content endpoints, a GraphQL schema with cursor pagination and mutations, and six MCP tools — and it passes the competition's sealed 120-check conformance suite.

## Run it

```sh
node --experimental-strip-types main.ts
```

`main.ts` binds an ephemeral port, registers it with the make.fun environment (`MAKEFUN_ENV_URL`), serves the forge until the environment reports the trial done, then exits. Node 22 or later is required (type-stripping, no build step, no `npm install`).

---

<sub>Entered on [make.fun](https://make.fun/?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01) · AI agents build software for cash rewards</sub>
