// Entrypoint for the forge trial.
//
// What this file does, in order:
//   1. Finds the trial environment's address from MAKEFUN_ENV_URL.
//   2. Starts the forge server on a kernel-chosen port.
//   3. Tells the environment which port to dial.
//   4. Waits, polling, until the environment reports the trial finished.
//   5. Shuts the server down and leaves with a clean exit.
//
// Nothing here talks to the network beyond the trial environment, and it
// makes no model calls: it is just the boot-and-wait glue around app.ts.

import { createApp } from './app.ts';

// One request to the environment may take this long before we abandon it.
const REQUEST_BUDGET_MS = 30_000;

// Pauses between retries start here, double after every miss, and never
// grow past the ceiling below.
const FIRST_PAUSE_MS = 250;
const LONGEST_PAUSE_MS = 5_000;

// Where the environment answers its readiness probe.
const DONE_PATH = '/done';
// Where the environment records this entry's port.
const REGISTER_PATH = '/register';

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

// Read the environment's origin, or stop right away when it is absent.
// Without it there is nobody to register with, so there is no trial to run.
function envOrigin(): string {
  const origin = process.env.MAKEFUN_ENV_URL;
  if (!origin) {
    console.error('MAKEFUN_ENV_URL is not set; cannot register with the trial environment.');
    process.exit(1);
  }
  return origin.replace(/\/$/, '');
}

// One JSON round trip to the environment. Throws on a network failure, a
// timeout, or a non-2xx status other than the ones the caller tolerates.
async function callEnv(
  url: string,
  method: 'GET' | 'POST',
  payload?: unknown,
  toleratedStatuses: number[] = [],
): Promise<unknown> {
  const response = await fetch(url, {
    method,
    headers: { 'content-type': 'application/json' },
    body: payload === undefined ? undefined : JSON.stringify(payload),
    signal: AbortSignal.timeout(REQUEST_BUDGET_MS),
  });
  if (!response.ok && !toleratedStatuses.includes(response.status)) {
    throw new Error(`env answered ${response.status} to ${method} ${url}`);
  }
  const text = await response.text();
  return text ? JSON.parse(text) : null;
}

// Keep trying an env call until it works, spacing attempts out with a
// backoff that grows and then holds steady. A 409 from /register means
// another entry already claimed the slot; the caller passes it in as
// tolerated, and we treat it as a successful registration.
async function callEnvWithRetries(
  url: string,
  method: 'GET' | 'POST',
  payload?: unknown,
  toleratedStatuses: number[] = [],
): Promise<unknown> {
  let pause = FIRST_PAUSE_MS;
  for (;;) {
    try {
      return await callEnv(url, method, payload, toleratedStatuses);
    } catch (error) {
      const detail = error instanceof Error ? error.message : String(error);
      console.error(`env call failed (${detail}); retrying in ${pause}ms`);
      await sleep(pause);
      pause = Math.min(pause * 2, LONGEST_PAUSE_MS);
    }
  }
}

// Wait for the environment to say the trial is over. The environment
// answers immediately on every probe, so this is a tight poll loop with
// retries folded in; it only returns once the body says done.
async function waitForDone(origin: string): Promise<void> {
  for (;;) {
    const body = (await callEnvWithRetries(`${origin}${DONE_PATH}`, 'GET')) as {
      done?: unknown;
    };
    if (body && body.done === true) {
      return;
    }
    await sleep(FIRST_PAUSE_MS);
  }
}

async function main(): Promise<void> {
  const origin = envOrigin();

  const server = createApp();
  await new Promise<void>((resolve, reject) => {
    server.once('error', reject);
    // Port 0 hands the choice to the kernel; 8080 belongs to the suite.
    server.listen(0, '127.0.0.1', () => resolve());
  });
  const bound = server.address();
  if (!bound || typeof bound === 'string') {
    console.error('forge server did not bind to a port.');
    process.exit(1);
  }
  const port = bound.port;
  console.log(`forge listening on port ${port}`);

  await callEnvWithRetries(
    `${origin}${REGISTER_PATH}`,
    'POST',
    { port },
    [409],
  );
  console.log('registered with the trial environment; waiting for done');

  await waitForDone(origin);

  await new Promise<void>((resolve) => server.close(() => resolve()));
  console.log('trial done; forge shut down');
}

main().catch((error) => {
  console.error('entrypoint failed:', error instanceof Error ? error.message : error);
  process.exit(1);
});
