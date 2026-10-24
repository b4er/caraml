import { ChildProcess, execFile, spawn } from 'child_process';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import * as vscode from 'vscode';

// find the caraml executable, set it up when it is missing.
//
// the latest compiler release carries, independent of the extension version,
//   caraml-<platform>-<arch>.tar.gz   (pre-built, `caraml` or `caraml.exe` inside)
//   caraml-src.tar.gz                 (`cabal sdist` of haskell/)
// with <platform>-<arch> as Node names them: linux-x64, darwin-arm64, win32-x64, ...
//
// downloads and builds install into $XDG_BIN_HOME, else ~/.local/bin (on Windows too)

const repo = 'b4er/caraml';
const exe = process.platform === 'win32' ? 'caraml.exe' : 'caraml';
const dismissedKey = 'caraml.setup.dismissed';

interface Asset {
  name: string;
  browser_download_url: string;
}

interface Release {
  tag_name: string;
  assets: Asset[];
}

export function findServer(): string | undefined {
  const c = vscode.workspace.getConfiguration('caraml');
  return c.get<string>('server.path') || process.env.CARAML_SERVER || onPath(exe) || installed();
}

function binDir(): string {
  return process.env.XDG_BIN_HOME || path.join(os.homedir(), '.local', 'bin');
}

// the binary a download or build installed, when it is not on PATH
function installed(): string | undefined {
  const file = path.join(binDir(), exe);
  try {
    fs.accessSync(file, fs.constants.X_OK);
    return file;
  } catch {
    return undefined;
  }
}

function onPathDir(dir: string): boolean {
  const norm = (d: string) => path.resolve(d).toLowerCase();
  return (process.env.PATH ?? '').split(path.delimiter).some((d) => d && norm(d) === norm(dir));
}

function onPath(name: string): string | undefined {
  const exts = process.platform === 'win32' ? ['', ...(process.env.PATHEXT ?? '').split(';')] : [''];
  for (const dir of (process.env.PATH ?? '').split(path.delimiter)) {
    for (const ext of exts) {
      const file = path.join(dir, name + ext);
      try {
        fs.accessSync(file, fs.constants.X_OK);
        if (fs.statSync(file).isFile()) {
          return file;
        }
      } catch {
        // not here
      }
    }
  }
  return undefined;
}

let running = false;

export async function setupServer(context: vscode.ExtensionContext, explicit = false): Promise<void> {
  if (running || (!explicit && context.globalState.get<boolean>(dismissedKey))) {
    return;
  }
  running = true;
  try {
    if (!explicit) {
      const answer = await vscode.window.showWarningMessage(
        'The CaraML language server (caraml lsp) was not found.',
        'Set Up…', 'Not Now', "Don't Ask Again",
      );
      if (answer === "Don't Ask Again") {
        await context.globalState.update(dismissedKey, true);
      }
      if (answer !== 'Set Up…') {
        return;
      }
    }
    const file = await wizard();
    if (!file) {
      return;
    }
    if (path.dirname(file) !== binDir()) {
      await vscode.workspace.getConfiguration('caraml')
        .update('server.path', file, vscode.ConfigurationTarget.Global);
      vscode.window.showInformationMessage(`CaraML: using ${file}.`);
      return;
    }
    await vscode.commands.executeCommand('caraml.restartServer');
    vscode.window.showInformationMessage(onPathDir(binDir())
      ? `CaraML: installed ${file}.`
      : `CaraML: installed ${file}. Add ${binDir()} to PATH to run caraml from a shell.`);
  } catch (e) {
    if (e instanceof Error && e.name === 'AbortError') {
      return;
    }
    vscode.window.showErrorMessage(`CaraML setup failed: ${e instanceof Error ? e.message : e}`);
  } finally {
    running = false;
  }
}

interface Choice extends vscode.QuickPickItem {
  run?: () => Promise<string | undefined>;
  missing?: { reason: string; help?: string };
}

async function wizard(): Promise<string | undefined> {
  const target = `${process.platform}-${process.arch}`;

  const [release, cabal, ghc] = await vscode.window.withProgress(
    { location: vscode.ProgressLocation.Window, title: 'CaraML: looking for a server' },
    () => Promise.all([findRelease(), toolVersion('cabal'), toolVersion('ghc')]),
  );

  const binary = release?.assets.find((a) => a.name === `caraml-${target}.tar.gz`);
  const sdist = release?.assets.find((a) => a.name === 'caraml-src.tar.gz');

  const download: Choice = {
    label: '$(cloud-download) Download a pre-built server',
    description: binary ? `(caraml ${release!.tag_name} for ${target})` : undefined,
    run: binary && (() => fetchBinary(binary)),
    missing: binary ? undefined : {
      reason: release
        ? `Release ${release.tag_name} has no pre-built server for ${target}.`
        : 'No release of caraml could be reached.',
      help: `https://github.com/${repo}/releases`,
    },
  };

  const cabalOk = cabal !== undefined && Number(cabal.split('.')[0]) >= 3;
  const build: Choice = {
    label: '$(tools) Build from source',
    description: cabalOk && ghc ? `(cabal ${cabal}, ghc ${ghc}; takes several minutes)` : undefined,
    run: sdist && cabalOk && ghc ? () => buildSdist(sdist) : undefined,
    missing: !sdist ? {
      reason: release ? `Release ${release.tag_name} has no source archive.` : 'No release of caraml could be reached.',
      help: `https://github.com/${repo}/releases`,
    } : !cabalOk ? {
      reason: cabal ? `Building needs cabal 3 or later, found cabal ${cabal}.` : 'Building needs cabal 3 or later on PATH.',
      help: 'https://www.haskell.org/ghcup/',
    } : !ghc ? {
      reason: 'Building needs ghc on PATH.',
      help: 'https://www.haskell.org/ghcup/',
    } : undefined,
  };

  const locate: Choice = {
    label: '$(file) Locate an installed caraml',
    description: '(sets caraml.server.path)',
    run: locateBinary,
  };

  const choices = [download, build, locate]
    .sort((a, b) => Number(!a.run) - Number(!b.run))
    .map((c) => c.run ? c : { ...c, detail: `$(circle-slash) ${c.missing!.reason}` });

  const pick = await vscode.window.showQuickPick(choices, {
    title: 'Set up the CaraML language server',
    placeHolder: 'How do you want to get caraml?',
    ignoreFocusOut: true,
  });
  if (!pick) {
    return undefined;
  }
  if (pick.run) {
    return pick.run();
  }
  const { reason, help } = pick.missing!;
  const open = help ? await vscode.window.showWarningMessage(reason, 'Open Help') : undefined;
  if (open) {
    vscode.env.openExternal(vscode.Uri.parse(help!));
  }
  return undefined;
}

async function findRelease(): Promise<Release | undefined> {
  try {
    const res = await fetch(`https://api.github.com/repos/${repo}/releases/latest`, {
      headers: { Accept: 'application/vnd.github+json' },
      signal: AbortSignal.timeout(10_000),
    });
    return res.ok ? await res.json() as Release : undefined;
  } catch {
    // offline or rate limited
    return undefined;
  }
}

function toolVersion(tool: string): Promise<string | undefined> {
  return new Promise((resolve) =>
    execFile(tool, ['--numeric-version'], { timeout: 10_000 }, (err, stdout) =>
      resolve(err ? undefined : stdout.trim())));
}

// download and unpack into a fresh temporary directory, which the caller removes
async function unpack(asset: Asset, signal?: AbortSignal): Promise<string> {
  const res = await fetch(asset.browser_download_url, { signal });
  if (!res.ok) {
    throw new Error(`downloading ${asset.name}: HTTP ${res.status}`);
  }
  const tmp = await fs.promises.mkdtemp(path.join(os.tmpdir(), 'caraml-'));
  const out = path.join(tmp, 'out');
  await fs.promises.mkdir(out);
  const archive = path.join(tmp, asset.name);
  await fs.promises.writeFile(archive, Buffer.from(await res.arrayBuffer()));
  await run('tar', ['-xzf', archive, '-C', out]);
  return out;
}

async function removeTmp(out: string): Promise<void> {
  await fs.promises.rm(path.dirname(out), { recursive: true, force: true });
}

async function fetchBinary(asset: Asset): Promise<string | undefined> {
  return vscode.window.withProgress(
    { location: vscode.ProgressLocation.Notification, title: `CaraML: downloading ${asset.name}`, cancellable: true },
    async (_, token) => {
      const abort = new AbortController();
      token.onCancellationRequested(() => abort.abort());
      const out = await unpack(asset, abort.signal);
      try {
        const file = await findFile(out, exe);
        if (!file) {
          throw new Error(`${asset.name} contains no ${exe}`);
        }
        // copy next to the target, then rename: the temporary directory may be on another
        // file system, and a running server keeps its old binary
        const dest = path.join(binDir(), exe);
        await fs.promises.mkdir(binDir(), { recursive: true });
        await fs.promises.copyFile(file, `${dest}.new`);
        await fs.promises.chmod(`${dest}.new`, 0o755);
        await fs.promises.rename(`${dest}.new`, dest);
        return dest;
      } finally {
        await removeTmp(out);
      }
    },
  );
}

async function findFile(dir: string, name: string): Promise<string | undefined> {
  for (const e of await fs.promises.readdir(dir, { withFileTypes: true })) {
    const p = path.join(dir, e.name);
    if (e.isFile() && e.name === name) {
      return p;
    }
    const sub = e.isDirectory() ? await findFile(p, name) : undefined;
    if (sub) {
      return sub;
    }
  }
  return undefined;
}

let log: vscode.OutputChannel | undefined;

async function buildSdist(asset: Asset): Promise<string | undefined> {
  log ??= vscode.window.createOutputChannel('CaraML Setup');
  log.show(true);
  const bin = binDir();
  return vscode.window.withProgress(
    { location: vscode.ProgressLocation.Notification, title: 'CaraML: building caraml with cabal', cancellable: true },
    async (progress, token) => {
      const abort = new AbortController();
      token.onCancellationRequested(() => abort.abort());
      progress.report({ message: `downloading ${asset.name}` });
      const out = await unpack(asset, abort.signal);
      try {
        // a cabal sdist unpacks to caraml-<version>/
        const top = (await fs.promises.readdir(out)).find((e) => e.startsWith('caraml-'));
        const src = top ? path.join(out, top) : out;
        progress.report({ message: 'cabal install (see the CaraML Setup output)' });
        await fs.promises.mkdir(bin, { recursive: true });
        await run('cabal', [
          'install', 'exe:caraml',
          `--installdir=${bin}`, '--install-method=copy', '--overwrite-policy=always',
        ], { cwd: src, log, signal: abort.signal });
        return path.join(bin, exe);
      } finally {
        await removeTmp(out);
      }
    },
  );
}

async function locateBinary(): Promise<string | undefined> {
  const picked = await vscode.window.showOpenDialog({
    title: 'Locate the caraml executable',
    openLabel: 'Use as CaraML Server',
    canSelectFiles: true,
    canSelectFolders: false,
    canSelectMany: false,
  });
  return picked?.[0].fsPath;
}

interface RunOptions {
  cwd?: string;
  log?: vscode.OutputChannel;
  signal?: AbortSignal;
}

function run(command: string, args: string[], opts: RunOptions = {}): Promise<void> {
  return new Promise((resolve, reject) => {
    opts.log?.appendLine(`$ ${command} ${args.join(' ')}`);
    const child: ChildProcess = spawn(command, args, { cwd: opts.cwd, signal: opts.signal });
    const stderr: string[] = [];
    child.stdout?.on('data', (d) => opts.log?.append(d.toString()));
    child.stderr?.on('data', (d) => {
      stderr.push(d.toString());
      opts.log?.append(d.toString());
    });
    child.on('error', reject);
    child.on('close', (code) => code === 0
      ? resolve()
      : reject(new Error(`${command} exited with ${code}${opts.log ? '' : `: ${stderr.join('').trim()}`}`)));
  });
}
