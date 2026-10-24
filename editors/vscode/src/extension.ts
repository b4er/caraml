import * as readline from 'readline';
import * as vscode from 'vscode';
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
} from 'vscode-languageclient/node';
import { registerAbbreviations } from './abbreviate';
import { registerSymbols } from './symbols';
import { findServer, setupServer } from './wizard';

let client: LanguageClient | undefined;

function currentConfig(): object {
  const c = vscode.workspace.getConfiguration('caraml');
  return {
    inlayHints: {
      enabled: c.get<boolean>('inlayHints.enabled', false),
      literals: c.get<boolean>('inlayHints.literals', false),
      hideTypeVariables: c.get<boolean>('inlayHints.hideTypeVariables', true),
    },
  };
}

function newClient(command: string): LanguageClient {
  const c = vscode.workspace.getConfiguration('caraml');
  const args = c.get<string[]>('server.args', []);

  const serverOptions: ServerOptions = {
    run: { command, args: [...args, 'lsp'] },
    debug: { command, args: [...args, '-vv', 'lsp'] },
  };

  const stdioOptions = {
    stdout: (input: NodeJS.ReadableStream, out: vscode.LogOutputChannel) =>
      lines(input, (l) => out.info(l)),
    stderr: (input: NodeJS.ReadableStream, out: vscode.LogOutputChannel) =>
      lines(input, (l) => {
        const m = /^\[(error|warn|info|debug|trace)\] (.*)$/.exec(l);
        if (!m) {
          return out.error(l);
        }
        const msg = m[2];
        switch (m[1]) {
          case 'error': return out.error(msg);
          case 'warn': return out.warn(msg);
          case 'info': return out.info(msg);
          case 'debug': return out.debug(msg);
          default: return out.trace(msg);
        }
      }),
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: 'file', language: 'caraml' }],
    initializationOptions: currentConfig(),
    stdioOptions,
  };

  return new LanguageClient('caraml', 'CaraML LSP', serverOptions, clientOptions);
}

function lines(input: NodeJS.ReadableStream, f: (line: string) => void): void {
  readline.createInterface({ input, crlfDelay: Infinity, terminal: false }).on('line', f);
}

export function activate(context: vscode.ExtensionContext): void {
  registerAbbreviations(context);
  registerSymbols(context);

  // without a server, offer to set one up; an install restarts, a located binary sets
  // `caraml.server.path`, which restarts
  const start = async (explicit = false) => {
    const command = findServer();
    if (!command) {
      void setupServer(context, explicit);
      return;
    }
    client = newClient(command);
    await client.start();
  };

  const restart = async (explicit = false) => {
    await client?.stop();
    client = undefined;
    await start(explicit);
  };

  void start();

  context.subscriptions.push(
    vscode.commands.registerCommand('caraml.restartServer', () => restart(true)),
    vscode.commands.registerCommand('caraml.setupServer', () => setupServer(context, true)),

    vscode.workspace.onDidChangeConfiguration(async (e) => {
      if (e.affectsConfiguration('caraml.server')) {
        await restart();
      } else if (e.affectsConfiguration('caraml.inlayHints')) {
        await client?.sendNotification('workspace/didChangeConfiguration', {
          settings: currentConfig(),
        });
      }
    }),
  );
}

export function deactivate(): Thenable<void> | undefined {
  return client?.stop();
}
