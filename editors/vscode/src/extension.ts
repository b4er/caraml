import * as readline from 'readline';
import * as vscode from 'vscode';
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
} from 'vscode-languageclient/node';
import { registerAbbreviations } from './abbreviate';

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

function newClient(): LanguageClient {
  const c = vscode.workspace.getConfiguration('caraml');
  const command = c.get<string>('server.path') || process.env.CARAML_SERVER || 'caraml';
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
          out.error(l);
          return;
        }
        const msg = m[2];
        switch (m[1]) {
          case 'error': out.error(msg); break;
          case 'warn': out.warn(msg); break;
          case 'info': out.info(msg); break;
          case 'debug': out.debug(msg); break;
          default: out.trace(msg);
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

  client = newClient();
  client.start();

  const restart = async () => {
    await client?.stop();
    client = newClient();
    await client.start();
  };

  context.subscriptions.push(
    vscode.commands.registerCommand('caraml.restartServer', restart),

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
