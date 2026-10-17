import * as vscode from 'vscode';
import { abbreviations } from './abbreviations';

const names = [...abbreviations.keys()];

function extensible(s: string): boolean {
  return names.some((n) => n.length > s.length && n.startsWith(s));
}

// `\` and a run of letters or of symbol characters, ending at the change
const pending = /\\([A-Za-z]+|[-<>=/|]+)$/;

export function rewrite(
  before: string,
  typed: string,
): { back: number; ahead: number; symbol: string } | undefined {
  const m = pending.exec(before);
  if (!m) {
    return undefined;
  }
  const name = m[1];
  const longer = name + typed;
  if (typed.length === 1 && extensible(longer)) {
    return undefined;
  } else if (typed.length === 1 && abbreviations.has(longer)) {
    return { back: name.length + 1, ahead: 1, symbol: abbreviations.get(longer)! };
  } else if (abbreviations.has(name)) {
    return { back: name.length + 1, ahead: 0, symbol: abbreviations.get(name)! };
  }
  return undefined;
}

export function registerAbbreviations(context: vscode.ExtensionContext): void {
  let applying = false;

  context.subscriptions.push(
    vscode.workspace.onDidChangeTextDocument(async (e) => {
      if (applying || e.document.languageId !== 'caraml' || e.contentChanges.length !== 1) {
        return;
      }
      if (!vscode.workspace.getConfiguration('caraml').get<boolean>('abbreviations.enabled', true)) {
        return;
      }
      const editor = vscode.window.activeTextEditor;
      const change = e.contentChanges[0];
      if (editor?.document !== e.document || change.text.length === 0) {
        return;
      }

      const start = change.range.start;
      const r = rewrite(e.document.lineAt(start.line).text.slice(0, start.character), change.text);
      if (!r) {
        return;
      }
      const range = new vscode.Range(start.translate(0, -r.back), start.translate(0, r.ahead));

      const version = e.document.version;
      applying = true;
      try {
        if (editor.document.version === version) {
          await editor.edit((b) => b.replace(range, r.symbol), {
            undoStopBefore: false,
            undoStopAfter: false,
          });
        }
      } finally {
        applying = false;
      }
    }),
  );
}
