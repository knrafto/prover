// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import * as child_process from 'child_process';

import * as vscode from 'vscode';

type Range = {
  start: number,
  end: number,
};

type HighlightedRange = {
  range: Range,
  kind: string,
};

type Response = {
  highlighting: HighlightedRange[],
};

// TODO: configure
let binaryPath =
    '/Users/knrafto/code/prover/.stack-work/dist/x86_64-osx/Cabal-2.4.0.1/build/prover/prover';


let highlightStyles: Map<string, string> = new Map([
  ['lparen', 'symbol'],
  ['rparen', 'symbol'],
  ['comma', 'symbol'],
  ['dot', 'symbol'],
  ['underscore', 'reserved_word'],
  ['colon', 'reserved_word'],
  ['colon_equals', 'reserved_word'],
  ['sigma', 'reserved_word'],
  ['pi', 'reserved_word'],
  ['lambda', 'reserved_word'],
  ['equals', 'reserved_word'],
  ['times', 'reserved_word'],
  ['arrow', 'reserved_word'],
  ['type', 'reserved_word'],
  ['define', 'reserved_word'],
  ['assume', 'reserved_word'],
  ['prove', 'reserved_word'],
  ['local_name', 'local_name'],
  ['defined_name', 'global_name'],
  ['assumed_name', 'global_name'],
  ['unbound_name', 'local_name'],
]);

let styles: Map<string, vscode.TextEditorDecorationType> = new Map([
  [
    'local_name',
    vscode.window.createTextEditorDecorationType({color: '#FFFFFF'})
  ],
  [
    'global_name',
    vscode.window.createTextEditorDecorationType({color: '#4EC9B0'})
  ],
  [
    'reserved_word',
    vscode.window.createTextEditorDecorationType({color: '#FF0000'})
  ],
  ['symbol', vscode.window.createTextEditorDecorationType({color: '#00FF00'})],
]);

let cache: Map<string, Response> = new Map();

function convertRange(
    document: vscode.TextDocument, range: Range): vscode.Range {
  return new vscode.Range(
      document.positionAt(range.start), document.positionAt(range.end));
}

// Run a command to completion, reporting its output and exit code.
function runCommand(
    command: string, args: string[],
    callback: (stdout: string, stderr: string) => void) {
  console.log('Running command:', command, args.join(' '));
  var child = child_process.spawn(command, args);

  var stdout = '';
  var stderr = '';

  child.stdout.setEncoding('utf8');
  child.stdout.on('data', (data) => {
    stdout += data.toString();
  });

  child.stderr.setEncoding('utf8');
  child.stderr.on('data', (data) => {
    stderr += data.toString();
  });

  child.on('close', () => {
    callback(stdout, stderr);
  });
}

function onChange(path: string) {
  if (!path.endsWith('.pf')) {
    return;
  }

  runCommand(binaryPath, ['--json', path], (stdout, stderr) => {
    if (stderr.length !== 0) {
      console.log('Error:\n' + stderr);
    }

    var resp: Response = {
      highlighting: [],
    };
    try {
      resp = JSON.parse(stdout);
    } catch (e) {
      console.log('Error decoding JSON:', e);
    }

    cache.set(path, resp);
    updateEditors();
  });
}

function updateEditors() {
  for (let textEditor of vscode.window.visibleTextEditors) {
    let path = textEditor.document.uri.path;
    let resp = cache.get(path);
    if (resp === undefined) {
      continue;
    }

    let decorations: Map<string, vscode.Range[]> = new Map();
    for (let highlightedRange of resp.highlighting) {
      let range = convertRange(textEditor.document, highlightedRange.range);
      let style = highlightStyles.get(highlightedRange.kind);
      if (style === undefined) {
        console.log(
            'Could not find style for highlighted range of kind',
            highlightedRange.kind);
        continue;
      }
      let ranges = decorations.get(style);
      if (ranges !== undefined) {
        ranges.push(range);
      } else {
        decorations.set(style, [range]);
      }
    }

    for (let [styleName, decorationType] of styles) {
      textEditor.setDecorations(
          decorationType, decorations.get(styleName) || []);
    }
  }
}

export function activate(context: vscode.ExtensionContext) {
  console.log('Extension "prover" is now active!');

  for (let textEditor of vscode.window.visibleTextEditors) {
    onChange(textEditor.document.uri.path);
  }

  context.subscriptions.push(vscode.workspace.onDidSaveTextDocument(
      (document) => onChange(document.uri.path)));

  context.subscriptions.push(
      vscode.window.onDidChangeVisibleTextEditors((_) => updateEditors()));
}

// this method is called when your extension is deactivated
export function deactivate() {}
