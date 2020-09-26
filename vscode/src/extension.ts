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

type Diagnostic = {
  range: Range,
  message: string,
};

type Response = {
  highlighting: HighlightedRange[],
  diagnostics: Diagnostic[],
};

// TODO: configure
let binaryPath =
    '/Users/knrafto/code/prover/dist-newstyle/build/x86_64-osx/ghc-8.10.1/prover-0.1.0.0/x/prover/build/prover/prover';

let highlightStyles: Map<string, string> = new Map([
  ['var_name', 'base1'],
  ['def_name', 'blue'],
  ['axiom_name', 'blue'],
  ['rewrite_name', 'blue'],
  ['unbound_name', 'red'],
  ['type', 'blue'],
  ['hole', 'cyan'],
]);

// Colors from Solarized dark: https://ethanschoonover.com/solarized/
let colors: Map<string, string> = new Map([
  ['base03', '#002b36'],
  ['base02', '#073642'],
  ['base01', '#586e75'],
  ['base00', '#657b83'],
  ['base0', '#839496'],
  ['base1', '#93a1a1'],
  ['base2', '#eee8d5'],
  ['base3', '#fdf6e3'],
  ['yellow', '#b58900'],
  ['orange', '#cb4b16'],
  ['red', '#dc322f'],
  ['magenta', '#d33682'],
  ['violet', '#6c71c4'],
  ['blue', '#268bd2'],
  ['cyan', '#2aa198'],
  ['green', '#859900'],
]);

let styles: Map<string, vscode.TextEditorDecorationType> = new Map();
for (let [name, color] of colors) {
  styles.set(name, vscode.window.createTextEditorDecorationType({
    color: color,
    rangeBehavior: vscode.DecorationRangeBehavior.ClosedClosed,
  }));
}

let cache: Map<string, Response> = new Map();

let diagnosticCollection =
    vscode.languages.createDiagnosticCollection('prover');

function convertRange(
    document: vscode.TextDocument, range: Range): vscode.Range {
  return new vscode.Range(
      document.positionAt(range.start), document.positionAt(range.end));
}

function convertDiagnostic(
    document: vscode.TextDocument, diagnostic: Diagnostic): vscode.Diagnostic {
  return new vscode.Diagnostic(
      convertRange(document, diagnostic.range), diagnostic.message);
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
      diagnostics: [],
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

    diagnosticCollection.set(
        textEditor.document.uri,
        resp.diagnostics.map(
            (diag) => convertDiagnostic(textEditor.document, diag)));
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
