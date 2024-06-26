// The module 'vscode' contains the VS Code extensibility API
// Import the necessary extensibility types to use in your code below
import * as vscode from "vscode";
import * as fs from "fs";
import * as path from "path";
import axios from "axios";

// This method is called when your extension is activated. Activation is
// controlled by the activation events defined in package.json.
export function activate(context: vscode.ExtensionContext) {
  const sandpiperButton = new SandPiperButton();
  sandpiperButton.show();
  const svgButton = new SvgButton();
  svgButton.show();
  const navTlvButton = new NavTlvButton();
  navTlvButton.show();
  const waveformButton = new WaveformButton();
  waveformButton.show();

  
  const sandpiperCommand = vscode.commands.registerCommand(
    "extension.sandpiperSaas",
    async () => {
      const editor = vscode.window.activeTextEditor;
      if (editor) {
        const document = editor.document;
        if (document.languageId === "tlverilog") {
          const tlvCode = document.getText();
          const inputFilePath = document.fileName;
          try {
            await compileTLVerilogWithSandPiper(tlvCode, inputFilePath);
          } catch (error) {
            vscode.window.showErrorMessage(
              `SandPiper SaaS compilation failed: ${error.message}`
            );
          }
        } else {
          vscode.window.showInformationMessage(
            "The active file is not a TL-Verilog file."
          );
        }
      } else {
        vscode.window.showInformationMessage("No active text editor found.");
      }
    }
  );
  context.subscriptions.push(sandpiperCommand);

  const showSvgCommand = vscode.commands.registerCommand(
    "extension.showSvg",
    async () => {
      const editor = vscode.window.activeTextEditor;
      if (editor) {
        const document = editor.document;
        if (document.languageId === "tlverilog") {
          const tlvCode = document.getText();
          const inputFilePath = document.fileName;
          try {
            const svgFilePath = await generateSvgFile(tlvCode, inputFilePath);
            showSvgInWebview(svgFilePath);
          } catch (error) {
            vscode.window.showErrorMessage(
              `Failed to generate SVG: ${error.message}`
            );
          }
        } else {
          vscode.window.showInformationMessage(
            "The active file is not a TL-Verilog file."
          );
        }
      } else {
        vscode.window.showInformationMessage("No active text editor found.");
      }
    }
  );
  context.subscriptions.push(showSvgCommand);


  const showNavTlvCommand = vscode.commands.registerCommand(
    "extension.showNavTlv",
    async () => {
      const editor = vscode.window.activeTextEditor;
      if (editor) {
        const document = editor.document;
        if (document.languageId === "tlverilog") {
          const tlvCode = document.getText();
          try {
            const navTlvHtml = await generateNavTlvHtml(tlvCode);
            showNavTlvInWebview(navTlvHtml);
          } catch (error) {
            vscode.window.showErrorMessage(
              `Failed to generate Nav TLV: ${error.message}`
            );
          }
        } else {
          vscode.window.showInformationMessage(
            "The active file is not a TL-Verilog file."
          );
        }
      } else {
        vscode.window.showInformationMessage("No active text editor found.");
      }
    }
  );
  context.subscriptions.push(showNavTlvCommand);


  const generateWaveformCommand = vscode.commands.registerCommand(
    "extension.generateWaveform",
    async () => {
      const editor = vscode.window.activeTextEditor;
      if (editor) {
        const document = editor.document;
        if (document.languageId === "systemverilog" || document.languageId === "verilog") {
          try {
            await generateAndViewWaveform(document.fileName);
          } catch (error) {
            vscode.window.showErrorMessage(`Failed to generate waveform: ${error.message}`);
          }
        } else {
          vscode.window.showInformationMessage("The active file is not a SystemVerilog or Verilog file.");
        }
      } else {
        vscode.window.showInformationMessage("No active text editor found.");
      }
    }
  );
  context.subscriptions.push(generateWaveformCommand);

  // System Verilog Hover Provider
  context.subscriptions.push(
    vscode.languages.registerHoverProvider(
      "tlverilog",
      new tlverilogHoverProvider()
    )
  );

  // instantiate system verilog module
  context.subscriptions.push(
    vscode.commands.registerCommand(
      "extension.tlverilog.instantiateModule",
      instantiateModuleInteract
    )
  );
}

class tlverilogHoverProvider implements vscode.HoverProvider {
  private _excludedText: RegExp;

  constructor() {
    this._excludedText = RegExp(
      /\b(alias|always|always_comb|always_ff|always_latch|and|assert|assign|assume|automatic|before|begin|bind|bins|binsof|bit|break|buf|bufif0|bufif1|byte|case|casex|casez|cell|chandle|class|clocking|cmos|config|const|constraint|context|continue|cover|covergroup|coverpoint|cross|deassign|default|defparam|design|disable|dist|do|edge|else|end|endcase|endclass|endclocking|endconfig|endfunction|endgenerate|endgroup|endinterface|endmodule|endpackage|endprimitive|endprogram|endproperty|endspecify|endsequence|endtable|endtask|enum|event|expect|export|extends|extern|final|first_match|for|force|foreach|forever|fork|forkjoin|function|generate|genvar|highz0|highz1|if|iff|ifnone|ignore_bins|illegal_bins|import|incdir|include|initial|inout|input|inside|instance|int|integer|interface|intersect|join|join_any|join_none|large|liblist|library|local|localparam|logic|longint|macromodule|matches|medium|modport|module|nand|negedge|new|nmos|nor|noshowcancelled|not|notif0|notif1|null|or|output|package|packed|parameter|pmos|posedge|primitive|priority|program|property|protected|pull0|pull1|pulldown|pullup|pulsestyle_onevent|pulsestyle_ondetect|pure|rand|randc|randcase|randsequence|rcmos|real|realtime|ref|reg|release|repeat|return|rnmos|rpmos|rtran|rtranif0|rtranif1|scalared|sequence|shortint|shortreal|showcancelled|signed|small|solve|specify|specparam|static|string|strong0|strong1|struct|super|supply0|supply1|table|tagged|task|this|throughout|time|timeprecision|timeunit|tran|tranif0|tranif1|tri|tri0|tri1|triand|trior|trireg|type|typedef|union|unique|unsigned|use|uwire|var|vectored|virtual|void|wait|wait_order|wand|weak0|weak1|while|wildcard|wire|with|within|wor|xnor|xor)\b/
    );
  }

  public provideHover(
    document: vscode.TextDocument,
    position: vscode.Position,
    token: vscode.CancellationToken
  ): vscode.Hover {
    // get word start and end
    let textRange = document.getWordRangeAtPosition(position);

    // hover word
    let targetText = document.getText(textRange);

    if (targetText.search(this._excludedText) !== -1) {
      // tlverilog keywords
      return;
    } else {
      // find declaration
      let declarationText = this._findDeclaration(
        document,
        position,
        targetText
      );
      if (declarationText !== undefined) {
        return new vscode.Hover([
          { language: "tlverilog", value: declarationText.element },
          declarationText.comment,
        ]);
      } else {
        return;
      }
    }
  }

  private _findDeclaration(
    document: vscode.TextDocument,
    position: vscode.Position,
    target: string
  ): { element: string; comment: string } {
    // check target is valid variable name
    if (target.search(/[A-Za-z_][A-Za-z0-9_]*/g) === -1) {
      return;
    }

    let variableType = String.raw`\b(input|output|inout|reg|wire|logic|integer|bit|byte|shortint|int|longint|time|shortreal|real|double|realtime)\b\s+`;
    let variableTypeStart = "^" + variableType;
    let paraType = String.raw`^\b(parameter|localparam)\b\s+\b${target}\b`;

    let regexTarget = RegExp(String.raw`\b${target}\b`);
    let regexVariableType = RegExp(variableType, "g");
    let regexVariableTypeStart = RegExp(variableTypeStart);
    let regexParaType = RegExp(paraType);

    // from previous line to first line
    for (let i = position.line - 1; i >= 0; i--) {
      // text at current line
      let line = document.lineAt(i).text;
      let element = line
        .replace(/\/\/.*/, "")
        .trim()
        .replace(/\s+/g, " ");
      let lastChar = element.charAt(element.length - 1);
      if (lastChar === "," || lastChar === ";") {
        // remove last ',' or ';'
        element = element.substring(0, element.length - 1);
      }

      // find variable declaration type
      if (element.search(regexVariableTypeStart) !== -1) {
        // replace type to '', like input, output
        let subText = element.replace(regexVariableType, "").trim();

        // replace array to '', like [7:0]
        subText = subText.replace(/(\[.+?\])?/g, "").trim();
        if (subText.search(regexTarget) !== -1) {
          let comment = getPrefixedComment(document, i);
          if (comment) return { element: element, comment: comment };
          else {
            comment = getSuffixedComment(document, i);
            return { element: element, comment: comment };
          }
        }
      }

      // find parameter declaration type
      if (element.search(regexParaType) !== -1) {
        let comment = getPrefixedComment(document, i);
        if (comment) return { element: element, comment: comment };
        else {
          comment = getSuffixedComment(document, i);
          return { element: element, comment: comment };
        }
      }
    }
  }
}

function getPrefixedComment(document: vscode.TextDocument, lineNo: number) {
  let i = lineNo - 1;
  let buf = "";
  while (true) {
    let line = document.lineAt(i).text.trim();
    if (!line.startsWith("//")) break;
    buf = line.substring(3) + "\n" + buf;
    i--;
  }
  return buf;
}

function getSuffixedComment(
  document: vscode.TextDocument,
  lineNo: number
): string {
  // Spearate comment after the declaration
  let line = document.lineAt(lineNo).text;
  let idx = line.indexOf("//");
  if (idx !== -1) return line.substr(idx + 2).trim();
  else return undefined;
}

function getDirectories(srcpath: string): string[] {
  return fs
    .readdirSync(srcpath)
    .filter((file) => fs.statSync(path.join(srcpath, file)).isDirectory());
}

function getFiles(srcpath: string): string[] {
  return fs
    .readdirSync(srcpath)
    .filter((file) => fs.statSync(path.join(srcpath, file)).isFile());
}

function selectFile(currentDir?: string): Thenable<string> {
  currentDir = currentDir || vscode.workspace.rootPath;

  let dirs = getDirectories(currentDir);
  // if is subdirectory, add '../'
  if (currentDir !== vscode.workspace.rootPath) {
    dirs.unshift("..");
  }
  // all files ends with '.sv'
  let files = getFiles(currentDir).filter(
    (file) => file.endsWith(".v") || file.endsWith(".sv")
  );

  // available quick pick items
  let items = dirs.concat(files);

  return vscode.window.showQuickPick(items).then((selected) => {
    if (!selected) {
      return;
    }

    // if is a directory
    let location = path.join(currentDir, selected);
    if (fs.statSync(location).isDirectory()) {
      return selectFile(location);
    }

    // return file path
    return location;
  });
}

function instantiatePort(ports: string[]): string {
  let port = "";
  // .NAME(NAME)
  for (let i = 0; i < ports.length; i++) {
    let element = ports[i];
    port += `\t.${element}(${element})`;

    if (i !== ports.length - 1) {
      port += ",";
    }
    port += "\n";
  }
  return port;
}

function instantiateModule(srcpath: string) {
  if (!srcpath || !fs.statSync(srcpath).isFile) {
    return;
  }

  // remove comment
  let content = fs
    .readFileSync(srcpath, "utf8")
    .replace(/\/\/.*/g, "")
    .replace(/\/\*[\s\S]*?\*\//g, "");
  if (content.indexOf("module") === -1) {
    return;
  }
  // module 2001 style
  let moduleIO = content.substring(
    content.indexOf("module"),
    content.indexOf(";")
  );
  let moduleName = moduleIO.match(/module\s+\b([A-Za-z_][A-Za-z0-9_]*)\b/)[1];
  let parametersName = [];
  let portsName = [];
  let lines = moduleIO.split("\n");

  // find all parameters and ports
  lines.forEach((line) => {
    line = line.trim();
    let matched = line.match(/parameter\s+\b([A-Za-z_][A-Za-z0-9_]*)\b/);
    if (matched !== null) {
      parametersName.push(matched[1]);
    }

    if (line.search(/^\b(input|output|inout)\b/) !== -1) {
      let variables = line
        .replace(
          /\b(input|output|inout|reg|wire|logic|integer|bit|byte|shortint|int|longint|time|shortreal|real|double|realtime)\b/g,
          ""
        )
        .replace(/(\[.+?\])?/g, "")
        .replace(/\s+/g, "")
        .split(",")
        .forEach((variable) => {
          if (variable) {
            portsName.push(variable);
          }
        });
    }
  });

  if (portsName.length === 0) {
    return;
  }

  let prefix = vscode.workspace.getConfiguration("tlverilog")["instancePrefix"];

  let paramString = ``;
  if (parametersName.length > 0) {
    paramString = `\n#(\n${instantiatePort(parametersName)})\n`;
  }

  return new vscode.SnippetString()
    .appendText(moduleName + " ")
    .appendText(paramString)
    .appendPlaceholder(prefix)
    .appendPlaceholder(`${moduleName}(\n`)
    .appendText(instantiatePort(portsName))
    .appendText(");\n");
}

function instantiateModuleInteract() {
  let filePath = path.dirname(vscode.window.activeTextEditor.document.fileName);
  selectFile(filePath).then((srcpath) => {
    let inst = instantiateModule(srcpath);
    vscode.window.activeTextEditor.insertSnippet(inst);
  });
}

async function compileTLVerilogWithSandPiper(
  tlvCode: string,
  inputFilePath: string
): Promise<void> {
  const externSettings =
    vscode.workspace.getConfiguration("tlverilog").get("formattingSettings") ||
    [];
  const args = `-i test.tlv -o test.sv --m4out out/m4out ${externSettings.join(
    " "
  )} --iArgs`;

  try {
    const response = await axios.post(
      "https://faas.makerchip.com/function/sandpiper-faas",
      JSON.stringify({
        args,
        responseType: "json",
        sv_url_inc: true,
        files: {
          "test.tlv": tlvCode,
        },
      }),
      {
        headers: {
          "Content-Type": "application/json",
        },
      }
    );

    if (response.status !== 200) {
      throw new Error(
        `SandPiper SaaS request failed with status ${response.status}`
      );
    }

    const data = response.data;
    if (data["out/test.sv"]) {
      const verilog = (data["out/test.sv"] as string)
        .replace(
          '`include "test_gen.sv"',
          "// gen included here\n" + data["out/test_gen.sv"]
        )
        .split("\n")
        .filter((line) => !line.startsWith('`include "sp_default.vh"'))
        .join("\n");

      // Save the generated Verilog code to files in the same directory as the input file
      const outputDirectory = path.dirname(inputFilePath);
      const outputFilePath = path.join(outputDirectory, "output.sv");
      const genFilePath = path.join(outputDirectory, "output_gen.sv");

      fs.writeFileSync(outputFilePath, verilog);
      fs.writeFileSync(genFilePath, data["out/test_gen.sv"]);

      vscode.window.showInformationMessage(
        `Generated Verilog code saved to ${outputFilePath} and ${genFilePath}`
      );
    } else {
      throw new Error(
        "SandPiper SaaS compilation failed: No output generated."
      );
    }
  } catch (error) {
    let errorMessage = "SandPiper SaaS compilation failed: ";
    if (axios.isAxiosError(error)) {
      errorMessage += error.message;
    } else {
      errorMessage += error;
    }
    vscode.window.showErrorMessage(errorMessage);
    throw new Error(errorMessage);
  }
}

class SandPiperButton implements vscode.StatusBarItem {
  private statusBarItem: vscode.StatusBarItem;

  alignment: vscode.StatusBarAlignment;
  priority: number;
  text: string;
  tooltip: string;
  color: string;
  command: string | undefined;

  constructor(
    alignment: vscode.StatusBarAlignment = vscode.StatusBarAlignment.Left,
    priority: number = 0
  ) {
    this.statusBarItem = vscode.window.createStatusBarItem(alignment, priority);
    this.statusBarItem.command = "extension.sandpiperSaas";
    this.statusBarItem.text = "$(rocket) SandPiper";
    this.statusBarItem.tooltip = "Compile TL-Verilog using SandPiper SaaS";
    this.text = "$(rocket) SandPiper";
    this.tooltip = "Compile TL-Verilog using SandPiper SaaS";
    this.alignment = alignment;
    this.priority = priority;
  }

  show() {
    this.statusBarItem.show();
  }

  hide() {
    this.statusBarItem.hide();
  }

  dispose() {
    this.statusBarItem.dispose();
  }
}


async function generateSvgFile(tlvCode: string, inputFilePath: string): Promise<string> {
    const externSettings =
      vscode.workspace.getConfiguration("tlverilog").get("formattingSettings") || [];
    const args = `-i test.tlv --graphTrans --svg ${externSettings.join(" ")} --iArgs`;
  
    try {
      const response = await axios.post(
        "https://faas.makerchip.com/function/sandpiper-faas",
        JSON.stringify({
          args,
          responseType: "json",
          sv_url_inc: true,
          files: {
            "test.tlv": tlvCode,
          },
        }),
        {
          headers: {
            "Content-Type": "application/json",
          },
        }
      );
  
      if (response.status !== 200) {
        throw new Error(`SandPiper SaaS request failed with status ${response.status}`);
      }
  
      const data = response.data;
      if (data["out/test.m5out_graph.svg"]) {
        const outputDirectory = path.dirname(inputFilePath);
        const svgFilePath = path.join(outputDirectory, "test.m5out_graph.svg");
        fs.writeFileSync(svgFilePath, data["out/test.m5out_graph.svg"]);
        return svgFilePath;
      } else {
        throw new Error("SandPiper SaaS compilation failed: No SVG output generated.");
      }
    } catch (error) {
      let errorMessage = "SandPiper SaaS compilation failed: ";
      if (axios.isAxiosError(error)) {
        errorMessage += error.message;
      } else {
        errorMessage += error;
      }
      vscode.window.showErrorMessage(errorMessage);
      throw new Error(errorMessage);
    }
  }

  function showSvgInWebview(svgFilePath: string) {
    const panel = vscode.window.createWebviewPanel(
      "svgViewer",
      "TL-Verilog SVG Viewer",
      vscode.ViewColumn.Two,
      {
        enableScripts: true,
        retainContextWhenHidden: true,
      }
    );
  
    const svg = fs.readFileSync(svgFilePath, "utf8");
    const webviewContent = `
      <!DOCTYPE html>
      <html lang="en">
      <head>
        <meta charset="UTF-8">
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <title>TL-Verilog SVG Viewer</title>
      </head>
      <body>
        ${svg}
      </body>
      </html>
    `;
  
    panel.webview.html = webviewContent;
  }

  class SvgButton implements vscode.StatusBarItem {
    private statusBarItem: vscode.StatusBarItem;
  
    alignment: vscode.StatusBarAlignment;
    priority: number;
    text: string;
    tooltip: string;
    color: string;
    command: string | undefined;
  
    constructor(alignment: vscode.StatusBarAlignment = vscode.StatusBarAlignment.Left, priority: number = 1) {
      this.statusBarItem = vscode.window.createStatusBarItem(alignment, priority);
      this.statusBarItem.command = "extension.showSvg";
      this.statusBarItem.text = "$(file-media) SVG";
      this.statusBarItem.tooltip = "Generate and view TL-Verilog SVG diagram";
      this.text = "$(file-media) SVG";
      this.tooltip = "Generate and view TL-Verilog SVG diagram";
      this.alignment = alignment;
      this.priority = priority;
    }
  
    show() {
      this.statusBarItem.show();
    }
  
    hide() {
      this.statusBarItem.hide();
    }
  
    dispose() {
      this.statusBarItem.dispose();
    }
  }

  async function generateNavTlvHtml(tlvCode: string): Promise<string> {
    const externSettings =
      vscode.workspace.getConfiguration("tlverilog").get("formattingSettings") || [];
    const args = `-i test.tlv -o gene.sv --dhtml ${externSettings.join(" ")} --iArgs`;
  
    try {
      const response = await axios.post(
        "https://faas.makerchip.com/function/sandpiper-faas",
        JSON.stringify({
          args,
          responseType: "json",
          sv_url_inc: true,
          files: {
            "test.tlv": tlvCode,
          },
        }),
        {
          headers: {
            "Content-Type": "application/json",
          },
        }
      );
  
      if (response.status !== 200) {
        throw new Error(`SandPiper SaaS request failed with status ${response.status}`);
      }
  
      const data = response.data;
      if (data["out/test.m5out.html"]) {
        return data["out/test.m5out.html"];
      } else {
        throw new Error("SandPiper SaaS compilation failed: No HTML output generated.");
      }
    } catch (error) {
      let errorMessage = "SandPiper SaaS compilation failed: ";
      if (axios.isAxiosError(error)) {
        errorMessage += error.message;
      } else {
        errorMessage += error;
      }
      vscode.window.showErrorMessage(errorMessage);
      throw new Error(errorMessage);
    }
  }

  function showNavTlvInWebview(navTlvHtml: string,) {
    const panel = vscode.window.createWebviewPanel(
      "navTlvViewer",
      "Nav TLV Viewer",
      vscode.ViewColumn.Two,
      {
        enableScripts: true,
        retainContextWhenHidden: true,
      }
    );
  
    // Modify the HTML to include necessary styles and scripts for Nav TLV mode
    const modifiedHtml = `
      <!DOCTYPE html>
      <html lang="en">
      <head>
        <meta charset="UTF-8">
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <title>Nav TLV Viewer</title>
        <style>
          body { font-family: Arial, sans-serif; }
          .nav-tlv-content { white-space: pre; font-family: monospace; }
        </style>
      </head>
      <body>
        <div class="nav-tlv-content">${navTlvHtml}</div>
        <script>
          
        </script>
      </body>
      </html>
    `;
  
    panel.webview.html = modifiedHtml;
  }

  
  class NavTlvButton implements vscode.StatusBarItem {
    private statusBarItem: vscode.StatusBarItem;
  
    alignment: vscode.StatusBarAlignment;
    priority: number;
    text: string;
    tooltip: string;
    color: string;
    command: string | undefined;
  
    constructor(alignment: vscode.StatusBarAlignment = vscode.StatusBarAlignment.Left, priority: number = 3) {
      this.statusBarItem = vscode.window.createStatusBarItem(alignment, priority);
      this.statusBarItem.command = "extension.showNavTlv";
      this.statusBarItem.text = "$(list-tree) Nav TLV";
      this.statusBarItem.tooltip = "Open Nav TLV Viewer";
      this.text = "$(list-tree) Nav TLV";
      this.tooltip = "Open Nav TLV Viewer";
      this.alignment = alignment;
      this.priority = priority;
    }
  
    show() {
      this.statusBarItem.show();
    }
  
    hide() {
      this.statusBarItem.hide();
    }
  
    dispose() {
      this.statusBarItem.dispose();
    }
  }

  export function deactivate(sandpiperButton: SandPiperButton, svgButton: SvgButton , navTlvButton: NavTlvButton ) {
    if (sandpiperButton) {
      sandpiperButton.hide();
      sandpiperButton.dispose();
    }
  
    if (svgButton) {
      svgButton.hide();
      svgButton.dispose();
    }
    if (navTlvButton) {
      navTlvButton.hide();
      navTlvButton.dispose();
    }
  }

  class WaveformButton implements vscode.StatusBarItem {
    private statusBarItem: vscode.StatusBarItem;
  
    alignment: vscode.StatusBarAlignment;
    priority: number;
    text: string;
    tooltip: string;
    color: string;
    command: string | undefined;
  
    constructor(alignment: vscode.StatusBarAlignment = vscode.StatusBarAlignment.Left, priority: number = 2) {
      this.statusBarItem = vscode.window.createStatusBarItem(alignment, priority);
      this.statusBarItem.command = "extension.generateWaveform";
      this.statusBarItem.text = "$(pulse) Waveform";
      this.statusBarItem.tooltip = "Generate and view waveform";
      this.text = "$(pulse) Waveform";
      this.tooltip = "Generate and view waveform";
      this.alignment = alignment;
      this.priority = priority;
    }
  
    show() {
      this.statusBarItem.show();
    }
  
    hide() {
      this.statusBarItem.hide();
    }
  
    dispose() {
      this.statusBarItem.dispose();
    }
  }