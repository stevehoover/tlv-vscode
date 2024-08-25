# TL-Verilog support for VSCode

TL-Verilog support inspired by [SystemVerilog extension](https://github.com/mshr-h/vscode-systemverilog-support).

## How to use

* Install `TL-Verilog` extension (eq. search "tlv" in extensions tab)
* Reload VSCode (it will prompt you)
* Set color theme to `TLVerilgg` ( Cmd/Ctrl + Shift + P -> "color theme") for light theme, and `TL-Verilog Dark` for a dark mode.
* Open .tlv file
* Enjoy

## Features

### Upcoming

- tlv to sv/gen_sv Compilation: Utilize SandPiper SaaS to compile TL-Verilog code into SystemVerilog (sv) and generated SystemVerilog (gen_sv) files.
- SVG Diagram Generation: Generate and view SVG diagrams from your TL-Verilog code using SandPiper SaaS directly within the VS Code webviews.
- NavTLV Viewer: Generate NavTLV files via SandPiper SaaS and view them in a dedicated webview.
- VCD File Generation and Viewing: Convert Verilog code to VCD files using Verilator and view them in GTKWave.
- Dark Mode: Enjoy a new dark mode theme tailored for better readability and comfort during long coding sessions.
- Status Bar Integration: Quick access to all the new features through the status bar.


### Done

- Syntax highlighting for `.tlv` `.TLV` files

### Known bugs

- None so far
- Open the issue in one of the repos

## Git repos

- Personal, main: [dbogatov/TL-Verilog-VSCode](https://git.dbogatov.org/dbogatov/TL-Verilog-VSCode)
- GitHub, mirror: [Dima4ka/tlv-vscode](https://github.com/Dima4ka/tlv-vscode)

## Repository organization

This repository is organized as follows:

```
sytnaxes/                     syntax definition
snippets/                     code snippet
src/                          source code for custom feature
language-configuration.json   language configuration
package.json                  package configuration
LICENSE.txt                   license
README.md                     readme
```

## Contributing
1. Fork it ( [Dima4ka/tlv-vscode](https://github.com/Dima4ka/tlv-vscode) )
2. Create your feature branch (`git checkout -b my-new-feature`)
3. Commit your changes (`git commit -am 'Add some feature'`)
4. Push to the branch (`git push origin my-new-feature`)
5. Create a new Pull Request

## See also

[TL-Verilog](https://marketplace.visualstudio.com/items?itemName=Dmytro.TL-Verilog)

## License

[MIT](LICENSE)
