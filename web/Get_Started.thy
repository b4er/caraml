theory Get_Started
  imports CaraML_Site
begin

page (part: start, order: 10, optional: 55) \<open>Get started\<close>

text \<open>
  CaraML is one program, \<^verbatim>\<open>caraml\<close>: the compiler, the build tool, the formatter and language server.
  This page helps you install it, check that your editor talks to it and compile a first program.
\<close>

section \<open>Install\<close>

div (id: "editors", picker) \<open>
  div (option, label: "VS Code / VSCodium") \<open>
    text \<open>Install the extension \<^verbatim>\<open>b4er.caraml\<close> from either registry:\<close>
    html \<open><ul>
  <li><a href="https://marketplace.visualstudio.com/items?itemName=b4er.caraml">Visual Studio Marketplace</a> (VS Code)</li>
  <li><a href="https://open-vsx.org/extension/b4er/caraml">Open VSX Registry</a> (VSCodium)</li>
</ul>\<close>
  \<close>

  div (option, label: "Emacs") \<open>
    text \<open>Requires Emacs 30 or later. In \<^verbatim>\<open>init.el\<close>:\<close>
    pre (code, elisp) \<open>(use-package caraml-mode
  :vc (:url "https://github.com/b4er/caraml"
       :lisp-dir "editors/emacs/local/caraml-mode")
  :hook (caraml-mode . caraml-eglot-ensure))\<close>
  \<close>

  div (option, label: "Spacemacs") \<open>
    text \<open>In \<^verbatim>\<open>~/.spacemacs\<close>, fetch the mode from git in
      \<^verbatim>\<open>dotspacemacs-additional-packages\<close>:\<close>
    pre (code, elisp) \<open>(caraml-mode :location (recipe :fetcher github :repo "b4er/caraml"
                               :files ("editors/emacs/local/caraml-mode/*.el")))\<close>
    text \<open>and start the language server in \<^verbatim>\<open>dotspacemacs/user-config\<close>:\<close>
    pre (code, elisp) \<open>(add-hook 'caraml-mode-hook #'caraml-eglot-ensure)\<close>
  \<close>

  div (option, label: "Command line") \<open>
    text \<open>Without an editor plugin, download a pre-built \<^verbatim>\<open>caraml\<close> into \<^verbatim>\<open>~/.local/bin\<close>; pick
      \<^verbatim>\<open>linux-x64\<close>, \<^verbatim>\<open>linux-arm64\<close>, or \<^verbatim>\<open>darwin-arm64\<close> (Windows users take
      \<^verbatim>\<open>caraml-win32-x64.tar.gz\<close>, which holds \<^verbatim>\<open>caraml.exe\<close>):\<close>
    pre (code, shell) \<open>curl -fsSL https://caraml-lang.org/releases/latest/caraml-linux-x64.tar.gz | tar -xz -C ~/.local/bin ./caraml\<close>
    text \<open>Or build and install it from source with Cabal:\<close>
    pre (code, shell) \<open>curl -fsSL https://caraml-lang.org/releases/latest/caraml-src.tar.gz | tar -xz
cd caraml-*/ && cabal install exe:caraml\<close>
    text \<open>Replace \<^verbatim>\<open>latest\<close> by a version such as \<^verbatim>\<open>v0.1.0\<close> to pin a release.\<close>
    text \<open>Any editor with a language client can then run \<^verbatim>\<open>caraml lsp\<close>, which serves the
      Language Server Protocol on stdin and stdout.\<close>
  \<close>
\<close>

text \<open>
  Open any \<^verbatim>\<open>.caraml\<close> file, when the plugin finds no \<^verbatim>\<open>caraml\<close> executable, it offers to set one up:

  \<^item> \<^bold>\<open>Download\<close> a pre-built binary from the latest release (Linux on x86-64 and ARM,
    macOS on Apple silicon, Windows on x86-64).
  \<^item> \<^bold>\<open>Build from source\<close> with Cabal, which needs \<^verbatim>\<open>cabal\<close> 3 or later and \<^verbatim>\<open>ghc\<close> on your \<^verbatim>\<open>PATH\<close> and
    takes several minutes.
  \<^item> \<^bold>\<open>Locate\<close> a \<^verbatim>\<open>caraml\<close> you already have.
  
  A download or a build installs into \<^verbatim>\<open>~/.local/bin\<close> (or \<^verbatim>\<open>$XDG_BIN_HOME\<close>). If that directory is
  not on your \<^verbatim>\<open>PATH\<close>, add it to run \<^verbatim>\<open>caraml\<close> from a shell.
\<close>

text \<open>Check the installation from a shell:\<close>

pre (code, shell) \<open>caraml --version\<close>

section \<open>Check your editor\<close>

text \<open>Create a file \<^verbatim>\<open>hello.caraml\<close>:\<close>

caraml \<open>main = putStr 42\<close>

text \<open>
  The editor underlines \<open>42\<close>: \<open>putStr\<close> takes a \<open>string\<close>, not an \<open>int\<close>. Hover over \<open>putStr\<close> to see
  its type. If neither happens, the editor has not started the language server (the plugin's log
  should say why).
\<close>

section \<open>A first program\<close>

text \<open>Fix the argument:\<close>

caraml \<open>main = putStr "Hello, World!"\<close>

pre (code, shell) \<open>caraml compile hello.caraml\<close>

section \<open>A first project\<close>

text \<open>
  A project is a directory with a manifest (\<^verbatim>\<open>project.caraml\<close>) which is itself a CaraML module. It
  names the package, its dependencies and its executables, each a binary name and a root module:
\<close>

caraml \<open>name = "hello"
version = "0.1.0"
dependencies = []
sources = []
library = None
executables = [("hello", "Main")]\<close>

text \<open>
  Move \<^verbatim>\<open>hello.caraml\<close> to \<^verbatim>\<open>Main.caraml\<close> next to it and build:
\<close>

pre (code, shell) \<open>caraml build\<close>

text \<open>
  \<^verbatim>\<open>caraml build\<close> resolves the dependencies, records them in
  \<^verbatim>\<open>project.lock\<close> and checks every module. The section \<^url>\<open>Tools\<close>
  describes the manifest and every command in more detail.
\<close>

section \<open>Where next?\<close>

text \<open>
  \<^item> \<^url>\<open>Language\<close> is an informal tour of the language: introducing the main concepts of CaraML.
  \<^item> \<^url>\<open>Prelude\<close> lists what every program starts with: the standard library of CaraML.
  \<^item> \<^url>\<open>Language_Report\<close> specifies the language and compiler formally.
  \<^item> \<^url>\<open>Compiler\<close> describes the verified compiler.
\<close>

end
