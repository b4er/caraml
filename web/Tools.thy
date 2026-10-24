theory Tools
  imports CaraML_Site
begin

page (part: docs, order: 10) \<open>Tools\<close>

text \<open>
  Everything is a single executable, \<^verbatim>\<open>caraml\<close>, with one subcommand per tool:
  every subcommand takes \<^verbatim>\<open>-v\<close> and \<^verbatim>\<open>-q\<close> (repeatable) for more or less log output,
  and \<^verbatim>\<open>--json\<close> for machine-readable diagnostics as global options.
\<close>

section \<open>caraml build\<close>

\<comment> \<open>build DIR: --lock, --offline, --package-path, --cache, --exe, --emit\<close>

section \<open>caraml compile\<close>

\<comment> \<open>compile FILE...: --target (x64, wasm), -o, --emit (surface, core, anf, flat);
  one file to one module, separate compilation\<close>

section \<open>caraml fmt\<close>

\<comment> \<open>fmt FILE...: in place, --check, --stdin\<close>

section \<open>caraml lsp\<close>

\<comment> \<open>what the server offers: diagnostics, hover with type and effect row,
  go to definition; spans count codepoints\<close>

end
