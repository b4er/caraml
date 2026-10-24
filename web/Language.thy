theory Language
  imports CaraML_Site
begin

page (part: docs, order: 20, optional: 55) \<open>Language\<close>

text \<open>
  A tour of the language, one construct at a time, each by a program.
\<close>

section \<open>Values, functions and types\<close>

\<comment> \<open>FIXME: declarations, main, datatypes and patterns, guards, layout\<close>

section \<open>Effects in the type\<close>

\<comment> \<open>FIXME: effect rows on arrows, divergence as an effect, a pure type is total\<close>

section \<open>Effects and handlers\<close>

\<comment> \<open>FIXME: effect declarations, handlers, the resumption as a value, multi-shot\<close>

section \<open>Named handlers\<close>

\<comment> \<open>FIXME: with f = handler ..., f.op\<close>

section \<open>Modules and implicits\<close>

\<comment> \<open>FIXME: signatures, functors, sealing, instances, implicit arguments\<close>

section \<open>Recursion schemes\<close>

\<comment> \<open>FIXME: the derived Fold instance per type\<close>

section \<open>The foreign interface\<close>

\<comment> \<open>FIXME: extern, the symbol, the foreign boundary as an effect\<close>

end
