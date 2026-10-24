theory Language_Report
  imports CaraML_Site
begin

page (part: report, order: 10) \<open>Language report\<close>

text \<open>
  The definition of CaraML: its syntax, its static and dynamic semantics, and the
  elaboration between them, rendered from the Isabelle/HOL theories that specify them.
\<close>

section \<open>Overview\<close>

\<comment> \<open>the chain read, infer, elaborate, evaluate; what is proved of each step and what
  is open\<close>

section \<open>Syntax\<close>

\<comment> \<open>names, the abstract syntax (CaraML_Syntax), the surface grammar and layout
  (parser/grammar.md, CaraML_Parser)\<close>

section \<open>Static semantics\<close>

\<comment> \<open>types and effect rows, the basis, the typing rules, inference and its soundness
  (CaraML_Typing)\<close>

section \<open>Elaboration\<close>

\<comment> \<open>static interpretation of modules, implicit resolution, desugaring to core\<close>

section \<open>Dynamic semantics\<close>

\<comment> \<open>the core language, its big-step semantics, handlers and the foreign boundary
  (CaraML_Core)\<close>

end
