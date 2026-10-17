theory Named_Cases
  imports Main
begin

section \<open>Stable case names for \<^theory_text>\<open>fun\<close> and \<^theory_text>\<open>function\<close>\<close>

text \<open>How \<^file>\<open>named_cases.ML\<close> derives the names:
  \<^item> A case's name lists, argument by argument and the constructors in which its
    patterns differ from the other cases' patterns. A constructor that all the
    patterns have at a place adds nothing, nor does a tuple.
  \<^item> Each case then drops the arguments its name does not need, as long as the
    name stays nonempty and differs from the other cases' names.
  \<^item> Names that still clash keep all arguments, with \<open>any\<close> for a variable
    one: the package splits the catch-all clause of
    \<open>zip2 (x # xs) (y # ys) | zip2 _ _\<close> into two cases, named \<open>Nil_any\<close>
    and \<open>any_Nil\<close>. Names that clash even then are numbered.
  \<^item> The cases of a mutual group are prefixed with the name of the function they
    belong to; those of a single function carry no prefix.\<close>

ML_file \<open>named_cases.ML\<close>

text \<open>Usage, once after the definition, with the name of the function (of any
  one function of a mutual group):

  \<^theory_text>\<open>lemmas ceval_induct = ceval_cevcon_\<dots>.induct[named_cases ceval]\<close>.\<close>

end
