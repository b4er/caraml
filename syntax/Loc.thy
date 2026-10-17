theory Loc
  imports Main
begin

section \<open>Source locations\<close>

text \<open>The AST's source locations; the parser session converts the lexer's
  \<^text>\<open>Token.span\<close> with \<^text>\<open>loc_of_span\<close>. Columns, offsets and lengths count
  codepoints.\<close>

record loc =
  l_line :: nat
  l_col  :: nat
  l_off  :: nat
  l_len  :: nat

text \<open>The span of a composite node, from its first child to its last.\<close>

definition loc_join :: \<open>'a loc_scheme \<Rightarrow> 'b loc_scheme \<Rightarrow> loc\<close> where
  \<open>loc_join a b = \<lparr> l_line = l_line a, l_col = l_col a, l_off = l_off a,
                    l_len = l_off b + l_len b - l_off a \<rparr>\<close>

definition loc_end :: \<open>'a loc_scheme \<Rightarrow> nat\<close> where
  \<open>loc_end l = l_off l + l_len l\<close>

lemma loc_join_off [simp]: \<open>l_off (loc_join a b) = l_off a\<close>
  and loc_join_line [simp]: \<open>l_line (loc_join a b) = l_line a\<close>
  and loc_join_col [simp]: \<open>l_col (loc_join a b) = l_col a\<close>
  by (simp_all add: loc_join_def)

lemma loc_join_end: \<open>l_off a \<le> loc_end b \<Longrightarrow> loc_end (loc_join a b) = loc_end b\<close>
  by (simp add: loc_join_def loc_end_def)

text \<open>A name: a location plus its spelling.\<close>

record nm = loc +
  n_txt :: \<open>nat list\<close>

definition no_loc :: loc where
  \<open>no_loc = \<lparr> l_line = 0, l_col = 0, l_off = 0, l_len = 0 \<rparr>\<close>

end
