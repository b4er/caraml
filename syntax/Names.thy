theory Names
  imports Main
begin

section \<open>Names shared by the stages\<close>

text \<open>Flat names, their mangling, and the reserved keys that the checker and
  the elaborator share.\<close>

type_synonym name = \<open>nat list\<close>  \<comment> \<open>codepoints\<close>

abbreviation str :: \<open>string \<Rightarrow> name\<close> where
  \<open>str \<equiv> map of_char\<close>

text \<open>Tuples are not primitive: they are constructor applications of the
  reserved names \<open>()\<close>, \<open>(,)\<close>, \<open>(,,)\<close> etc.\<close>

definition tuple_con :: \<open>nat \<Rightarrow> name\<close> where
  \<open>tuple_con n = str ''('' @ replicate (n - 1) 0x2C @ str '')''\<close>

definition mangle :: \<open>name \<Rightarrow> name \<Rightarrow> name\<close> where
  \<open>mangle p x = (if p = [] then x else p @ str ''.'' @ x)\<close>

text \<open>An operator's fixity lives under a \<open>%fix.\<close> key:\<close>

definition fix_key :: \<open>name \<Rightarrow> name\<close> where
  \<open>fix_key opr = str ''%fix.'' @ opr\<close>

subsection \<open>Fixity resolution\<close>

text \<open>Operator chains are parsed flat and resolved by Dijkstra's shunting-yard
  \<^cite>\<open>dijkstra1961\<close> with the associativity test of Haskell: at equal precedence,
  differing or non-associative fixities are rejected
  \<^cite>\<open>\<open>Sect. 10.6\<close> in marlow2010\<close> (and \<^cite>\<open>\<open>Sect. 2.6\<close> in milner1997\<close>).
  The node builder is a parameter, so the checker and the elaborator run the same
  function.\<close>

datatype fixity = FixL | FixR | FixN

datatype obld = OCon name | OVar name  \<comment> \<open>an operator's meaning\<close>

fun unwind :: \<open>(obld \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<times> obld \<times> fixity \<times> nat) list \<Rightarrow> 'a \<Rightarrow> 'a\<close> where
  \<open>unwind mk [] r = r\<close>
| \<open>unwind mk ((l, b, f, p) # stk) r = unwind mk stk (mk b l r)\<close>

fun shunt :: \<open>(obld \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<times> obld \<times> fixity \<times> nat) list \<Rightarrow> 'a
              \<Rightarrow> ((obld \<times> fixity \<times> nat) \<times> 'a) list \<Rightarrow> 'a option\<close> where
  \<open>shunt mk stk l [] = Some (unwind mk stk l)\<close>
| \<open>shunt mk [] l (((b\<^sub>2, f\<^sub>2, p\<^sub>2), r) # rest) = shunt mk [(l, b\<^sub>2, f\<^sub>2, p\<^sub>2)] r rest\<close>
| \<open>shunt mk ((l\<^sub>1, b\<^sub>1, f\<^sub>1, p\<^sub>1) # stk) l (((b\<^sub>2, f\<^sub>2, p\<^sub>2), r) # rest) =
     (if p\<^sub>1 > p\<^sub>2 \<or> (p\<^sub>1 = p\<^sub>2 \<and> f\<^sub>1 = FixL \<and> f\<^sub>2 = FixL)
      then shunt mk stk (mk b\<^sub>1 l\<^sub>1 l) (((b\<^sub>2, f\<^sub>2, p\<^sub>2), r) # rest)
      else if p\<^sub>2 > p\<^sub>1 \<or> (p\<^sub>1 = p\<^sub>2 \<and> f\<^sub>1 = FixR \<and> f\<^sub>2 = FixR)
      then shunt mk ((l, b\<^sub>2, f\<^sub>2, p\<^sub>2) # (l\<^sub>1, b\<^sub>1, f\<^sub>1, p\<^sub>1) # stk) r rest
      else None)\<close>

text \<open>Whether a chain resolves depends only on its fixities, not on the
  leaves: the two stages run \<^const>\<open>shunt\<close> over different leaf types and
  the elaborator succeeds exactly where the checker did.\<close>

lemma shunt_map:
  assumes \<open>\<And>b x y. mk' b (g x) (g y) = g (mk b x y)\<close>
  shows \<open>shunt mk' (map (\<lambda>(l, b, f, p). (g l, b, f, p)) stk) (g l) (map (apsnd g) ops)
         = map_option g (shunt mk stk l ops)\<close>
proof -
  have \<open>unwind mk' (map (\<lambda>(l, b, f, p). (g l, b, f, p)) stk) (g l) = g (unwind mk stk l)\<close>
    for stk l
    by (induction stk arbitrary: l) (auto simp: assms)
  then show ?thesis
    using assms by (induction mk stk l ops rule: shunt.induct) auto
qed

end
