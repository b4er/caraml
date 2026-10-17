theory Named_Cases_Test
  imports CaraML_Prelude.Named_Cases
begin

section \<open>Tests of the attribute \<open>named_cases\<close>\<close>

text \<open>Each test compares the names derived by \<open>named_cases\<close> with the expected ones:\<close>

ML \<open>
  fun check_cases th expected =
    let val names = map (fst o fst) (fst (Rule_Cases.get th))
    in
      if names = expected then ()
      else error ("case names " ^ commas_quote names ^ ", expected " ^ commas_quote expected)
    end
\<close>

subsection \<open>Constructors at the top\<close>

fun len :: \<open>'a list \<Rightarrow> nat\<close> where
  \<open>len [] = 0\<close>
| \<open>len (x # xs) = Suc (len xs)\<close>

lemmas len_induct = len.induct[named_cases len]
lemmas len_cases = len.cases[named_cases len]

ML \<open>
  check_cases @{thm len.induct} ["1", "2"];
  check_cases @{thm len_induct} ["Nil", "Cons"];
  check_cases @{thm len_cases} ["Nil", "Cons"]
\<close>

text \<open>The names are those of \<^theory_text>\<open>induction\<close> and \<^theory_text>\<open>cases\<close>.\<close>

lemma len_eq_length: \<open>len xs = length xs\<close>
proof (induction xs rule: len_induct)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by simp
qed

lemma \<open>len xs = 0 \<or> 0 < len xs\<close>
proof (cases xs rule: len_cases)
  case Nil
  then show ?thesis by simp
next
  case (Cons y ys)
  then show ?thesis by simp
qed

subsection \<open>Nested constructors\<close>

text \<open>Patterns that share a constructor are told apart by its arguments; a
  constructor that all patterns share adds nothing (here \<^const>\<open>Suc\<close> in the
  two last equations).\<close>

fun fib :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>fib 0 = 0\<close>
| \<open>fib (Suc 0) = 1\<close>
| \<open>fib (Suc (Suc n)) = fib n + fib (Suc n)\<close>

ML \<open>check_cases @{thm fib.induct[named_cases fib]} ["0", "Suc_0", "Suc_Suc"]\<close>

datatype t = A nat | B t t | C

fun depth :: \<open>t \<Rightarrow> nat\<close> where
  \<open>depth (B (A n) u) = n\<close>
| \<open>depth (B (B s u) v) = depth s\<close>
| \<open>depth (B C v) = depth v\<close>
| \<open>depth _ = 0\<close>

text \<open>The catch-all clause of \<^const>\<open>depth\<close> is split by the package into
  the constructors that the clauses before it leave out: they become the cases
  \<open>A\<close> and \<open>C\<close>, where the package numbers \<open>4_1\<close> and \<open>4_2\<close>.\<close>

ML \<open>
  check_cases @{thm depth.induct} ["1", "2", "3", "4_1", "4_2"];
  check_cases @{thm depth.induct[named_cases depth]} ["B_A", "B_B", "B_C", "A", "C"]
\<close>

subsection \<open>The names survive a new constructor\<close>

fun size_t :: \<open>t \<Rightarrow> nat\<close> where
  \<open>size_t (A n) = n\<close>
| \<open>size_t (B s u) = size_t s + size_t u\<close>
| \<open>size_t C = 0\<close>

datatype t' = A' nat | D' | B' t' t' | C'

fun size' :: \<open>t' \<Rightarrow> nat\<close> where
  \<open>size' (A' n) = n\<close>
| \<open>size' D' = 1\<close>
| \<open>size' (B' s u) = size' s + size' u\<close>
| \<open>size' C' = 0\<close>

ML \<open>
  check_cases @{thm size_t.induct} ["1", "2", "3"];
  check_cases @{thm size'.induct} ["1", "2", "3", "4"];
  check_cases @{thm size_t.induct[named_cases size_t]} ["A", "B", "C"];
  check_cases @{thm size'.induct[named_cases size']} ["A'", "D'", "B'", "C'"]
\<close>

subsection \<open>Several arguments\<close>

fun add_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>add_nat 0 m = m\<close>
| \<open>add_nat (Suc n) m = Suc (add_nat n m)\<close>

fun zip2 :: \<open>'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list\<close> where
  \<open>zip2 (x # xs) (y # ys) = (x, y) # zip2 xs ys\<close>
| \<open>zip2 _ _ = []\<close>

text \<open>An argument position that no case needs is left out of all names (the
  second argument of \<^const>\<open>add_nat\<close>). When names would clash without a
  position, the clashing cases keep all positions, with \<open>any\<close> for a variable
  one: the catch-all clause of \<^const>\<open>zip2\<close> is split into \<open>[] _\<close> and
  \<open>(_ # _) []\<close>.\<close>

ML \<open>
  check_cases @{thm add_nat.induct[named_cases add_nat]} ["0", "Suc"];
  check_cases @{thm zip2.induct} ["1", "2_1", "2_2"];
  check_cases @{thm zip2.induct[named_cases zip2]} ["Cons", "Nil_any", "any_Nil"]
\<close>

text \<open>A tuple argument counts as its components: \<^const>\<open>Pair\<close> is shared by
  all patterns.\<close>

fun add_pair :: \<open>nat \<times> nat \<Rightarrow> nat\<close> where
  \<open>add_pair (0, m) = m\<close>
| \<open>add_pair (Suc n, m) = Suc (add_pair (n, m))\<close>

ML \<open>check_cases @{thm add_pair.induct[named_cases add_pair]} ["0", "Suc"]\<close>

text \<open>A tuple never names a case, also where other patterns have a variable:\<close>

fun pick :: \<open>nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat\<close> where
  \<open>pick 0 (n, m) = n\<close>
| \<open>pick (Suc k) p = pick k p\<close>

ML \<open>check_cases @{thm pick.induct[named_cases pick]} ["0", "Suc"]\<close>

subsection \<open>Mutual groups\<close>

text \<open>Given one function of a mutual group, the attribute prefixes each case
  with the name of its function; given several names, it uses them as the
  prefixes, in the order of the group. The group's induction rule is one rule per
  function, all with the same cases.\<close>

fun ev :: \<open>nat \<Rightarrow> bool\<close> and od :: \<open>nat \<Rightarrow> bool\<close> where
  \<open>ev 0 = True\<close>
| \<open>ev (Suc n) = od n\<close>
| \<open>od 0 = False\<close>
| \<open>od (Suc n) = ev n\<close>

ML \<open>
  List.app (fn th => check_cases th ["ev_0", "ev_Suc", "od_0", "od_Suc"])
    @{thms ev_od.induct[named_cases ev]};
  List.app (fn th => check_cases th ["e_0", "e_Suc", "o_0", "o_Suc"])
    @{thms ev_od.induct[named_cases e o]}
\<close>

text \<open>The prefixes follow the declaration of the functions, not the order of
  their equations, which is the order of the cases.\<close>

fun ev' :: \<open>nat \<Rightarrow> bool\<close> and od' :: \<open>nat \<Rightarrow> bool\<close> where
  \<open>od' 0 = False\<close>
| \<open>ev' 0 = True\<close>
| \<open>od' (Suc n) = ev' n\<close>
| \<open>ev' (Suc n) = od' n\<close>

ML \<open>
  List.app (fn th => check_cases th ["od'_0", "ev'_0", "od'_Suc", "ev'_Suc"])
    @{thms ev'_od'.induct[named_cases ev']}
\<close>

subsection \<open>\<^theory_text>\<open>function\<close> and conditional equations\<close>

function sub :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>sub 0 m = 0\<close>
| \<open>sub (Suc n) 0 = Suc n\<close>
| \<open>sub (Suc n) (Suc m) = sub n m\<close>
  by pat_completeness auto
termination by lexicographic_order

text \<open>Each case drops the positions its name does not need: the last case of
  \<^const>\<open>sub\<close> is told apart by its first argument from the first case and by
  its second from the second, but after the first case has kept \<open>0\<close> and the
  second \<open>Suc_0\<close>, the name \<open>Suc\<close> is free.\<close>

ML \<open>check_cases @{thm sub.induct[named_cases sub]} ["0", "Suc_0", "Suc"]\<close>

text \<open>Equations that only their conditions tell apart have no constructor to be
  named after: they are numbered.\<close>

function pos :: \<open>int \<Rightarrow> int\<close> where
  \<open>pos i = 1\<close> if \<open>i > 0\<close>
| \<open>pos i = 0\<close> if \<open>i \<le> 0\<close>
  by atomize_elim auto
termination by lexicographic_order

ML \<open>check_cases @{thm pos.induct[named_cases pos]} ["any_1", "any_2"]\<close>

end
