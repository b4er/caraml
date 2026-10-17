theory Protocol
  imports
    "Regular-Sets.Equivalence_Checking"
    "Regular-Sets.Derivatives"
    "HOL-Library.List_Lexorder"
    "HOL-Library.Product_Lexorder"
    Names
begin

section \<open>Protocols: linear temporal formulas over an effect's operations\<close>

text \<open>A protocol constrains the operations performed on one handler instance
  during its extent (the instance is named as in \<^cite>\<open>\<open>Sect. 2.3\<close> in xie2021names\<close>).
  Formulas are LTL over finite traces \<^cite>\<open>degiacomo2013\<close> in negation normal form, with the
  regular-prefix modalities \<open>[r]\<phi>\<close> (\<open>SImp\<close>) and \<open>\<langle>r\<rangle>\<phi>\<close> (\<open>SConj\<close>) of LDLf. Atoms
  are first-order (\<open>Prop as\<close>: the next operation is one of \<open>as\<close>), so formulas have
  decidable equality and the derivative closure below is computable.\<close>

notation Regular_Exp.Times (infixr \<open>~~\<close> 60)

datatype 'a ltlf =
    Ff | Tt
  | Prop \<open>'a list\<close>              \<comment> \<open>the next operation is one of these\<close>
  | NProp \<open>'a list\<close>             \<comment> \<open>the next operation, if any, is none of these\<close>
  | And \<open>'a ltlf\<close> \<open>'a ltlf\<close>
  | Or \<open>'a ltlf\<close> \<open>'a ltlf\<close>
  | Next \<open>'a ltlf\<close>                \<comment> \<open>strong next: fails at trace end\<close>
  | WNext \<open>'a ltlf\<close>               \<comment> \<open>weak next: holds at trace end\<close>
  | Until \<open>'a ltlf\<close> \<open>'a ltlf\<close>
  | Release \<open>'a ltlf\<close> \<open>'a ltlf\<close>
  | SImp \<open>'a rexp\<close> \<open>'a ltlf\<close>   \<comment> \<open>every prefix in \<open>r\<close> is followed by \<open>\<phi>\<close>\<close>
  | SConj \<open>'a rexp\<close> \<open>'a ltlf\<close>  \<comment> \<open>some prefix in \<open>r\<close> is followed by \<open>\<phi>\<close>\<close>

abbreviation Fin where \<open>Fin \<phi> \<equiv> Until Tt \<phi>\<close>
abbreviation Glob where \<open>Glob \<phi> \<equiv> Release Ff \<phi>\<close>
abbreviation WUntil where \<open>WUntil \<phi> \<psi> \<equiv> Or (Until \<phi> \<psi>) (Glob \<phi>)\<close>

text \<open>Semantics over possibly empty traces. \<open>Prop\<close>, \<open>NProp\<close>, \<open>Next\<close> and \<open>WNext\<close> look
  at the head of the trace; at its end \<open>Prop\<close>/\<open>Next\<close> fail and their duals \<open>NProp\<close>/\<open>WNext\<close>
  hold, so that negation is definable by duality (\<open>sat_neg\<close> below):\<close>

fun sat where
  \<open>sat _ Ff \<longleftrightarrow> False\<close>
| \<open>sat _ Tt \<longleftrightarrow> True\<close>
| \<open>sat [] (Prop as) \<longleftrightarrow> False\<close>
| \<open>sat (a # w) (Prop as) \<longleftrightarrow> a \<in> set as\<close>
| \<open>sat [] (NProp as) \<longleftrightarrow> True\<close>
| \<open>sat (a # w) (NProp as) \<longleftrightarrow> a \<notin> set as\<close>
| \<open>sat w (And \<phi> \<psi>) \<longleftrightarrow> sat w \<phi> \<and> sat w \<psi>\<close>
| \<open>sat w (Or \<phi> \<psi>) \<longleftrightarrow> sat w \<phi> \<or> sat w \<psi>\<close>
| \<open>sat [] (Next \<phi>) \<longleftrightarrow> False\<close>
| \<open>sat (a # w) (Next \<phi>) \<longleftrightarrow> sat w \<phi>\<close>
| \<open>sat [] (WNext \<phi>) \<longleftrightarrow> True\<close>
| \<open>sat (a # w) (WNext \<phi>) \<longleftrightarrow> sat w \<phi>\<close>
| sat_Until: \<open>sat w (Until \<phi> \<psi>) \<longleftrightarrow>
     (\<exists>i \<le> length w. sat (drop i w) \<psi> \<and> (\<forall>j<i. sat (drop j w) \<phi>))\<close>
| sat_Release: \<open>sat w (Release \<phi> \<psi>) \<longleftrightarrow>
     (\<forall>i \<le> length w. sat (drop i w) \<psi> \<or> (\<exists>j<i. sat (drop j w) \<phi>))\<close>
| sat_SImp: \<open>sat w (SImp r \<phi>) \<longleftrightarrow> (\<forall>u v. w = u @ v \<longrightarrow> u \<in> lang r \<longrightarrow> sat v \<phi>)\<close>
| sat_SConj: \<open>sat w (SConj r \<phi>) \<longleftrightarrow> (\<exists>u v. w = u @ v \<and> u \<in> lang r \<and> sat v \<phi>)\<close>

primrec neg where
  \<open>neg Ff = Tt\<close>
| \<open>neg Tt = Ff\<close>
| \<open>neg (Prop as) = NProp as\<close>
| \<open>neg (NProp as) = Prop as\<close>
| \<open>neg (And \<phi> \<psi>) = Or (neg \<phi>) (neg \<psi>)\<close>
| \<open>neg (Or \<phi> \<psi>) = And (neg \<phi>) (neg \<psi>)\<close>
| \<open>neg (Next \<phi>) = WNext (neg \<phi>)\<close>
| \<open>neg (WNext \<phi>) = Next (neg \<phi>)\<close>
| \<open>neg (Until \<phi> \<psi>) = Release (neg \<phi>) (neg \<psi>)\<close>
| \<open>neg (Release \<phi> \<psi>) = Until (neg \<phi>) (neg \<psi>)\<close>
| \<open>neg (SImp r \<phi>) = SConj r (neg \<phi>)\<close>
| \<open>neg (SConj r \<phi>) = SImp r (neg \<phi>)\<close>

lemma sat_neg[simp]: \<open>sat w (neg \<phi>) \<longleftrightarrow> \<not> sat w \<phi>\<close>
  by (induction \<phi> arbitrary: w) (auto elim: sat.elims split: list.splits)

section \<open>Derivatives\<close>

text \<open>Brzozowski-style derivatives \<^cite>\<open>brzozowski1964\<close>: \<open>fnull \<phi>\<close> decides the empty
  trace, and \<open>fderiv a \<phi>\<close> is what the rest of the trace must satisfy after the operation
  \<open>a\<close>. The \<open>Until\<close>/\<open>Release\<close> clauses are the LTL expansion laws; the \<open>SImp\<close>/\<open>SConj\<close>
  clauses step the regular expression with \<^const>\<open>Derivatives.deriv\<close>. This is the \<open>\<delta>\<close> of
  the alternating automaton of \<^cite>\<open>\<open>Sect. 6\<close> in degiacomo2013\<close>, read as a formula
  rewrite. A named handler's frame keeps the residual of its protocol, and the handler
  is stuck when the residual is \<open>Ff\<close>.\<close>

primrec fnull :: \<open>'a ltlf \<Rightarrow> bool\<close> where
  \<open>fnull Ff \<longleftrightarrow> False\<close>
| \<open>fnull Tt \<longleftrightarrow> True\<close>
| \<open>fnull (Prop as) \<longleftrightarrow> False\<close>
| \<open>fnull (NProp as) \<longleftrightarrow> True\<close>
| \<open>fnull (And \<phi> \<psi>) \<longleftrightarrow> fnull \<phi> \<and> fnull \<psi>\<close>
| \<open>fnull (Or \<phi> \<psi>) \<longleftrightarrow> fnull \<phi> \<or> fnull \<psi>\<close>
| \<open>fnull (Next \<phi>) \<longleftrightarrow> False\<close>
| \<open>fnull (WNext \<phi>) \<longleftrightarrow> True\<close>
| \<open>fnull (Until \<phi> \<psi>) \<longleftrightarrow> fnull \<psi>\<close>
| \<open>fnull (Release \<phi> \<psi>) \<longleftrightarrow> fnull \<psi>\<close>
| \<open>fnull (SImp r \<phi>) \<longleftrightarrow> nullable r \<longrightarrow> fnull \<phi>\<close>
| \<open>fnull (SConj r \<phi>) \<longleftrightarrow> nullable r \<and> fnull \<phi>\<close>

primrec fderiv :: \<open>'a \<Rightarrow> 'a ltlf \<Rightarrow> 'a ltlf\<close> where
  \<open>fderiv a Ff = Ff\<close>
| \<open>fderiv a Tt = Tt\<close>
| \<open>fderiv a (Prop as) = (if a \<in> set as then Tt else Ff)\<close>
| \<open>fderiv a (NProp as) = (if a \<in> set as then Ff else Tt)\<close>
| \<open>fderiv a (And \<phi> \<psi>) = And (fderiv a \<phi>) (fderiv a \<psi>)\<close>
| \<open>fderiv a (Or \<phi> \<psi>) = Or (fderiv a \<phi>) (fderiv a \<psi>)\<close>
| \<open>fderiv a (Next \<phi>) = \<phi>\<close>
| \<open>fderiv a (WNext \<phi>) = \<phi>\<close>
| \<open>fderiv a (Until \<phi> \<psi>) = Or (fderiv a \<psi>) (And (fderiv a \<phi>) (Until \<phi> \<psi>))\<close>
| \<open>fderiv a (Release \<phi> \<psi>) = And (fderiv a \<psi>) (Or (fderiv a \<phi>) (Release \<phi> \<psi>))\<close>
| \<open>fderiv a (SImp r \<phi>) = And (if nullable r then fderiv a \<phi> else Tt) (SImp (deriv a r) \<phi>)\<close>
| \<open>fderiv a (SConj r \<phi>) = Or (if nullable r then fderiv a \<phi> else Ff) (SConj (deriv a r) \<phi>)\<close>

lemma ex_le_Suc_iff: \<open>(\<exists>i \<le> Suc n. P i) \<longleftrightarrow> P 0 \<or> (\<exists>i \<le> n. P (Suc i))\<close>
  by (metis Suc_le_mono not0_implies_Suc zero_le)

lemma all_le_Suc_iff: \<open>(\<forall>i \<le> Suc n. P i) \<longleftrightarrow> P 0 \<and> (\<forall>i \<le> n. P (Suc i))\<close>
  by (metis Suc_le_mono not0_implies_Suc zero_le)

lemma sat_U_Cons:
  \<open>sat (a # w) (Until \<phi> \<psi>) \<longleftrightarrow> sat (a # w) \<psi> \<or> sat (a # w) \<phi> \<and> sat w (Until \<phi> \<psi>)\<close>
  by (simp only: ex_le_Suc_iff All_less_Suc2 sat.simps drop_Suc_Cons drop_0 length_Cons) blast

lemma sat_R_Cons:
  \<open>sat (a # w) (Release \<phi> \<psi>) \<longleftrightarrow> sat (a # w) \<psi> \<and> (sat (a # w) \<phi> \<or> sat w (Release \<phi> \<psi>))\<close>
  by (simp only: all_le_Suc_iff Ex_less_Suc2 sat.simps drop_Suc_Cons drop_0 length_Cons) blast

lemma sat_SImp_Cons:
  \<open>sat (a # w) (SImp r \<phi>) \<longleftrightarrow> (nullable r \<longrightarrow> sat (a # w) \<phi>) \<and> sat w (SImp (deriv a r) \<phi>)\<close>
  by (auto simp: nullable_iff lang_deriv Deriv_def Cons_eq_append_conv)

lemma sat_SConj_Cons:
  \<open>sat (a # w) (SConj r \<phi>) \<longleftrightarrow> nullable r \<and> sat (a # w) \<phi> \<or> sat w (SConj (deriv a r) \<phi>)\<close>
  by (auto simp: nullable_iff lang_deriv Deriv_def Cons_eq_append_conv)

lemma sat_Nil[simp]: \<open>sat [] \<phi> \<longleftrightarrow> fnull \<phi>\<close>
  by (induction \<phi>) (auto simp: nullable_iff)

lemma sat_Cons[simp]: \<open>sat (a # w) \<phi> \<longleftrightarrow> sat w (fderiv a \<phi>)\<close>
  by (induction \<phi> arbitrary: w)
    (simp_all add: sat_U_Cons sat_R_Cons sat_SImp_Cons sat_SConj_Cons
      del: sat_Until sat_Release sat_SImp sat_SConj)

lemma sat_foldl[code]: \<open>sat w \<phi> \<longleftrightarrow> fnull (foldl (\<lambda>\<phi> a. fderiv a \<phi>) \<phi> w)\<close>
  by (induction w arbitrary: \<phi>) simp_all

section \<open>Matching regular protocols\<close>

text \<open>\<open>Last\<close> holds exactly at the end of the trace, so \<open>SConj r Last\<close> says the whole
  trace lies in \<open>lang r\<close>: a regular expression is a protocol formula.\<close>

abbreviation Last where \<open>Last \<equiv> WNext Ff\<close>

lemma sat_Last[simp]: \<open>sat w Last \<longleftrightarrow> w = []\<close>
  by (cases w) simp_all

lemma sat_SConj_Last[simp]: \<open>sat w (SConj r Last) \<longleftrightarrow> w \<in> lang r\<close>
  by auto

lemma sat_SImp_Last: \<open>sat w (SImp r Last) \<longleftrightarrow> (\<forall>u v. w = u@v \<longrightarrow> u \<in> lang r \<longrightarrow> v = [])\<close>
  by auto

abbreviation \<open>Match r \<equiv> SConj r Last\<close>

section \<open>Normal forms\<close>

text \<open>Modulo associativity, commutativity and idempotence of \<open>And\<close>/\<open>Or\<close> and the regular
  normal form \<^const>\<open>norm\<close>, a formula has finitely many derivatives (for WS1S:
  \<^cite>\<open>\<open>Thm. 4\<close> in traytel2015\<close>). This makes the checker below terminate in
  practice; only the preservation of \<^const>\<open>sat\<close> is proved.\<close>

primrec ser :: \<open>'a ltlf \<Rightarrow> (nat \<times> 'a list \<times> 'a rexp) list\<close> where
  \<open>ser Ff = [(0, [], Zero)]\<close>
| \<open>ser Tt = [(1, [], Zero)]\<close>
| \<open>ser (Prop as) = [(2, as, Zero)]\<close>
| \<open>ser (NProp as) = [(3, as, Zero)]\<close>
| \<open>ser (Next \<phi>) = (4, [], Zero) # ser \<phi>\<close>
| \<open>ser (WNext \<phi>) = (5, [], Zero) # ser \<phi>\<close>
| \<open>ser (And \<phi> \<psi>) = (6, [], Zero) # ser \<phi> @ ser \<psi>\<close>
| \<open>ser (Or \<phi> \<psi>) = (7, [], Zero) # ser \<phi> @ ser \<psi>\<close>
| \<open>ser (Until \<phi> \<psi>) = (8, [], Zero) # ser \<phi> @ ser \<psi>\<close>
| \<open>ser (Release \<phi> \<psi>) = (9, [], Zero) # ser \<phi> @ ser \<psi>\<close>
| \<open>ser (SImp r \<phi>) = (10, [], r) # ser \<phi>\<close>
| \<open>ser (SConj r \<phi>) = (11, [], r) # ser \<phi>\<close>

text \<open>The preorder serialisation is prefix-free, so comparing serialisations
  lexicographically is a total order on formulas (only decidability is used).\<close>

definition le_ltlf :: \<open>'a::linorder ltlf \<Rightarrow> 'a ltlf \<Rightarrow> bool\<close> where
  \<open>le_ltlf \<phi> \<psi> \<longleftrightarrow> ser \<phi> \<le> ser \<psi>\<close>

fun ins_And :: \<open>'a::linorder ltlf \<Rightarrow> 'a ltlf \<Rightarrow> 'a ltlf\<close> where
  \<open>ins_And \<phi> (And \<psi> \<chi>) =
     (if \<phi> = \<psi> then And \<psi> \<chi>
      else if le_ltlf \<phi> \<psi> then And \<phi> (And \<psi> \<chi>) else And \<psi> (ins_And \<phi> \<chi>))\<close>
| \<open>ins_And \<phi> \<psi> = (if \<phi> = \<psi> then \<phi> else if le_ltlf \<phi> \<psi> then And \<phi> \<psi> else And \<psi> \<phi>)\<close>

fun nAnd :: \<open>'a::linorder ltlf \<Rightarrow> 'a ltlf \<Rightarrow> 'a ltlf\<close> where
  \<open>nAnd (And \<phi> \<psi>) \<chi> = nAnd \<phi> (nAnd \<psi> \<chi>)\<close>
| \<open>nAnd \<phi> \<chi> =
     (if \<phi> = Ff \<or> \<chi> = Ff then Ff else if \<phi> = Tt then \<chi> else if \<chi> = Tt then \<phi>
      else ins_And \<phi> \<chi>)\<close>

lemma sat_ins_And[simp]: \<open>sat w (ins_And \<phi> \<psi>) \<longleftrightarrow> sat w \<phi> \<and> sat w \<psi>\<close>
  by (induction \<phi> \<psi> rule: ins_And.induct) auto

lemma sat_nAnd[simp]: \<open>sat w (nAnd \<phi> \<psi>) \<longleftrightarrow> sat w \<phi> \<and> sat w \<psi>\<close>
  by (induction \<phi> \<psi> rule: nAnd.induct) auto

fun ins_Or :: \<open>'a::linorder ltlf \<Rightarrow> 'a ltlf \<Rightarrow> 'a ltlf\<close> where
  \<open>ins_Or \<phi> (Or \<psi> \<chi>) =
     (if \<phi> = \<psi> then Or \<psi> \<chi>
      else if le_ltlf \<phi> \<psi> then Or \<phi> (Or \<psi> \<chi>) else Or \<psi> (ins_Or \<phi> \<chi>))\<close>
| \<open>ins_Or \<phi> \<psi> = (if \<phi> = \<psi> then \<phi> else if le_ltlf \<phi> \<psi> then Or \<phi> \<psi> else Or \<psi> \<phi>)\<close>

fun nOr :: \<open>'a::linorder ltlf \<Rightarrow> 'a ltlf \<Rightarrow> 'a ltlf\<close> where
  \<open>nOr (Or \<phi> \<psi>) \<chi> = nOr \<phi> (nOr \<psi> \<chi>)\<close>
| \<open>nOr \<phi> \<chi> =
     (if \<phi> = Tt \<or> \<chi> = Tt then Tt else if \<phi> = Ff then \<chi> else if \<chi> = Ff then \<phi>
      else ins_Or \<phi> \<chi>)\<close>

lemma sat_ins_Or[simp]: \<open>sat w (ins_Or \<phi> \<psi>) \<longleftrightarrow> sat w \<phi> \<or> sat w \<psi>\<close>
  by (induction \<phi> \<psi> rule: ins_Or.induct) auto

lemma sat_nOr[simp]: \<open>sat w (nOr \<phi> \<psi>) \<longleftrightarrow> sat w \<phi> \<or> sat w \<psi>\<close>
  by (induction \<phi> \<psi> rule: nOr.induct) auto

fun nX where \<open>nX Ff = Ff\<close> | \<open>nX \<phi> = Next \<phi>\<close>
fun nWX where \<open>nWX Tt = Tt\<close> | \<open>nWX \<phi> = WNext \<phi>\<close>
definition nU where
  \<open>nU \<phi> \<psi> = (if \<psi> = Ff then Ff else if \<psi> = Tt then Tt else if \<phi> = Ff then \<psi> else Until \<phi> \<psi>)\<close>
definition nR where
  \<open>nR \<phi> \<psi> = (if \<psi> = Tt then Tt else if \<psi> = Ff then Ff else if \<phi> = Tt then \<psi> else Release \<phi> \<psi>)\<close>

definition nSImp :: \<open>'a::order rexp \<Rightarrow> 'a ltlf \<Rightarrow> 'a ltlf\<close> where
  \<open>nSImp r \<phi> = (let r' = norm r in if r' = Zero then Tt else if r' = One then \<phi> else SImp r' \<phi>)\<close>

definition nSConj :: \<open>'a::order rexp \<Rightarrow> 'a ltlf \<Rightarrow> 'a ltlf\<close> where
  \<open>nSConj r \<phi> = (let r' = norm r in if r' = Zero then Ff else if r' = One then \<phi> else SConj r' \<phi>)\<close>

lemma sat_nX[simp]: \<open>sat w (nX \<phi>) \<longleftrightarrow> sat w (Next \<phi>)\<close>
  by (cases \<phi>; cases w) simp_all

lemma sat_nWX[simp]: \<open>sat w (nWX \<phi>) \<longleftrightarrow> sat w (WNext \<phi>)\<close>
  by (cases \<phi>; cases w) simp_all

lemma sat_U_Ff_left: \<open>sat w (Until Ff \<psi>) \<longleftrightarrow> sat w \<psi>\<close>
  by (auto simp del: sat_Nil sat_Cons) (metis drop_0 not_gr_zero)

lemma sat_R_Tt_left: \<open>sat w (Release Tt \<psi>) \<longleftrightarrow> sat w \<psi>\<close>
  by (auto simp del: sat_Nil sat_Cons) (metis drop_0 not_gr_zero)

lemma sat_U_Tt: \<open>sat w (Until \<phi> Tt)\<close>
  by (auto simp del: sat_Nil sat_Cons intro: exI[of _ 0])

lemma sat_U_Ff: \<open>\<not> sat w (Until \<phi> Ff)\<close>
  by (simp del: sat_Nil sat_Cons)

lemma sat_R_Tt: \<open>sat w (Release \<phi> Tt)\<close>
  by (simp del: sat_Nil sat_Cons)

lemma sat_R_Ff: \<open>\<not> sat w (Release \<phi> Ff)\<close>
  by (auto simp del: sat_Nil sat_Cons dest: spec[of _ 0])

lemma sat_nU[simp]: \<open>sat w (nU \<phi> \<psi>) \<longleftrightarrow> sat w (Until \<phi> \<psi>)\<close>
  by (simp add: nU_def sat_U_Ff_left sat_U_Tt sat_U_Ff del: sat_Nil sat_Cons sat_Until)

lemma sat_nR[simp]: \<open>sat w (nR \<phi> \<psi>) \<longleftrightarrow> sat w (Release \<phi> \<psi>)\<close>
  by (simp add: nR_def sat_R_Tt_left sat_R_Tt sat_R_Ff del: sat_Nil sat_Cons sat_Release)

lemma sat_SImp_norm: \<open>sat w (SImp (norm r) \<phi>) \<longleftrightarrow> sat w (SImp r \<phi>)\<close>
  and sat_SConj_norm: \<open>sat w (SConj (norm r) \<phi>) \<longleftrightarrow> sat w (SConj r \<phi>)\<close>
  by simp_all

lemma sat_nSImp[simp]: \<open>sat w (nSImp r \<phi>) \<longleftrightarrow> sat w (SImp r \<phi>)\<close>
proof -
  have \<open>sat w (if r' = Zero then Tt else if r' = One then \<phi> else SImp r' \<phi>) \<longleftrightarrow> sat w (SImp r' \<phi>)\<close>
    for r' :: \<open>'a rexp\<close>
    by auto
  from this[of \<open>norm r\<close>] show ?thesis unfolding nSImp_def Let_def by simp
qed

lemma sat_nSConj[simp]: \<open>sat w (nSConj r \<phi>) \<longleftrightarrow> sat w (SConj r \<phi>)\<close>
proof -
  have \<open>sat w (if r' = Zero then Ff else if r' = One then \<phi> else SConj r' \<phi>) \<longleftrightarrow> sat w (SConj r' \<phi>)\<close>
    for r' :: \<open>'a rexp\<close>
    by auto
  from this[of \<open>norm r\<close>] show ?thesis unfolding nSConj_def Let_def by simp
qed

primrec fnorm :: \<open>'a::linorder ltlf \<Rightarrow> 'a ltlf\<close> where
  \<open>fnorm Ff = Ff\<close>
| \<open>fnorm Tt = Tt\<close>
| \<open>fnorm (Prop as) = (if as = [] then Ff else Prop (remdups (sort as)))\<close>
| \<open>fnorm (NProp as) = (if as = [] then Tt else NProp (remdups (sort as)))\<close>
| \<open>fnorm (And \<phi> \<psi>) = nAnd (fnorm \<phi>) (fnorm \<psi>)\<close>
| \<open>fnorm (Or \<phi> \<psi>) = nOr (fnorm \<phi>) (fnorm \<psi>)\<close>
| \<open>fnorm (Next \<phi>) = nX (fnorm \<phi>)\<close>
| \<open>fnorm (WNext \<phi>) = nWX (fnorm \<phi>)\<close>
| \<open>fnorm (Until \<phi> \<psi>) = nU (fnorm \<phi>) (fnorm \<psi>)\<close>
| \<open>fnorm (Release \<phi> \<psi>) = nR (fnorm \<phi>) (fnorm \<psi>)\<close>
| \<open>fnorm (SImp r \<phi>) = nSImp r (fnorm \<phi>)\<close>
| \<open>fnorm (SConj r \<phi>) = nSConj r (fnorm \<phi>)\<close>

lemma sat_fnorm[simp]: \<open>sat w (fnorm \<phi>) \<longleftrightarrow> sat w \<phi>\<close>
proof (induction \<phi> arbitrary: w)
  case (Prop as)
  then show ?case by (cases w) simp_all
next
  case (NProp as)
  then show ?case by (cases w) simp_all
next
  case (Until \<phi> \<psi>)
  then show ?case by (simp del: sat_Nil sat_Cons sat_Until) (simp only: sat_Until Until)
next
  case (Release \<phi> \<psi>)
  then show ?case by (simp del: sat_Nil sat_Cons sat_Release) (simp only: sat_Release Release)
next
  case (Next \<phi>)
  then show ?case by (cases w) simp_all
next
  case (WNext \<phi>)
  then show ?case by (cases w) simp_all
qed simp_all

text \<open>The normalising derivative: the transition function of the checker.\<close>

definition nfderiv :: \<open>'a::linorder \<Rightarrow> 'a ltlf \<Rightarrow> 'a ltlf\<close> where
  \<open>nfderiv a \<phi> = fnorm (fderiv a \<phi>)\<close>

lemma sat_nfderiv[simp]: \<open>sat w (nfderiv a \<phi>) \<longleftrightarrow> sat (a # w) \<phi>\<close>
  by (simp add: nfderiv_def)

section \<open>A generic inclusion checker\<close>

text \<open>Inclusion of the language of state \<open>s\<close> in that of \<open>t\<close>, over the alphabet \<open>as\<close>: every
  pair in the product closure of \<open>(s, t)\<close> satisfies \<open>os p \<longrightarrow> ot q\<close>. This is the one-sided
  variant of the bisimulation worklist of \<^cite>\<open>\<open>Sect. 2, Thm. 2\<close> in traytel2015\<close> and of
  \<^const>\<open>Equivalence_Checking.closure\<close>; \<^const>\<open>rtrancl_while\<close> returns \<open>None\<close> only if
  the closure is infinite.\<close>

definition drive :: \<open>('a \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> 'a list \<Rightarrow> 's\<close> where
  \<open>drive d s w = foldl (\<lambda>s a. d a s) s w\<close>

definition accepts :: \<open>('s \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
  \<open>accepts acc d s w \<longleftrightarrow> acc (drive d s w)\<close>

lemma drive_Nil[simp]: \<open>drive d s [] = s\<close>
  and drive_Cons[simp]: \<open>drive d s (a # w) = drive d (d a s) w\<close>
  by (simp_all add: drive_def)

definition incl ::
  \<open>('s \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('t \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 't \<Rightarrow> 't) \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> 't \<Rightarrow> bool\<close> where
  \<open>incl os ds ot dt as s t \<longleftrightarrow>
     (case rtrancl_while (\<lambda>(p, q). os p \<longrightarrow> ot q) (\<lambda>(p, q). map (\<lambda>a. (ds a p, dt a q)) as) (s, t) of
        Some ([], _) \<Rightarrow> True | _ \<Rightarrow> False)\<close>

lemma incl_sound:
  assumes \<open>incl os ds ot dt as s t\<close> \<open>set w \<subseteq> set as\<close> \<open>accepts os ds s w\<close>
  shows \<open>accepts ot dt t w\<close>
proof -
  let ?f = \<open>\<lambda>(p, q). map (\<lambda>a. (ds a p, dt a q)) as\<close>
  let ?R = \<open>{(x, y). y \<in> set (?f x)}\<close>
  from assms(1) obtain Z where \<open>rtrancl_while (\<lambda>(p, q). os p \<longrightarrow> ot q) ?f (s, t) = Some ([], Z)\<close>
    by (auto simp: incl_def split: option.splits list.splits)
  from rtrancl_while_Some[OF this]
  have Z: \<open>Z = ?R\<^sup>* `` {(s, t)}\<close> \<open>\<forall>(p, q) \<in> Z. os p \<longrightarrow> ot q\<close> by simp_all
  have \<open>((s, t), (drive ds s w, drive dt t w)) \<in> ?R\<^sup>*\<close> if \<open>set w \<subseteq> set as\<close> for w
    using that
  proof (induction w rule: rev_induct)
    case (snoc a w)
    then have \<open>((s, t), (drive ds s w, drive dt t w)) \<in> ?R\<^sup>*\<close> by simp
    moreover have
      \<open>((drive ds s w, drive dt t w), (drive ds s (w @ [a]), drive dt t (w @ [a]))) \<in> ?R\<close>
      using snoc.prems by (auto simp: drive_def)
    ultimately show ?case by (rule rtrancl_into_rtrancl)
  qed simp
  with assms(2) have \<open>(drive ds s w, drive dt t w) \<in> Z\<close> unfolding Z(1) by blast
  with Z(2) assms(3) show ?thesis by (auto simp: accepts_def dest!: bspec)
qed

subsection \<open>Instances\<close>

text \<open>A regular expression against a formula (the grade check), a formula against a formula
  (signature matching may strengthen a protocol), and two regular expressions.\<close>

definition incl_rl :: \<open>'a::linorder list \<Rightarrow> 'a rexp \<Rightarrow> 'a ltlf \<Rightarrow> bool\<close> where
  \<open>incl_rl as r \<phi> = incl nullable nderiv fnull nfderiv as (norm r) (fnorm \<phi>)\<close>

definition incl_ll :: \<open>'a::linorder list \<Rightarrow> 'a ltlf \<Rightarrow> 'a ltlf \<Rightarrow> bool\<close> where
  \<open>incl_ll as \<phi> \<psi> = incl fnull nfderiv fnull nfderiv as (fnorm \<phi>) (fnorm \<psi>)\<close>

definition incl_rr :: \<open>'a::linorder list \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp \<Rightarrow> bool\<close> where
  \<open>incl_rr as r s = incl nullable nderiv nullable nderiv as (norm r) (norm s)\<close>

lemma accepts_nderiv: \<open>accepts nullable nderiv r w \<longleftrightarrow> w \<in> lang r\<close>
  by (simp add: accepts_def drive_def nullable_nderivs)

lemma accepts_nfderiv: \<open>accepts fnull nfderiv \<phi> w \<longleftrightarrow> sat w \<phi>\<close>
  by (induction w arbitrary: \<phi>) (simp_all add: accepts_def)

lemma incl_rl_sound: \<open>incl_rl as r \<phi> \<Longrightarrow> atoms r \<subseteq> set as \<Longrightarrow> w \<in> lang r \<Longrightarrow> sat w \<phi>\<close>
  using incl_sound[where os = nullable and ds = nderiv and ot = fnull and dt = nfderiv
                   and as = as and s = \<open>norm r\<close> and t = \<open>fnorm \<phi>\<close> and w = w] atoms_lang[of w r]
  by (auto simp: incl_rl_def accepts_nderiv accepts_nfderiv)

lemma incl_ll_sound: \<open>incl_ll as \<phi> \<psi> \<Longrightarrow> set w \<subseteq> set as \<Longrightarrow> sat w \<phi> \<Longrightarrow> sat w \<psi>\<close>
  using incl_sound[where os = fnull and ds = nfderiv and ot = fnull and dt = nfderiv
                   and as = as and s = \<open>fnorm \<phi>\<close> and t = \<open>fnorm \<psi>\<close> and w = w]
  by (auto simp: incl_ll_def accepts_nfderiv)

lemma incl_rr_sound: \<open>incl_rr as r s \<Longrightarrow> atoms r \<subseteq> set as \<Longrightarrow> w \<in> lang r \<Longrightarrow> w \<in> lang s\<close>
  using incl_sound[where os = nullable and ds = nderiv and ot = nullable and dt = nderiv
                   and as = as and s = \<open>norm r\<close> and t = \<open>norm s\<close> and w = w] atoms_lang[of w r]
  by (auto simp: incl_rr_def accepts_nderiv)

text \<open>With the alphabet read off the regular expression, the two regular-expression checks
  need no side condition; the formula check keeps the effect's operations as its alphabet,
  since a trace may use an operation neither formula mentions.\<close>

definition check_rl :: \<open>'a::linorder rexp \<Rightarrow> 'a ltlf \<Rightarrow> bool\<close> where
  \<open>check_rl r \<phi> = incl_rl (add_atoms r []) r \<phi>\<close>

definition check_rr :: \<open>'a::linorder rexp \<Rightarrow> 'a rexp \<Rightarrow> bool\<close> where
  \<open>check_rr r s = incl_rr (add_atoms r []) r s\<close>

lemma check_rl_sound: \<open>check_rl r \<phi> \<Longrightarrow> w \<in> lang r \<Longrightarrow> sat w \<phi>\<close>
  using incl_rl_sound[where as = \<open>add_atoms r []\<close>] by (simp add: check_rl_def set_add_atoms)

lemma check_rr_sound: \<open>check_rr r s \<Longrightarrow> lang r \<subseteq> lang s\<close>
  using incl_rr_sound[where as = \<open>add_atoms r []\<close>] by (auto simp: check_rr_def set_add_atoms)

end
