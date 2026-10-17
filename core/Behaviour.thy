theory Behaviour
  imports Foreign CaraML_Spec.Pipeline
begin

section \<open>Behaviours of clocked semantics\<close>

text \<open>Behaviours of clocked semantics in the terms of the specification, and
  Core as a \<^locale>\<open>language\<close> (\<^text>\<open>core_sem\<close>). The value type of a clocked
  result is a type variable: behaviours never look at the value, and the
  languages of the backend have their own values.\<close>

subsection \<open>Behaviours\<close>

text \<open>A clocked semantics is a clock-indexed family of results with their
  traces. Its behaviour \<^cite>\<open>\<open>Sect. 10\<close> in tan2016\<close> \<^cite>\<open>owens2016\<close>: a
  program terminates if some clock yields a value or a host error, fails if
  some clock gets stuck, and diverges if it times out at every clock, its event
  stream then the limit of the traces along the clocks. For a
  \<^const>\<open>tres_le\<close>-chain the cases are exclusive and the terminating outcome is
  unique.\<close>

definition outcome :: \<open>'a cres \<times> ffi_ev list \<Rightarrow> ffi_ev behaviour\<close> where
  \<open>outcome r =
     (case r of
        (Rval _, evs) \<Rightarrow> Terminate Success evs
      | (Rhost ev, evs) \<Rightarrow> Terminate (FFI_error ev) evs
      | _ \<Rightarrow> Fail)\<close>

definition beh :: \<open>(nat \<Rightarrow> 'a cres \<times> ffi_ev list) \<Rightarrow> ffi_ev behaviour set\<close> where
  \<open>beh F =
     (if \<exists>k. fst (F k) \<noteq> Rtimeout
      then {outcome (F k) | k. fst (F k) \<noteq> Rtimeout}
      else {Diverge (lSup (range (\<lambda>k. llist_of (snd (F k)))))})\<close>

lemma beh_nonempty: \<open>beh F \<noteq> {}\<close>
  by (auto simp: beh_def)

lemma tres_le_ne: \<open>r \<sqsubseteq>\<^sub>t r' \<Longrightarrow> fst r \<noteq> Rtimeout \<Longrightarrow> r' = r\<close>
  by (auto simp: tres_le_def)

lemma tres_le_trace: \<open>r \<sqsubseteq>\<^sub>t r' \<Longrightarrow> prefix (snd r) (snd r')\<close>
  by (auto simp: tres_le_def prefix_def)

lemma chain_range:
  fixes f :: \<open>nat \<Rightarrow> 'a llist\<close>
  assumes \<open>\<And>k k'. k \<le> k' \<Longrightarrow> lprefix (f k) (f k')\<close>
  shows \<open>Complete_Partial_Order.chain lprefix (range f)\<close>
proof (rule chainI)
  fix x y assume \<open>x \<in> range f\<close> \<open>y \<in> range f\<close>
  then obtain i j where \<open>x = f i\<close> \<open>y = f j\<close> by blast
  then show \<open>lprefix x y \<or> lprefix y x\<close>
    using assms[of i j] assms[of j i] nat_le_linear[of i j] by auto
qed

lemma lSup_chain_le:
  fixes f g :: \<open>nat \<Rightarrow> 'a llist\<close>
  assumes f: \<open>\<And>k k'. k \<le> k' \<Longrightarrow> lprefix (f k) (f k')\<close>
    and g: \<open>\<And>k k'. k \<le> k' \<Longrightarrow> lprefix (g k) (g k')\<close>
    and eq: \<open>\<And>k. n \<le> k \<Longrightarrow> f k = g k\<close>
  shows \<open>lprefix (lSup (range f)) (lSup (range g))\<close>
proof -
  have chf: \<open>Complete_Partial_Order.chain lprefix (range f)\<close>
    by (auto intro: chain_range f)
  have chg: \<open>Complete_Partial_Order.chain lprefix (range g)\<close>
    by (auto intro: chain_range g)
  show ?thesis
  proof (rule chain_lSup_lprefix[OF chf])
    fix xs assume \<open>xs \<in> range f\<close>
    then obtain k where xs: \<open>xs = f k\<close> ..
    have \<open>lprefix (f k) (g (max k n))\<close>
      using f[of k \<open>max k n\<close>] eq[of \<open>max k n\<close>] by simp
    also have \<open>lprefix (g (max k n)) (lSup (range g))\<close>
      by (rule chain_lprefix_lSup[OF chg]) (rule rangeI)
    finally show \<open>lprefix xs (lSup (range g))\<close> by (simp add: xs)
  qed
qed

lemma lSup_chain_eq:
  fixes f g :: \<open>nat \<Rightarrow> 'a llist\<close>
  assumes f: \<open>\<And>k k'. k \<le> k' \<Longrightarrow> lprefix (f k) (f k')\<close>
    and g: \<open>\<And>k k'. k \<le> k' \<Longrightarrow> lprefix (g k) (g k')\<close>
    and eq: \<open>\<And>k. n \<le> k \<Longrightarrow> f k = g k\<close>
  shows \<open>lSup (range f) = lSup (range g)\<close>
  using lSup_chain_le[OF f g eq] lSup_chain_le[OF g f eq[symmetric]] by (rule lprefix_antisym)

text \<open>Two chains that agree from some clock on have the same behaviour:\<close>

lemma beh_chain_eq:
  assumes F: \<open>\<And>k k'. k \<le> k' \<Longrightarrow> F k \<sqsubseteq>\<^sub>t F k'\<close>
    and G: \<open>\<And>k k'. k \<le> k' \<Longrightarrow> G k \<sqsubseteq>\<^sub>t G k'\<close>
    and eq: \<open>\<And>k. n \<le> k \<Longrightarrow> F k = G k\<close>
  shows \<open>beh F = beh G\<close>
proof -
  have ne: \<open>fst (F k) \<noteq> Rtimeout \<Longrightarrow> F k = G (max k n)\<close> for k
    using tres_le_ne[OF F[of k \<open>max k n\<close>]] eq[of \<open>max k n\<close>] by simp
  have ne': \<open>fst (G k) \<noteq> Rtimeout \<Longrightarrow> G k = F (max k n)\<close> for k
    using tres_le_ne[OF G[of k \<open>max k n\<close>]] eq[of \<open>max k n\<close>] by simp
  have tm: \<open>(\<exists>k. fst (F k) \<noteq> Rtimeout) \<longleftrightarrow> (\<exists>k. fst (G k) \<noteq> Rtimeout)\<close>
    by (metis ne ne')
  have outs: \<open>{outcome (F k) | k. fst (F k) \<noteq> Rtimeout} =
      {outcome (G k) | k. fst (G k) \<noteq> Rtimeout}\<close>
    by (auto; metis ne ne')
  have dv: \<open>lSup (range (\<lambda>k. llist_of (snd (F k)))) =
      lSup (range (\<lambda>k. llist_of (snd (G k))))\<close>
    by (rule lSup_chain_eq[of _ _ n]) (auto simp: eq intro!: tres_le_trace intro: F G)
  show ?thesis
    by (simp only: beh_def tm outs dv)
qed

subsection \<open>Behaviour congruence\<close>

text \<open>A behaviour observes of a clocked result whether it is a value, a
  timeout, stuckness, or which host error, and the trace (never the value).
  Two results \<^emph>\<open>look alike\<close> when they agree on that much. A pass between
  clocked semantics closes with \<open>beh_cong\<close>, clock for clock, or with
  \<open>beh_sim\<close>, up to a shift of the clock in either direction.\<close>

fun same_res :: \<open>'a cres \<Rightarrow> 'b cres \<Rightarrow> bool\<close> where
  \<open>same_res (Rval _) (Rval _) \<longleftrightarrow> True\<close>
| \<open>same_res Rtimeout Rtimeout \<longleftrightarrow> True\<close>
| \<open>same_res Rerr Rerr \<longleftrightarrow> True\<close>
| \<open>same_res (Rhost ev) (Rhost ev') \<longleftrightarrow> ev = ev'\<close>
| \<open>same_res _ _ \<longleftrightarrow> False\<close>

definition alike :: \<open>'a cres \<times> ffi_ev list \<Rightarrow> 'b cres \<times> ffi_ev list \<Rightarrow> bool\<close>
where
  \<open>alike r r' \<longleftrightarrow> same_res (fst r) (fst r') \<and> snd r = snd r'\<close>

lemma same_res_timeout: \<open>same_res r r' \<Longrightarrow> r = Rtimeout \<longleftrightarrow> r' = Rtimeout\<close>
  by (cases r; cases r') simp_all

lemma alike_outcome: \<open>alike r r' \<Longrightarrow> outcome r = outcome r'\<close>
  by (cases r; cases r'; cases \<open>fst r\<close>; cases \<open>fst r'\<close>)
     (simp_all add: alike_def outcome_def)

lemma beh_cong:
  assumes \<open>\<And>k. alike (F k) (G k)\<close>
  shows \<open>beh F = beh G\<close>
proof -
  have \<open>fst (F k) = Rtimeout \<longleftrightarrow> fst (G k) = Rtimeout\<close>
    and \<open>outcome (F k) = outcome (G k)\<close>
    and \<open>snd (F k) = snd (G k)\<close> for k
    using assms[of k] by (auto simp: alike_def alike_outcome dest: same_res_timeout)
  then show ?thesis
    by (simp add: beh_def)
qed

text \<open>Up to clock shifts, \<open>r \<preceq> r'\<close>: \<open>r\<close> is a timeout whose trace \<open>r'\<close>
  extends, or the two look alike.\<close>

definition res_below :: \<open>'a cres \<times> ffi_ev list \<Rightarrow> 'b cres \<times> ffi_ev list \<Rightarrow> bool\<close>
  (infix \<open>\<preceq>\<close> 50) where
  \<open>r \<preceq> r' \<longleftrightarrow> (fst r = Rtimeout \<and> prefix (snd r) (snd r')) \<or> alike r r'\<close>

lemma alike_res_below: \<open>alike r r' \<Longrightarrow> r \<preceq> r'\<close>
  by (simp add: res_below_def)

lemma beh_sim:
  fixes F G :: \<open>nat \<Rightarrow> 'a cres \<times> ffi_ev list\<close>
  assumes F: \<open>\<And>k k'. k \<le> k' \<Longrightarrow> F k \<sqsubseteq>\<^sub>t F k'\<close>
    and G: \<open>\<And>k k'. k \<le> k' \<Longrightarrow> G k \<sqsubseteq>\<^sub>t G k'\<close>
    and FG: \<open>\<And>k. \<exists>k'. F k \<preceq> G k'\<close>
    and GF: \<open>\<And>k. \<exists>k'. G k \<preceq> F k'\<close>
  shows \<open>beh F = beh G\<close>
proof -
  have fin: \<open>\<exists>k'. alike (A k) (B k') \<and> fst (B k') \<noteq> Rtimeout\<close>
    if AB: \<open>\<And>k. \<exists>k'. A k \<preceq> B k'\<close> and nt: \<open>fst (A k) \<noteq> Rtimeout\<close>
    for A B :: \<open>nat \<Rightarrow> 'a cres \<times> ffi_ev list\<close> and k
  proof -
    obtain k' where \<open>A k \<preceq> B k'\<close> using AB by blast
    with nt have \<open>alike (A k) (B k')\<close> by (simp add: res_below_def)
    with nt show ?thesis by (auto simp: alike_def dest: same_res_timeout)
  qed
  have sub: \<open>{outcome (A k) | k. fst (A k) \<noteq> Rtimeout} \<subseteq>
      {outcome (B k) | k. fst (B k) \<noteq> Rtimeout}\<close>
    if AB: \<open>\<And>k. \<exists>k'. A k \<preceq> B k'\<close> for A B :: \<open>nat \<Rightarrow> 'a cres \<times> ffi_ev list\<close>
  proof clarify
    fix k assume nt: \<open>fst (A k) \<noteq> Rtimeout\<close>
    obtain k' where \<open>alike (A k) (B k')\<close> \<open>fst (B k') \<noteq> Rtimeout\<close>
      using fin[of A B, OF AB nt] by blast
    then show \<open>\<exists>k'. outcome (A k) = outcome (B k') \<and> fst (B k') \<noteq> Rtimeout\<close>
      by (blast dest: alike_outcome)
  qed
  have tm: \<open>(\<exists>k. fst (F k) \<noteq> Rtimeout) \<longleftrightarrow> (\<exists>k. fst (G k) \<noteq> Rtimeout)\<close>
    using fin[of F G, OF FG] fin[of G F, OF GF] by blast
  have outs: \<open>{outcome (F k) | k. fst (F k) \<noteq> Rtimeout} =
      {outcome (G k) | k. fst (G k) \<noteq> Rtimeout}\<close>
    by (rule subset_antisym[OF sub[of F G, OF FG] sub[of G F, OF GF]])
  have sup_le: \<open>lprefix (lSup (range (\<lambda>k. llist_of (snd (A k)))))
      (lSup (range (\<lambda>k. llist_of (snd (B k)))))\<close>
    if A: \<open>\<And>k k'. k \<le> k' \<Longrightarrow> A k \<sqsubseteq>\<^sub>t A k'\<close>
      and B: \<open>\<And>k k'. k \<le> k' \<Longrightarrow> B k \<sqsubseteq>\<^sub>t B k'\<close>
      and AB: \<open>\<And>k. \<exists>k'. A k \<preceq> B k'\<close>
    for A B :: \<open>nat \<Rightarrow> 'a cres \<times> ffi_ev list\<close>
  proof -
    have chA: \<open>Complete_Partial_Order.chain lprefix (range (\<lambda>k. llist_of (snd (A k))))\<close>
      by (rule chain_range) (simp add: tres_le_trace A)
    have chB: \<open>Complete_Partial_Order.chain lprefix (range (\<lambda>k. llist_of (snd (B k))))\<close>
      by (rule chain_range) (simp add: tres_le_trace B)
    show ?thesis
    proof (rule chain_lSup_lprefix[OF chA])
      fix xs assume \<open>xs \<in> range (\<lambda>k. llist_of (snd (A k)))\<close>
      then obtain k where xs: \<open>xs = llist_of (snd (A k))\<close> by blast
      obtain k' where \<open>A k \<preceq> B k'\<close> using AB by blast
      then have \<open>lprefix xs (llist_of (snd (B k')))\<close>
        by (auto simp: xs res_below_def alike_def)
      also have \<open>lprefix (llist_of (snd (B k'))) (lSup (range (\<lambda>k. llist_of (snd (B k)))))\<close>
        by (rule chain_lprefix_lSup[OF chB]) (rule rangeI)
      finally show \<open>lprefix xs (lSup (range (\<lambda>k. llist_of (snd (B k)))))\<close> .
    qed
  qed
  have dv: \<open>lSup (range (\<lambda>k. llist_of (snd (F k)))) =
      lSup (range (\<lambda>k. llist_of (snd (G k))))\<close>
    by (rule lprefix_antisym[OF sup_le[of F G, OF F G FG] sup_le[of G F, OF G F GF]])
  show ?thesis
    by (simp only: beh_def tm outs dv)
qed

subsection \<open>Failure\<close>

lemma Fail_beh:
  fixes F :: \<open>nat \<Rightarrow> 'a cres \<times> ffi_ev list\<close>
  shows \<open>Fail \<in> beh F \<longleftrightarrow> (\<exists>k. fst (F k) = Rerr)\<close>
proof -
  have \<open>Fail = outcome r \<longleftrightarrow> fst r = Rerr \<or> fst r = Rtimeout\<close>
    for r :: \<open>'a cres \<times> ffi_ev list\<close>
    by (cases r; cases \<open>fst r\<close>) (auto simp: outcome_def)
  then show ?thesis
    unfolding beh_def by auto
qed

lemma Fail_beh_obs: \<open>Fail \<in> beh (\<lambda>k. obs (F k)) \<longleftrightarrow> (\<exists>k. fst (F k) = Rerr)\<close>
  by (simp add: Fail_beh fst_obs)

subsection \<open>Core as a language\<close>

text \<open>The program loop \<^const>\<open>csem\<close> at the opaque host, observed erased
  (\<^theory>\<open>CaraML_Core.Foreign\<close>).\<close>

definition core_sem :: \<open>ffi \<Rightarrow> cprog \<Rightarrow> ffi_ev behaviour set\<close> where
  \<open>core_sem ffi p = beh (\<lambda>k. obs (csem (opaque ffi) p k))\<close>

lemma core_language: \<open>language core_sem\<close>
  by unfold_locales (simp add: core_sem_def beh_nonempty)

interpretation core: language core_sem
  by (rule core_language)

end
