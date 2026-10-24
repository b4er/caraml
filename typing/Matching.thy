theory Matching
  imports Types
begin

section \<open>Matching schemes\<close>

text \<open>Implicit resolution and signature matching compare schemes against
  types up to instantiation of the bound variables, that is \<open>\<sigma> \<succeq> \<tau>\<close>,
  an existential over substitutions that cannot compute. \<open>tmatch\<close> is
  first-order matching with an accumulator of partial bindings, the bound
  variables flexible and everything else rigid; \<^text>\<open>imatch_sinst\<close>
  proves it sound and complete for \<open>\<succeq>\<close>, so resolution is decidable and
  the inference algorithm runs it directly \<^cite>\<open>\<open>Sect. 2.2.2\<close> in white2014\<close>.\<close>

notation Option.bind (infixr \<open>\<bind>\<close> 54)

type_synonym tsub = \<open>tvar \<rightharpoonup> kty\<close>
type_synonym rsub = \<open>rvar \<rightharpoonup> krow\<close>

definition mk_tsub :: \<open>tsub \<Rightarrow> tvar \<Rightarrow> kty\<close> where
  \<open>mk_tsub \<theta> a = (case \<theta> a of Some \<tau> \<Rightarrow> \<tau> | None \<Rightarrow> TV a)\<close>

definition mk_rsub :: \<open>rsub \<Rightarrow> rvar \<Rightarrow> krow\<close> where
  \<open>mk_rsub \<rho> v = (case \<rho> v of Some r \<Rightarrow> r | None \<Rightarrow> RV v)\<close>

definition mk_btsub :: \<open>tsub \<Rightarrow> tvar \<Rightarrow> kty\<close> where
  \<open>mk_btsub \<theta> a = (case \<theta> a of Some \<tau> \<Rightarrow> \<tau> | None \<Rightarrow> TB a)\<close>

definition mk_brsub :: \<open>rsub \<Rightarrow> rvar \<Rightarrow> krow\<close> where
  \<open>mk_brsub \<rho> v = (case \<rho> v of Some r \<Rightarrow> r | None \<Rightarrow> RB v)\<close>

fun rmatch :: \<open>krow \<Rightarrow> krow \<Rightarrow> rsub \<Rightarrow> rsub option\<close> where
  \<open>rmatch RNil RNil \<rho> = Some \<rho>\<close>
| \<open>rmatch (RV v) w \<rho> = (if w = RV v then Some \<rho> else None)\<close>
| \<open>rmatch (RB v) w \<rho> =
     (case \<rho> v of
        None \<Rightarrow> Some (\<rho>(v \<mapsto> w))
      | Some w' \<Rightarrow> (if w' = w then Some \<rho> else None))\<close>
| \<open>rmatch (RCons l r) (RCons l' w) \<rho> =
     (if l = l' then rmatch r w \<rho> else None)\<close>
| \<open>rmatch r w \<rho> = None\<close>

fun tmatch :: \<open>kty \<Rightarrow> kty \<Rightarrow> tsub \<times> rsub \<Rightarrow> (tsub \<times> rsub) option\<close>
and tmatchs :: \<open>kty list \<Rightarrow> kty list \<Rightarrow> tsub \<times> rsub \<Rightarrow> (tsub \<times> rsub) option\<close> where
  \<open>tmatch (TV a) w \<sigma> = (if w = TV a then Some \<sigma> else None)\<close>
| \<open>tmatch (TK a) w \<sigma> = (if w = TK a then Some \<sigma> else None)\<close>
| \<open>tmatch (TA k i) w \<sigma> = (if w = TA k i then Some \<sigma> else None)\<close>
| \<open>tmatch (TB a) w (\<theta>, \<rho>) =
     (case \<theta> a of
        None \<Rightarrow> Some (\<theta>(a \<mapsto> w), \<rho>)
      | Some w' \<Rightarrow> (if w' = w then Some (\<theta>, \<rho>) else None))\<close>
| \<open>tmatch (TC c ts) (TC c' ws) \<sigma> =
     (if c = c' then tmatchs ts ws \<sigma> else None)\<close>
| \<open>tmatch (TFn t\<^sub>1 e t\<^sub>2) (TFn w\<^sub>1 f w\<^sub>2) \<sigma> =
     tmatch t\<^sub>1 w\<^sub>1 \<sigma> \<bind> (\<lambda>(\<theta>, \<rho>).
       rmatch e f \<rho> \<bind> (\<lambda>\<rho>'. tmatch t\<^sub>2 w\<^sub>2 (\<theta>, \<rho>')))\<close>
| \<open>tmatch (TDep i sg T e t) (TDep i' sg' T' f w) (\<theta>, \<rho>) =
     (if i = i' \<and> sg = sg' \<and> T = T'
      then rmatch e f \<rho> \<bind> (\<lambda>\<rho>'. tmatch t w (\<theta>, \<rho>')) else None)\<close>
| \<open>tmatch (TApp t\<^sub>1 t\<^sub>2) (TApp w\<^sub>1 w\<^sub>2) \<sigma> =
     tmatch t\<^sub>1 w\<^sub>1 \<sigma> \<bind> tmatch t\<^sub>2 w\<^sub>2\<close>
| \<open>tmatch (TEv l s t) (TEv l' s' w) \<sigma> =
     tmatch l l' \<sigma> \<bind> (\<lambda>\<sigma>\<^sub>1. tmatch s s' \<sigma>\<^sub>1 \<bind> tmatch t w)\<close>
| \<open>tmatch (TAct l K e t) (TAct l' K' f w) \<sigma> =
     (if K = K'
      then tmatch l l' \<sigma> \<bind> (\<lambda>(\<theta>, \<rho>). rmatch e f \<rho> \<bind> (\<lambda>\<rho>'. tmatch t w (\<theta>, \<rho>')))
      else None)\<close>
| \<open>tmatch TRNil TRNil \<sigma> = Some \<sigma>\<close>
| \<open>tmatch (TRCons l t r) (TRCons l' w r') \<sigma> =
     (if l = l' then tmatch t w \<sigma> \<bind> tmatch r r' else None)\<close>
| \<open>tmatch t w \<sigma> = None\<close>
| \<open>tmatchs [] [] \<sigma> = Some \<sigma>\<close>
| \<open>tmatchs (t # ts) (w # ws) \<sigma> =
     tmatch t w \<sigma> \<bind> tmatchs ts ws\<close>
| \<open>tmatchs ts ws \<sigma> = None\<close>  (* ~13s *)

lemmas tmatch_induct = tmatch_tmatchs.induct[named_cases tmatch]

lemma obind_SomeE:
  assumes \<open>(a \<bind> f) = Some r\<close>
  obtains x where \<open>a = Some x\<close> and \<open>f x = Some r\<close>
  using assms by (auto simp: bind_eq_Some_conv)

lemma rmatch_le: \<open>rmatch r w \<rho> = Some \<rho>' \<Longrightarrow> \<rho> \<subseteq>\<^sub>m \<rho>'\<close>
  by (induction r w \<rho> rule: rmatch.induct)
     (auto simp: map_le_def split: if_split_asm option.split_asm)

lemma map_le_upd_None: \<open>m a = None \<Longrightarrow> m \<subseteq>\<^sub>m m(a \<mapsto> w)\<close>
  by (auto simp: map_le_def dom_def)

lemma map_le_SomeD: \<open>m \<subseteq>\<^sub>m m' \<Longrightarrow> m a = Some y \<Longrightarrow> m' a = Some y\<close>
  by (auto simp: map_le_def dom_def)

lemma tmatch_le:
  \<open>tmatch t w (\<theta>, \<rho>) = Some (\<theta>', \<rho>') \<Longrightarrow> \<theta> \<subseteq>\<^sub>m \<theta>' \<and> \<rho> \<subseteq>\<^sub>m \<rho>'\<close>
  and tmatchs_le: \<open>tmatchs ts ws (\<theta>, \<rho>) = Some (\<theta>', \<rho>') \<Longrightarrow> \<theta> \<subseteq>\<^sub>m \<theta>' \<and> \<rho> \<subseteq>\<^sub>m \<rho>'\<close>
proof (induction t w \<open>(\<theta>, \<rho>)\<close> and ts ws \<open>(\<theta>, \<rho>)\<close>
       arbitrary: \<theta> \<rho> \<theta>' \<rho>' and \<theta> \<rho> \<theta>' \<rho>' rule: tmatch_induct)
  case (tmatch_TEv l s t l' s' w \<theta> \<rho> \<theta>' \<rho>')
  from tmatch_TEv.prems obtain \<theta>\<^sub>1 \<rho>\<^sub>1 \<theta>\<^sub>2 \<rho>\<^sub>2 where
    m\<^sub>1: \<open>tmatch l l' (\<theta>, \<rho>) = Some (\<theta>\<^sub>1, \<rho>\<^sub>1)\<close> and
    m\<^sub>2: \<open>tmatch s s' (\<theta>\<^sub>1, \<rho>\<^sub>1) = Some (\<theta>\<^sub>2, \<rho>\<^sub>2)\<close> and
    m\<^sub>3: \<open>tmatch t w (\<theta>\<^sub>2, \<rho>\<^sub>2) = Some (\<theta>', \<rho>')\<close>
    by (auto elim!: obind_SomeE split: prod.split_asm)
  show ?case using tmatch_TEv.hyps m\<^sub>1 m\<^sub>2 m\<^sub>3 by (blast intro: map_le_trans)
next
  case (tmatch_TAct l K e t l' K' f w \<theta> \<rho> \<theta>' \<rho>')
  from tmatch_TAct.prems obtain \<theta>\<^sub>1 \<rho>\<^sub>1 \<rho>\<^sub>2 where
    m\<^sub>1: \<open>tmatch l l' (\<theta>, \<rho>) = Some (\<theta>\<^sub>1, \<rho>\<^sub>1)\<close> and
    m\<^sub>2: \<open>rmatch e f \<rho>\<^sub>1 = Some \<rho>\<^sub>2\<close> and
    m\<^sub>3: \<open>tmatch t w (\<theta>\<^sub>1, \<rho>\<^sub>2) = Some (\<theta>', \<rho>')\<close>
    by (auto elim!: obind_SomeE split: prod.split_asm if_split_asm)
  show ?case using tmatch_TAct.hyps tmatch_TAct.prems m\<^sub>1 m\<^sub>2 m\<^sub>3 rmatch_le[OF m\<^sub>2]
    by (auto split: if_split_asm intro: map_le_trans)
qed (auto elim!: obind_SomeE
          split: if_split_asm option.split_asm prod.split_asm,
     ((blast intro: map_le_refl map_le_upd_None map_le_trans dest: rmatch_le)+)?)  (* ~6s *)

text \<open>Soundness, in extension-stable form: a successful match makes the
  pattern instantiate to the target under any extension of the final
  bindings:\<close>

lemma rmatch_sound:
  \<open>rmatch r w \<rho> = Some \<rho>' \<Longrightarrow> \<rho>' \<subseteq>\<^sub>m \<rho>'' \<Longrightarrow> brsubst (mk_brsub \<rho>'') r = w\<close>
proof (induction r w \<rho> arbitrary: \<rho>' rule: rmatch.induct)
qed (auto simp: mk_brsub_def map_le_def dom_def
     split: if_split_asm option.split_asm option.split)

lemma tmatch_sound:
  \<open>tmatch t w (\<theta>, \<rho>) = Some (\<theta>', \<rho>') \<Longrightarrow> \<theta>' \<subseteq>\<^sub>m \<theta>'' \<Longrightarrow> \<rho>' \<subseteq>\<^sub>m \<rho>'' \<Longrightarrow>
     bsubst (mk_btsub \<theta>'') (mk_brsub \<rho>'') t = w\<close>
  and tmatchs_sound:
  \<open>tmatchs ts ws (\<theta>, \<rho>) = Some (\<theta>', \<rho>') \<Longrightarrow> \<theta>' \<subseteq>\<^sub>m \<theta>'' \<Longrightarrow> \<rho>' \<subseteq>\<^sub>m \<rho>'' \<Longrightarrow>
     map (bsubst (mk_btsub \<theta>'') (mk_brsub \<rho>'')) ts = ws\<close>
proof (induction t w \<open>(\<theta>, \<rho>)\<close> and ts ws \<open>(\<theta>, \<rho>)\<close>
       arbitrary: \<theta> \<rho> \<theta>' \<rho>' and \<theta> \<rho> \<theta>' \<rho>' rule: tmatch_induct)
  case (tmatch_TB a w \<theta> \<rho> \<theta>' \<rho>')
  then have \<open>\<theta>' a = Some w\<close> by (auto split: option.split_asm if_split_asm)
  then have \<open>\<theta>'' a = Some w\<close> using \<open>\<theta>' \<subseteq>\<^sub>m \<theta>''\<close> map_le_SomeD by fast
  then show ?case by (simp add: mk_btsub_def)
next
  case (tmatch_TFn t\<^sub>1 e t\<^sub>2 w\<^sub>1 f w\<^sub>2 \<theta> \<rho> \<theta>' \<rho>')
  note le = \<open>\<theta>' \<subseteq>\<^sub>m \<theta>''\<close> \<open>\<rho>' \<subseteq>\<^sub>m \<rho>''\<close>
  from tmatch_TFn.prems obtain \<theta>\<^sub>1 \<rho>\<^sub>1 \<rho>\<^sub>2 where
    m\<^sub>1: \<open>tmatch t\<^sub>1 w\<^sub>1 (\<theta>, \<rho>) = Some (\<theta>\<^sub>1, \<rho>\<^sub>1)\<close> and
    m\<^sub>2: \<open>rmatch e f \<rho>\<^sub>1 = Some \<rho>\<^sub>2\<close> and
    m\<^sub>3: \<open>tmatch t\<^sub>2 w\<^sub>2 (\<theta>\<^sub>1, \<rho>\<^sub>2) = Some (\<theta>', \<rho>')\<close>
    by (auto elim!: obind_SomeE split: prod.split_asm)
  have le\<^sub>2: \<open>\<theta>\<^sub>1 \<subseteq>\<^sub>m \<theta>''\<close> \<open>\<rho>\<^sub>2 \<subseteq>\<^sub>m \<rho>''\<close>
    using tmatch_le[OF m\<^sub>3] le map_le_trans by blast+
  have le\<^sub>1: \<open>\<theta>\<^sub>1 \<subseteq>\<^sub>m \<theta>''\<close> \<open>\<rho>\<^sub>1 \<subseteq>\<^sub>m \<rho>''\<close>
    using rmatch_le[OF m\<^sub>2] le\<^sub>2 map_le_trans by blast+
  have \<open>bsubst (mk_btsub \<theta>'') (mk_brsub \<rho>'') t\<^sub>1 = w\<^sub>1\<close>
    using m\<^sub>1 le\<^sub>1 by (rule tmatch_TFn.hyps)
  moreover have \<open>bsubst (mk_btsub \<theta>'') (mk_brsub \<rho>'') t\<^sub>2 = w\<^sub>2\<close>
    using m\<^sub>1 refl m\<^sub>2 m\<^sub>3 le by (rule tmatch_TFn.hyps)
  ultimately show ?case using rmatch_sound[OF m\<^sub>2 le\<^sub>2(2)] by simp
next
  case (tmatch_TDep i sg T e t i' sg' T' f w \<theta> \<rho> \<theta>' \<rho>')
  note le = \<open>\<theta>' \<subseteq>\<^sub>m \<theta>''\<close> \<open>\<rho>' \<subseteq>\<^sub>m \<rho>''\<close>
  from tmatch_TDep.prems obtain \<rho>\<^sub>1 where
    eq: \<open>i = i'\<close> \<open>sg = sg'\<close> \<open>T = T'\<close> and
    m\<^sub>1: \<open>rmatch e f \<rho> = Some \<rho>\<^sub>1\<close> and
    m\<^sub>2: \<open>tmatch t w (\<theta>, \<rho>\<^sub>1) = Some (\<theta>', \<rho>')\<close>
    by (auto elim!: obind_SomeE split: if_split_asm)
  have le\<^sub>1: \<open>\<rho>\<^sub>1 \<subseteq>\<^sub>m \<rho>''\<close>
    using tmatch_le[OF m\<^sub>2] le map_le_trans by blast
  have \<open>bsubst (mk_btsub \<theta>'') (mk_brsub \<rho>'') t = w\<close>
    using conjI[OF eq(1) conjI[OF eq(2,3)]] m\<^sub>1 m\<^sub>2 le by (rule tmatch_TDep.hyps)
  then show ?case using eq rmatch_sound[OF m\<^sub>1 le\<^sub>1] by simp
next
  case (tmatch_TApp t\<^sub>1 t\<^sub>2 w\<^sub>1 w\<^sub>2 \<theta> \<rho> \<theta>' \<rho>')
  note le = \<open>\<theta>' \<subseteq>\<^sub>m \<theta>''\<close> \<open>\<rho>' \<subseteq>\<^sub>m \<rho>''\<close>
  from tmatch_TApp.prems obtain \<theta>\<^sub>1 \<rho>\<^sub>1 where
    m\<^sub>1: \<open>tmatch t\<^sub>1 w\<^sub>1 (\<theta>, \<rho>) = Some (\<theta>\<^sub>1, \<rho>\<^sub>1)\<close> and
    m\<^sub>2: \<open>tmatch t\<^sub>2 w\<^sub>2 (\<theta>\<^sub>1, \<rho>\<^sub>1) = Some (\<theta>', \<rho>')\<close>
    by (auto elim!: obind_SomeE split: prod.split_asm)
  have le\<^sub>1: \<open>\<theta>\<^sub>1 \<subseteq>\<^sub>m \<theta>''\<close> \<open>\<rho>\<^sub>1 \<subseteq>\<^sub>m \<rho>''\<close>
    using tmatch_le[OF m\<^sub>2] le map_le_trans by blast+
  have \<open>bsubst (mk_btsub \<theta>'') (mk_brsub \<rho>'') t\<^sub>1 = w\<^sub>1\<close>
    using m\<^sub>1 le\<^sub>1 by (rule tmatch_TApp.hyps)
  moreover have \<open>bsubst (mk_btsub \<theta>'') (mk_brsub \<rho>'') t\<^sub>2 = w\<^sub>2\<close>
    using m\<^sub>1 m\<^sub>2 le by (rule tmatch_TApp.hyps)
  ultimately show ?case by simp
next
  case (tmatch_TEv l s t l' s' w \<theta> \<rho> \<theta>' \<rho>')
  note le = \<open>\<theta>' \<subseteq>\<^sub>m \<theta>''\<close> \<open>\<rho>' \<subseteq>\<^sub>m \<rho>''\<close>
  from tmatch_TEv.prems obtain \<theta>\<^sub>1 \<rho>\<^sub>1 \<theta>\<^sub>2 \<rho>\<^sub>2 where
    m\<^sub>1: \<open>tmatch l l' (\<theta>, \<rho>) = Some (\<theta>\<^sub>1, \<rho>\<^sub>1)\<close> and
    m\<^sub>2: \<open>tmatch s s' (\<theta>\<^sub>1, \<rho>\<^sub>1) = Some (\<theta>\<^sub>2, \<rho>\<^sub>2)\<close> and
    m\<^sub>3: \<open>tmatch t w (\<theta>\<^sub>2, \<rho>\<^sub>2) = Some (\<theta>', \<rho>')\<close>
    by (auto elim!: obind_SomeE split: prod.split_asm)
  have le\<^sub>2: \<open>\<theta>\<^sub>2 \<subseteq>\<^sub>m \<theta>''\<close> \<open>\<rho>\<^sub>2 \<subseteq>\<^sub>m \<rho>''\<close>
    using tmatch_le[OF m\<^sub>3] le map_le_trans by blast+
  have le\<^sub>1: \<open>\<theta>\<^sub>1 \<subseteq>\<^sub>m \<theta>''\<close> \<open>\<rho>\<^sub>1 \<subseteq>\<^sub>m \<rho>''\<close>
    using tmatch_le[OF m\<^sub>2] le\<^sub>2 map_le_trans by blast+
  have \<open>bsubst (mk_btsub \<theta>'') (mk_brsub \<rho>'') l = l'\<close>
    using m\<^sub>1 le\<^sub>1 by (rule tmatch_TEv.hyps)
  moreover have \<open>bsubst (mk_btsub \<theta>'') (mk_brsub \<rho>'') s = s'\<close>
    using m\<^sub>1 m\<^sub>2 le\<^sub>2 by (rule tmatch_TEv.hyps)
  moreover have \<open>bsubst (mk_btsub \<theta>'') (mk_brsub \<rho>'') t = w\<close>
    using m\<^sub>1 m\<^sub>2 m\<^sub>3 le by (rule tmatch_TEv.hyps)
  ultimately show ?case by simp
next
  case (tmatch_TAct l K e t l' K' f w \<theta> \<rho> \<theta>' \<rho>')
  note le = \<open>\<theta>' \<subseteq>\<^sub>m \<theta>''\<close> \<open>\<rho>' \<subseteq>\<^sub>m \<rho>''\<close>
  from tmatch_TAct.prems obtain \<theta>\<^sub>1 \<rho>\<^sub>1 \<rho>\<^sub>2 where
    eq: \<open>K = K'\<close> and
    m\<^sub>1: \<open>tmatch l l' (\<theta>, \<rho>) = Some (\<theta>\<^sub>1, \<rho>\<^sub>1)\<close> and
    m\<^sub>2: \<open>rmatch e f \<rho>\<^sub>1 = Some \<rho>\<^sub>2\<close> and
    m\<^sub>3: \<open>tmatch t w (\<theta>\<^sub>1, \<rho>\<^sub>2) = Some (\<theta>', \<rho>')\<close>
    by (auto elim!: obind_SomeE split: prod.split_asm if_split_asm)
  have le\<^sub>2: \<open>\<theta>\<^sub>1 \<subseteq>\<^sub>m \<theta>''\<close> \<open>\<rho>\<^sub>2 \<subseteq>\<^sub>m \<rho>''\<close>
    using tmatch_le[OF m\<^sub>3] le map_le_trans by blast+
  have le\<^sub>1: \<open>\<rho>\<^sub>1 \<subseteq>\<^sub>m \<rho>''\<close>
    using rmatch_le[OF m\<^sub>2] le\<^sub>2 map_le_trans by blast
  have \<open>bsubst (mk_btsub \<theta>'') (mk_brsub \<rho>'') l = l'\<close>
    using eq m\<^sub>1 le\<^sub>2(1) le\<^sub>1 by (rule tmatch_TAct.hyps)
  moreover have \<open>bsubst (mk_btsub \<theta>'') (mk_brsub \<rho>'') t = w\<close>
    using eq m\<^sub>1 refl m\<^sub>2 m\<^sub>3 le by (rule tmatch_TAct.hyps)
  ultimately show ?case using eq rmatch_sound[OF m\<^sub>2 le\<^sub>2(2)] by simp
next
  case (tmatch_TRCons l t r l' w r' \<theta> \<rho> \<theta>' \<rho>')
  note le = \<open>\<theta>' \<subseteq>\<^sub>m \<theta>''\<close> \<open>\<rho>' \<subseteq>\<^sub>m \<rho>''\<close>
  from tmatch_TRCons.prems obtain \<theta>\<^sub>1 \<rho>\<^sub>1 where
    eq: \<open>l = l'\<close> and
    m\<^sub>1: \<open>tmatch t w (\<theta>, \<rho>) = Some (\<theta>\<^sub>1, \<rho>\<^sub>1)\<close> and
    m\<^sub>2: \<open>tmatch r r' (\<theta>\<^sub>1, \<rho>\<^sub>1) = Some (\<theta>', \<rho>')\<close>
    by (auto elim!: obind_SomeE split: prod.split_asm if_split_asm)
  have le\<^sub>1: \<open>\<theta>\<^sub>1 \<subseteq>\<^sub>m \<theta>''\<close> \<open>\<rho>\<^sub>1 \<subseteq>\<^sub>m \<rho>''\<close>
    using tmatch_le[OF m\<^sub>2] le map_le_trans by blast+
  have \<open>bsubst (mk_btsub \<theta>'') (mk_brsub \<rho>'') t = w\<close>
    using eq m\<^sub>1 le\<^sub>1 by (rule tmatch_TRCons.hyps)
  moreover have \<open>bsubst (mk_btsub \<theta>'') (mk_brsub \<rho>'') r = r'\<close>
    using eq m\<^sub>1 m\<^sub>2 le by (rule tmatch_TRCons.hyps)
  ultimately show ?case using eq by simp
next
  case (tmatchs_Cons t ts w ws \<theta> \<rho> \<theta>' \<rho>')
  note le = \<open>\<theta>' \<subseteq>\<^sub>m \<theta>''\<close> \<open>\<rho>' \<subseteq>\<^sub>m \<rho>''\<close>
  from tmatchs_Cons.prems obtain \<theta>\<^sub>1 \<rho>\<^sub>1 where
    m\<^sub>1: \<open>tmatch t w (\<theta>, \<rho>) = Some (\<theta>\<^sub>1, \<rho>\<^sub>1)\<close> and
    m\<^sub>2: \<open>tmatchs ts ws (\<theta>\<^sub>1, \<rho>\<^sub>1) = Some (\<theta>', \<rho>')\<close>
    by (auto elim!: obind_SomeE split: prod.split_asm)
  have le\<^sub>1: \<open>\<theta>\<^sub>1 \<subseteq>\<^sub>m \<theta>''\<close> \<open>\<rho>\<^sub>1 \<subseteq>\<^sub>m \<rho>''\<close>
    using tmatchs_le[OF m\<^sub>2] le map_le_trans by blast+
  have \<open>bsubst (mk_btsub \<theta>'') (mk_brsub \<rho>'') t = w\<close>
    using m\<^sub>1 le\<^sub>1 by (rule tmatchs_Cons.hyps)
  moreover have \<open>map (bsubst (mk_btsub \<theta>'') (mk_brsub \<rho>'')) ts = ws\<close>
    using m\<^sub>1 m\<^sub>2 le by (rule tmatchs_Cons.hyps)
  ultimately show ?case by simp
qed (auto split: if_split_asm option.split_asm)

text \<open>A partial map agrees with a total one where it is defined.\<close>

abbreviation agrees :: \<open>('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close> where
  \<open>agrees m g \<equiv> \<forall>a y. m a = Some y \<longrightarrow> g a = y\<close>

text \<open>Completeness: any \<open>\<succeq>\<close>-witness is found by the matcher, from any
  accumulator consistent with the witness:\<close>

lemma rmatch_complete:
  \<open>brsubst g r = w \<Longrightarrow> agrees \<rho> g \<Longrightarrow>
   \<exists>\<rho>'. rmatch r w \<rho> = Some \<rho>' \<and> agrees \<rho>' g\<close>
  by (induction r arbitrary: w \<rho>) (auto split: option.split)

lemma tmatchs_complete_pre:
  \<open>(\<forall>t \<in> set ts. \<forall>w \<theta> \<rho>. bsubst gt gr t = w \<longrightarrow> agrees \<theta> gt \<longrightarrow> agrees \<rho> gr \<longrightarrow>
       (\<exists>\<theta>' \<rho>'. tmatch t w (\<theta>, \<rho>) = Some (\<theta>', \<rho>') \<and> agrees \<theta>' gt \<and> agrees \<rho>' gr)) \<Longrightarrow>
   map (bsubst gt gr) ts = ws \<Longrightarrow> agrees \<theta> gt \<Longrightarrow> agrees \<rho> gr \<Longrightarrow>
   \<exists>\<theta>' \<rho>'. tmatchs ts ws (\<theta>, \<rho>) = Some (\<theta>', \<rho>') \<and> agrees \<theta>' gt \<and> agrees \<rho>' gr\<close>
proof (induction ts arbitrary: ws \<theta> \<rho>)
  case (Cons t ts)
  note ok = \<open>agrees \<theta> gt\<close> \<open>agrees \<rho> gr\<close>
  from Cons.prems have \<open>\<forall>w \<theta> \<rho>. bsubst gt gr t = w \<longrightarrow> agrees \<theta> gt \<longrightarrow> agrees \<rho> gr \<longrightarrow>
      (\<exists>\<theta>' \<rho>'. tmatch t w (\<theta>, \<rho>) = Some (\<theta>', \<rho>') \<and> agrees \<theta>' gt \<and> agrees \<rho>' gr)\<close>
    by simp
  with ok obtain \<theta>\<^sub>1 \<rho>\<^sub>1 where
    m\<^sub>1: \<open>tmatch t (bsubst gt gr t) (\<theta>, \<rho>) = Some (\<theta>\<^sub>1, \<rho>\<^sub>1)\<close> and
    c\<^sub>1: \<open>agrees \<theta>\<^sub>1 gt\<close> \<open>agrees \<rho>\<^sub>1 gr\<close>
    by blast
  from Cons.IH[of \<open>map (bsubst gt gr) ts\<close> \<theta>\<^sub>1 \<rho>\<^sub>1] Cons.prems c\<^sub>1
  obtain \<theta>\<^sub>2 \<rho>\<^sub>2 where
    m\<^sub>2: \<open>tmatchs ts (map (bsubst gt gr) ts) (\<theta>\<^sub>1, \<rho>\<^sub>1) = Some (\<theta>\<^sub>2, \<rho>\<^sub>2)\<close> and
    c\<^sub>2: \<open>agrees \<theta>\<^sub>2 gt\<close> \<open>agrees \<rho>\<^sub>2 gr\<close>
    by auto
  show ?case using \<open>map (bsubst gt gr) (t # ts) = ws\<close>[symmetric] m\<^sub>1 m\<^sub>2 c\<^sub>2 by auto
qed auto

lemma tmatch_complete:
  \<open>bsubst gt gr t = w \<Longrightarrow> agrees \<theta> gt \<Longrightarrow> agrees \<rho> gr \<Longrightarrow>
   \<exists>\<theta>' \<rho>'. tmatch t w (\<theta>, \<rho>) = Some (\<theta>', \<rho>') \<and> agrees \<theta>' gt \<and> agrees \<rho>' gr\<close>
proof (induction t arbitrary: w \<theta> \<rho>)
  case (TB a)
  then show ?case by (auto split: option.split)
next
  case (TC c ts)
  note ok = \<open>agrees \<theta> gt\<close> \<open>agrees \<rho> gr\<close>
  have el: \<open>\<forall>t \<in> set ts. \<forall>w \<theta> \<rho>. bsubst gt gr t = w \<longrightarrow> agrees \<theta> gt \<longrightarrow> agrees \<rho> gr \<longrightarrow>
       (\<exists>\<theta>' \<rho>'. tmatch t w (\<theta>, \<rho>) = Some (\<theta>', \<rho>') \<and> agrees \<theta>' gt \<and> agrees \<rho>' gr)\<close>
    using TC.IH by blast
  from tmatchs_complete_pre[OF el _ ok, of \<open>map (bsubst gt gr) ts\<close>]
  obtain \<theta>' \<rho>' where
    \<open>tmatchs ts (map (bsubst gt gr) ts) (\<theta>, \<rho>) = Some (\<theta>', \<rho>')\<close>
    \<open>agrees \<theta>' gt\<close> \<open>agrees \<rho>' gr\<close>
    by auto
  then show ?case using TC.prems by auto
next
  case (TFn t\<^sub>1 e t\<^sub>2)
  from TFn.prems obtain \<theta>\<^sub>1 \<rho>\<^sub>1 where
    m\<^sub>1: \<open>tmatch t\<^sub>1 (bsubst gt gr t\<^sub>1) (\<theta>, \<rho>) = Some (\<theta>\<^sub>1, \<rho>\<^sub>1)\<close> and
    c\<^sub>1t: \<open>agrees \<theta>\<^sub>1 gt\<close> and c\<^sub>1r: \<open>agrees \<rho>\<^sub>1 gr\<close>
    using TFn.IH[of \<open>bsubst gt gr t\<^sub>1\<close> \<theta> \<rho>] by auto
  from rmatch_complete[of gr e \<open>brsubst gr e\<close> \<rho>\<^sub>1] c\<^sub>1r obtain \<rho>\<^sub>2 where
    m\<^sub>2: \<open>rmatch e (brsubst gr e) \<rho>\<^sub>1 = Some \<rho>\<^sub>2\<close> and
    c\<^sub>2r: \<open>agrees \<rho>\<^sub>2 gr\<close>
    by auto
  from TFn.IH[of \<open>bsubst gt gr t\<^sub>2\<close> \<theta>\<^sub>1 \<rho>\<^sub>2] c\<^sub>1t c\<^sub>2r obtain \<theta>\<^sub>3 \<rho>\<^sub>3 where
    m\<^sub>3: \<open>tmatch t\<^sub>2 (bsubst gt gr t\<^sub>2) (\<theta>\<^sub>1, \<rho>\<^sub>2) = Some (\<theta>\<^sub>3, \<rho>\<^sub>3)\<close> and
    c\<^sub>3: \<open>agrees \<theta>\<^sub>3 gt\<close> \<open>agrees \<rho>\<^sub>3 gr\<close>
    by auto
  show ?case using TFn.prems m\<^sub>1 m\<^sub>2 m\<^sub>3 c\<^sub>3 by auto
next
  case (TDep i sg T e t)
  from rmatch_complete[of gr e \<open>brsubst gr e\<close> \<rho>] TDep.prems obtain \<rho>\<^sub>1 where
    m\<^sub>1: \<open>rmatch e (brsubst gr e) \<rho> = Some \<rho>\<^sub>1\<close> and
    c\<^sub>1: \<open>agrees \<rho>\<^sub>1 gr\<close>
    by auto
  from TDep.IH[of \<open>bsubst gt gr t\<close> \<theta> \<rho>\<^sub>1] TDep.prems c\<^sub>1 obtain \<theta>\<^sub>2 \<rho>\<^sub>2 where
    m\<^sub>2: \<open>tmatch t (bsubst gt gr t) (\<theta>, \<rho>\<^sub>1) = Some (\<theta>\<^sub>2, \<rho>\<^sub>2)\<close> and
    c\<^sub>2: \<open>agrees \<theta>\<^sub>2 gt\<close> \<open>agrees \<rho>\<^sub>2 gr\<close>
    by auto
  show ?case using TDep.prems m\<^sub>1 m\<^sub>2 c\<^sub>2 by auto
next
  case (TApp t\<^sub>1 t\<^sub>2)
  from TApp.prems obtain \<theta>\<^sub>1 \<rho>\<^sub>1 where
    m\<^sub>1: \<open>tmatch t\<^sub>1 (bsubst gt gr t\<^sub>1) (\<theta>, \<rho>) = Some (\<theta>\<^sub>1, \<rho>\<^sub>1)\<close> and
    c\<^sub>1: \<open>agrees \<theta>\<^sub>1 gt\<close> \<open>agrees \<rho>\<^sub>1 gr\<close>
    using TApp.IH[of \<open>bsubst gt gr t\<^sub>1\<close> \<theta> \<rho>] by auto
  from TApp.IH[of \<open>bsubst gt gr t\<^sub>2\<close> \<theta>\<^sub>1 \<rho>\<^sub>1] TApp.prems c\<^sub>1 obtain \<theta>\<^sub>2 \<rho>\<^sub>2 where
    m\<^sub>2: \<open>tmatch t\<^sub>2 (bsubst gt gr t\<^sub>2) (\<theta>\<^sub>1, \<rho>\<^sub>1) = Some (\<theta>\<^sub>2, \<rho>\<^sub>2)\<close> and
    c\<^sub>2: \<open>agrees \<theta>\<^sub>2 gt\<close> \<open>agrees \<rho>\<^sub>2 gr\<close>
    by auto
  show ?case using TApp.prems m\<^sub>1 m\<^sub>2 c\<^sub>2 by auto
next
  case (TEv l s t)
  from TEv.prems obtain \<theta>\<^sub>1 \<rho>\<^sub>1 where
    m\<^sub>1: \<open>tmatch l (bsubst gt gr l) (\<theta>, \<rho>) = Some (\<theta>\<^sub>1, \<rho>\<^sub>1)\<close> and
    c\<^sub>1: \<open>agrees \<theta>\<^sub>1 gt\<close> \<open>agrees \<rho>\<^sub>1 gr\<close>
    using TEv.IH[of \<open>bsubst gt gr l\<close> \<theta> \<rho>] by auto
  from TEv.IH[of \<open>bsubst gt gr s\<close> \<theta>\<^sub>1 \<rho>\<^sub>1] TEv.prems c\<^sub>1 obtain \<theta>\<^sub>2 \<rho>\<^sub>2 where
    m\<^sub>2: \<open>tmatch s (bsubst gt gr s) (\<theta>\<^sub>1, \<rho>\<^sub>1) = Some (\<theta>\<^sub>2, \<rho>\<^sub>2)\<close> and
    c\<^sub>2: \<open>agrees \<theta>\<^sub>2 gt\<close> \<open>agrees \<rho>\<^sub>2 gr\<close>
    by auto
  from TEv.IH[of \<open>bsubst gt gr t\<close> \<theta>\<^sub>2 \<rho>\<^sub>2] TEv.prems c\<^sub>2 obtain \<theta>\<^sub>3 \<rho>\<^sub>3 where
    m\<^sub>3: \<open>tmatch t (bsubst gt gr t) (\<theta>\<^sub>2, \<rho>\<^sub>2) = Some (\<theta>\<^sub>3, \<rho>\<^sub>3)\<close> and
    c\<^sub>3: \<open>agrees \<theta>\<^sub>3 gt\<close> \<open>agrees \<rho>\<^sub>3 gr\<close>
    by auto
  show ?case using TEv.prems m\<^sub>1 m\<^sub>2 m\<^sub>3 c\<^sub>3 by auto
next
  case (TAct l K e t)
  from TAct.prems obtain \<theta>\<^sub>1 \<rho>\<^sub>1 where
    m\<^sub>1: \<open>tmatch l (bsubst gt gr l) (\<theta>, \<rho>) = Some (\<theta>\<^sub>1, \<rho>\<^sub>1)\<close> and
    c\<^sub>1: \<open>agrees \<theta>\<^sub>1 gt\<close> \<open>agrees \<rho>\<^sub>1 gr\<close>
    using TAct.IH[of \<open>bsubst gt gr l\<close> \<theta> \<rho>] by auto
  from rmatch_complete[of gr e \<open>brsubst gr e\<close> \<rho>\<^sub>1] c\<^sub>1 obtain \<rho>\<^sub>2 where
    m\<^sub>2: \<open>rmatch e (brsubst gr e) \<rho>\<^sub>1 = Some \<rho>\<^sub>2\<close> and
    c\<^sub>2: \<open>agrees \<rho>\<^sub>2 gr\<close>
    by auto
  from TAct.IH[of \<open>bsubst gt gr t\<close> \<theta>\<^sub>1 \<rho>\<^sub>2] TAct.prems c\<^sub>1 c\<^sub>2 obtain \<theta>\<^sub>3 \<rho>\<^sub>3 where
    m\<^sub>3: \<open>tmatch t (bsubst gt gr t) (\<theta>\<^sub>1, \<rho>\<^sub>2) = Some (\<theta>\<^sub>3, \<rho>\<^sub>3)\<close> and
    c\<^sub>3: \<open>agrees \<theta>\<^sub>3 gt\<close> \<open>agrees \<rho>\<^sub>3 gr\<close>
    by auto
  show ?case using TAct.prems m\<^sub>1 m\<^sub>2 m\<^sub>3 c\<^sub>3 by auto
next
  case (TRCons l t r)
  from TRCons.prems obtain \<theta>\<^sub>1 \<rho>\<^sub>1 where
    m\<^sub>1: \<open>tmatch t (bsubst gt gr t) (\<theta>, \<rho>) = Some (\<theta>\<^sub>1, \<rho>\<^sub>1)\<close> and
    c\<^sub>1: \<open>agrees \<theta>\<^sub>1 gt\<close> \<open>agrees \<rho>\<^sub>1 gr\<close>
    using TRCons.IH[of \<open>bsubst gt gr t\<close> \<theta> \<rho>] by auto
  from TRCons.IH[of \<open>bsubst gt gr r\<close> \<theta>\<^sub>1 \<rho>\<^sub>1] TRCons.prems c\<^sub>1 obtain \<theta>\<^sub>2 \<rho>\<^sub>2 where
    m\<^sub>2: \<open>tmatch r (bsubst gt gr r) (\<theta>\<^sub>1, \<rho>\<^sub>1) = Some (\<theta>\<^sub>2, \<rho>\<^sub>2)\<close> and
    c\<^sub>2: \<open>agrees \<theta>\<^sub>2 gt\<close> \<open>agrees \<rho>\<^sub>2 gr\<close>
    by auto
  show ?case using TRCons.prems m\<^sub>1 m\<^sub>2 c\<^sub>2 by auto
qed auto

fun imatch :: \<open>scheme \<Rightarrow> kty \<Rightarrow> bool\<close> where
  \<open>imatch (Sch t) \<tau> =
     (case tmatch t \<tau> (Map.empty, Map.empty) of
        None \<Rightarrow> False
      | Some (\<theta>', \<rho>') \<Rightarrow>
          btv \<tau> = {} \<and> brv \<tau> = {} \<and>
          (\<forall>a \<in> btv t. case \<theta>' a of Some u \<Rightarrow> taclosed u | None \<Rightarrow> True))\<close>
| \<open>imatch (Mono t) \<tau> \<longleftrightarrow> \<tau> = t\<close>

theorem imatch_sinst: \<open>imatch \<sigma> \<tau> \<longleftrightarrow> \<sigma> \<succeq> \<tau>\<close>
proof (cases \<sigma>)
  case (Sch t)
  show ?thesis
  proof
    assume \<open>imatch \<sigma> \<tau>\<close>
    then obtain \<theta>' \<rho>' where m: \<open>tmatch t \<tau> (Map.empty, Map.empty) = Some (\<theta>', \<rho>')\<close>
      and bf: \<open>btv \<tau> = {}\<close> \<open>brv \<tau> = {}\<close>
      and im: \<open>\<forall>a \<in> btv t. case \<theta>' a of Some u \<Rightarrow> taclosed u | None \<Rightarrow> True\<close>
      unfolding Sch by (auto split: option.splits)
    have e: \<open>bsubst (mk_btsub \<theta>') (mk_brsub \<rho>') t = \<tau>\<close>
      using tmatch_sound[OF m map_le_refl map_le_refl] .
    define \<theta>\<^sub>c where \<open>\<theta>\<^sub>c = (\<lambda>a. if a \<in> btv t then mk_btsub \<theta>' a else TB a)\<close>
    have \<open>bsubst \<theta>\<^sub>c (mk_brsub \<rho>') t = \<tau>\<close>
      unfolding e[symmetric] by (rule bsubst_cong_eq) (simp_all add: \<theta>\<^sub>c_def)
    moreover have \<open>taclosed (\<theta>\<^sub>c a)\<close> for a
    proof (cases \<open>a \<in> btv t\<close>)
      case True
      show ?thesis
      proof (cases \<open>\<theta>' a\<close>)
        case (Some u)
        then show ?thesis using True bspec[OF im True] by (simp add: \<theta>\<^sub>c_def mk_btsub_def)
      qed (simp add: \<theta>\<^sub>c_def mk_btsub_def)
    qed (simp add: \<theta>\<^sub>c_def)
    ultimately show \<open>\<sigma> \<succeq> \<tau>\<close> using bf unfolding Sch sinst_Sch by blast
  next
    assume \<open>\<sigma> \<succeq> \<tau>\<close>
    then obtain gt gr where \<open>bsubst gt gr t = \<tau>\<close> and bf: \<open>btv \<tau> = {}\<close> \<open>brv \<tau> = {}\<close>
      and im: \<open>\<forall>a. taclosed (gt a)\<close> unfolding Sch sinst_Sch by blast
    then show \<open>imatch \<sigma> \<tau>\<close>
      using tmatch_complete[of gt gr t \<tau> Map.empty Map.empty] im unfolding Sch
      by (fastforce split: option.splits)
  qed
qed simp

lemma imatch_sinst'[code_unfold]: \<open>\<sigma> \<succeq> \<tau> \<longleftrightarrow> imatch \<sigma> \<tau>\<close>
  by (simp add: imatch_sinst)

end
