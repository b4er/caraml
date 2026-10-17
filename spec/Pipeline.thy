theory Pipeline
  imports
    Coinductive.Coinductive_List
begin

section \<open>The compiler specification\<close>

text \<open>The compiler stated abstractly: behaviours are compared by refinement
  up to running out of resources.

  A phase refines behaviour, a separate phase also commutes with linking. The
  locale \<^text>\<open>module_compiler\<close> composes the frontend, the type system,
  elaboration and the backend into the per-file theorem \<^text>\<open>module_correct\<close>.\<close>

subsection \<open>Observable behaviour and refinement\<close>

datatype 'ev outcome = Success | ResourceExhausted | FFI_error 'ev

datatype 'ev behaviour =
    Terminate \<open>'ev outcome\<close> \<open>'ev list\<close>
  | Diverge \<open>'ev llist\<close>
  | Fail

text \<open>The finite traces a behaviour is observed to produce up to some point:\<close>

primrec prefix_of :: \<open>'ev list \<Rightarrow> 'ev behaviour \<Rightarrow> bool\<close> where
  \<open>prefix_of xs (Terminate _ ys) \<longleftrightarrow> prefix xs ys\<close>
| \<open>prefix_of xs (Diverge ys) \<longleftrightarrow> lprefix (llist_of xs) ys\<close>
| \<open>prefix_of xs Fail \<longleftrightarrow> False\<close>

lemma prefix_of_trans: \<open>\<lbrakk>prefix xs\<^sub>1 xs\<^sub>2; prefix_of xs\<^sub>2 b\<rbrakk> \<Longrightarrow> prefix_of xs\<^sub>1 b\<close>
  by (cases b) (auto elim: lprefix_trans[of \<open>llist_of xs\<^sub>1\<close>, rotated])

text \<open>\<open>ext B\<close> adds running out of resources after every observed prefix:\<close>

definition ext :: \<open>'ev behaviour set \<Rightarrow> 'ev behaviour set\<close> where
  \<open>ext B = B \<union> {Terminate ResourceExhausted io | io. \<exists>b \<in> B. prefix_of io b}\<close>

lemma ext_mono: \<open>B \<subseteq> B' \<Longrightarrow> ext B \<subseteq> ext B'\<close>
  by (auto simp: ext_def)

lemma Fail_not_ext [intro]: \<open>Fail \<notin> B \<Longrightarrow> Fail \<notin> ext B\<close>
  by (simp add: ext_def)

lemma ext_idem [simp]: \<open>ext (ext B) = ext B\<close>
  by (fastforce intro: prefix_of_trans simp: ext_def)

text \<open>\<open>T \<sqsubseteq> S\<close>: every behaviour of \<open>T\<close> is one of \<open>S\<close> or runs out of resources
  after a prefix of one; a source that can fail allows anything.\<close>

definition refines :: \<open>'ev behaviour set \<Rightarrow> 'ev behaviour set \<Rightarrow> bool\<close> (infix \<open>\<sqsubseteq>\<close> 50) where
  \<open>T \<sqsubseteq> S \<longleftrightarrow> (Fail \<notin> S \<longrightarrow> T \<subseteq> ext S)\<close>

(*<*)
lemma refines_refl [intro!, simp]: \<open>T \<sqsubseteq> T\<close>
  by (auto simp: refines_def ext_def)

lemma refines_trans:
  assumes \<open>T \<sqsubseteq> M\<close> and \<open>M \<sqsubseteq> S\<close>
  shows \<open>T \<sqsubseteq> S\<close>
  using assms ext_mono[of M \<open>ext S\<close>] Fail_not_ext[of S] by (auto simp: refines_def)
(*>*)

text \<open>Refinement is reflexive and transitive:
  \<^item> @{thm [display] refines_refl}
  \<^item> @{thm [display] refines_trans}\<close>


subsection \<open>Language, linking, and contextual refinement\<close>

text \<open>A language sends a program to a set of behaviours (non-emptiness rules
  out a language that refines everything).\<close>

locale language =
  fixes sem :: \<open>'ffi \<Rightarrow> 'prog \<Rightarrow> 'ev behaviour set\<close>
  assumes sem_nonempty: \<open>sem ffi p \<noteq> {}\<close>

text \<open>A linkable language has a partial, associative linking operation, and
  the signature of a linked program joins those of its parts. A context
  \<^text>\<open>compatible\<close> with a signature has the imports that close a program of
  that signature, so linking succeeds.\<close>

locale linkable = language sem
  for sem :: \<open>'ffi \<Rightarrow> 'prog \<Rightarrow> 'ev behaviour set\<close> +
  fixes link :: \<open>'prog \<Rightarrow> 'prog \<Rightarrow> 'prog option\<close>
    and mod_sig :: \<open>'prog \<Rightarrow> 'sig\<close>
    and sig_join :: \<open>'sig \<Rightarrow> 'sig \<Rightarrow> 'sig\<close>
    and compatible :: \<open>'prog \<Rightarrow> 'sig \<Rightarrow> bool\<close>
  assumes link_assoc:
    \<open>link p q = Some pq \<Longrightarrow> link q r = Some qr \<Longrightarrow> link pq r = link p qr\<close>
  and link_sig:
    \<open>link p q = Some pq \<Longrightarrow> mod_sig pq = sig_join (mod_sig p) (mod_sig q)\<close>
  and link_total:
    \<open>compatible ctx (mod_sig p) \<Longrightarrow> \<exists>r. link ctx p = Some r\<close>
begin

text \<open>Contextual refinement: \<open>p\<close> refines \<open>q\<close> in every linking context compatible
  with their signature.\<close>

definition ctx_refines :: \<open>'prog \<Rightarrow> 'prog \<Rightarrow> bool\<close> (infix \<open>\<sqsubseteq>\<^sub>c\<close> 50) where
  \<open>p \<sqsubseteq>\<^sub>c q \<longleftrightarrow>
    mod_sig p = mod_sig q \<and>
    (\<forall>ctx p' q' ffi.
       compatible ctx (mod_sig q) \<longrightarrow>
       link ctx p = Some p' \<longrightarrow>
       link ctx q = Some q' \<longrightarrow>
       sem ffi p' \<sqsubseteq> sem ffi q')\<close>

(*<*)
lemma ctx_refines_refl [intro!, simp]: \<open>p \<sqsubseteq>\<^sub>c p\<close>
  by (auto simp: ctx_refines_def)

lemma ctx_refines_trans:
  assumes \<open>a \<sqsubseteq>\<^sub>c b\<close> and \<open>b \<sqsubseteq>\<^sub>c c\<close>
  shows \<open>a \<sqsubseteq>\<^sub>c c\<close>
  using assms link_total refines_trans[of \<open>sem _ _\<close> \<open>sem _ _\<close> \<open>sem _ _\<close>]
  unfolding ctx_refines_def
  by metis
(*>*)

text \<open>Contextual refinement is reflexive and transitive:
  \<^item> @{thm [display] ctx_refines_refl}
  \<^item> @{thm [display] ctx_refines_trans}\<close>

end


subsection \<open>Phase and separate compilation\<close>

text \<open>A phase translates between two languages under a configuration
  \<open>cfg\<close>. \<^text>\<open>compile_correct\<close> is a whole-program statement: a module
  without its imports can fail, so for it the assumption says nothing.
  \<^text>\<open>compile_link\<close> of \<^text>\<open>separate_phase\<close> carries it to the closed
  program obtained by linking.\<close>

locale phase =
  src: language sem\<^sub>S + tgt: language sem\<^sub>T
  for sem\<^sub>S :: \<open>'ffi \<Rightarrow> 's \<Rightarrow> 'ev behaviour set\<close>
    and sem\<^sub>T :: \<open>'ffi \<Rightarrow> 't \<Rightarrow> 'ev behaviour set\<close> +
  fixes cfg :: \<open>'c\<close>
    and compile :: \<open>'c \<Rightarrow> 's \<Rightarrow> 't option\<close>
  assumes compile_correct:
    \<open>compile cfg p = Some q \<Longrightarrow> sem\<^sub>T ffi q \<sqsubseteq> sem\<^sub>S ffi p\<close>

text \<open>Phases compose, under the pair of their configurations:\<close>

lemma phase_compose:
  assumes p\<^sub>1: \<open>phase sem\<^sub>1 sem\<^sub>2 c\<^sub>a f\<close> and p\<^sub>2: \<open>phase sem\<^sub>2 sem\<^sub>3 c\<^sub>b g\<close>
  shows \<open>phase sem\<^sub>1 sem\<^sub>3 (c\<^sub>a, c\<^sub>b) (\<lambda>(a, b) p. Option.bind (f a p) (g b))\<close>
proof -
  interpret p\<^sub>1: phase sem\<^sub>1 sem\<^sub>2 c\<^sub>a f by (rule p\<^sub>1)
  interpret p\<^sub>2: phase sem\<^sub>2 sem\<^sub>3 c\<^sub>b g by (rule p\<^sub>2)

  show ?thesis
  proof (unfold_locales, goal_cases _ _ Some)
    case (Some p q ffi)
    then obtain m where
      fm: \<open>f c\<^sub>a p = Some m\<close> and gm: \<open>g c\<^sub>b m = Some q\<close>
      by (auto split: Option.bind_split_asm)
    note correct = p\<^sub>2.compile_correct[OF gm] p\<^sub>1.compile_correct[OF fm]
    from refines_trans[OF correct] show ?case.
  qed (intro p\<^sub>1.src.sem_nonempty p\<^sub>2.tgt.sem_nonempty)+
qed

text \<open>A separate phase commutes with linking: modules compiled separately link,
  and the result is the compilation of the linked source. Both modules are
  compiled under the same \<open>cfg\<close> (the syntactic linking of SepCompCert
  \<^cite>\<open>kang2016\<close>) without it \<^text>\<open>compile_link\<close> holds only for identity
  translations.\<close>

locale separate_phase =
  phase sem\<^sub>S sem\<^sub>T cfg compile +
  src: linkable sem\<^sub>S link\<^sub>S mod_sig\<^sub>S sig_join\<^sub>S compat\<^sub>S +
  tgt: linkable sem\<^sub>T link\<^sub>T mod_sig\<^sub>T sig_join\<^sub>T compat\<^sub>T
  for sem\<^sub>S :: \<open>'ffi \<Rightarrow> 's \<Rightarrow> 'ev behaviour set\<close>
    and sem\<^sub>T :: \<open>'ffi \<Rightarrow> 't \<Rightarrow> 'ev behaviour set\<close>
    and cfg :: \<open>'c\<close>
    and compile link\<^sub>S
    and mod_sig\<^sub>S :: \<open>'s \<Rightarrow> 'sig\<close>
    and sig_join\<^sub>S compat\<^sub>S link\<^sub>T mod_sig\<^sub>T sig_join\<^sub>T compat\<^sub>T +
  assumes compile_link:
    \<open>compile cfg p\<^sub>1 = Some q\<^sub>1 \<Longrightarrow>
     compile cfg p\<^sub>2 = Some q\<^sub>2 \<Longrightarrow>
     link\<^sub>S p\<^sub>1 p\<^sub>2 = Some p \<Longrightarrow>
     \<exists>q. link\<^sub>T q\<^sub>1 q\<^sub>2 = Some q \<and> compile cfg p = Some q\<close>
begin

lemma separate_compilation:
  assumes \<open>compile cfg p\<^sub>1 = Some q\<^sub>1\<close>
      and \<open>compile cfg p\<^sub>2 = Some q\<^sub>2\<close>
      and \<open>link\<^sub>S p\<^sub>1 p\<^sub>2 = Some p\<close>
    shows \<open>\<exists>q. link\<^sub>T q\<^sub>1 q\<^sub>2 = Some q \<and> sem\<^sub>T ffi q \<sqsubseteq> sem\<^sub>S ffi p\<close>
  using compile_link[OF assms] compile_correct
  by blast

end

text \<open>Separate phases compose like phases:\<close>

lemma separate_phase_compose:
  assumes p\<^sub>1: \<open>separate_phase sem\<^sub>1 sem\<^sub>2 c\<^sub>a f
      link\<^sub>1 sig\<^sub>1 join\<^sub>1 compat\<^sub>1 link\<^sub>2 sig\<^sub>2 join\<^sub>2 compat\<^sub>2\<close>
    and p\<^sub>2: \<open>separate_phase sem\<^sub>2 sem\<^sub>3 c\<^sub>b g
      link\<^sub>2 sig\<^sub>2 join\<^sub>2 compat\<^sub>2 link\<^sub>3 sig\<^sub>3 join\<^sub>3 compat\<^sub>3\<close>
  shows \<open>separate_phase sem\<^sub>1 sem\<^sub>3 (c\<^sub>a, c\<^sub>b) (\<lambda>(a, b) p. Option.bind (f a p) (g b))
    link\<^sub>1 sig\<^sub>1 join\<^sub>1 compat\<^sub>1 link\<^sub>3 sig\<^sub>3 join\<^sub>3 compat\<^sub>3\<close>
proof -
  interpret p\<^sub>1: separate_phase sem\<^sub>1 sem\<^sub>2 c\<^sub>a f
      link\<^sub>1 sig\<^sub>1 join\<^sub>1 compat\<^sub>1 link\<^sub>2 sig\<^sub>2 join\<^sub>2 compat\<^sub>2
    by (rule p\<^sub>1)
  interpret p\<^sub>2: separate_phase sem\<^sub>2 sem\<^sub>3 c\<^sub>b g
      link\<^sub>2 sig\<^sub>2 join\<^sub>2 compat\<^sub>2 link\<^sub>3 sig\<^sub>3 join\<^sub>3 compat\<^sub>3
    by (rule p\<^sub>2)
  from p\<^sub>1 p\<^sub>2 have ph: \<open>phase sem\<^sub>1 sem\<^sub>3 (c\<^sub>a, c\<^sub>b) (\<lambda>(a, b) p. Option.bind (f a p) (g b))\<close>
      and l\<^sub>1: \<open>linkable sem\<^sub>1 link\<^sub>1 sig\<^sub>1 join\<^sub>1 compat\<^sub>1\<close>
      and l\<^sub>3: \<open>linkable sem\<^sub>3 link\<^sub>3 sig\<^sub>3 join\<^sub>3 compat\<^sub>3\<close>
    by (auto simp: separate_phase_def intro: phase_compose)
  show ?thesis
  proof (intro separate_phase.intro ph l\<^sub>1 l\<^sub>3 separate_phase_axioms.intro, goal_cases link)
    case (link p\<^sub>1 q\<^sub>1 p\<^sub>2 q\<^sub>2 p)
    then obtain m\<^sub>1 m\<^sub>2 where f\<^sub>1: \<open>f c\<^sub>a p\<^sub>1 = Some m\<^sub>1\<close> and g\<^sub>1: \<open>g c\<^sub>b m\<^sub>1 = Some q\<^sub>1\<close>
        and f\<^sub>2: \<open>f c\<^sub>a p\<^sub>2 = Some m\<^sub>2\<close> and g\<^sub>2: \<open>g c\<^sub>b m\<^sub>2 = Some q\<^sub>2\<close>
      by (auto split: Option.bind_split_asm)
    from p\<^sub>1.compile_link[OF f\<^sub>1 f\<^sub>2 \<open>link\<^sub>1 p\<^sub>1 p\<^sub>2 = Some p\<close>] obtain m
      where l: \<open>link\<^sub>2 m\<^sub>1 m\<^sub>2 = Some m\<close> and \<open>f c\<^sub>a p = Some m\<close>
      by blast
    with p\<^sub>2.compile_link[OF g\<^sub>1 g\<^sub>2 l] show ?case by auto
  qed
qed


subsection \<open>Frontend\<close>

text \<open>The frontend preserves no behaviour, it fixes what the program is: an
  executable reader, sound and complete for a relation \<open>READ(f) \<leadsto> a\<close>.\<close>

locale frontend =
  fixes read  :: \<open>'file \<Rightarrow> 'ast option\<close>
    and reads :: \<open>'file \<Rightarrow> 'ast \<Rightarrow> bool\<close>  (\<open>READ'(_')/ \<leadsto>/ _\<close> [51, 51] 50)
  assumes read_sound: \<open>read f = Some a \<Longrightarrow> READ(f) \<leadsto> a\<close>
      and read_complete: \<open>READ(f) \<leadsto> a \<Longrightarrow> read f = Some a\<close>
begin

theorem read: \<open>read f = Some a \<longleftrightarrow> READ(f) \<leadsto> a\<close>
  using read_sound read_complete by blast

corollary read_unambiguous: \<open>READ(f) \<leadsto> a \<Longrightarrow> READ(f) \<leadsto> a' \<Longrightarrow> a = a'\<close>
  by (simp flip: read)

end


subsection \<open>Static semantics\<close>

text \<open>The type system discharges the premise \<open>Fail \<notin> sem \<dots>\<close>, everything else
  is stated modulo it. It elaborates a source term \<open>e\<close> to an \<^emph>\<open>explicit\<close>
  term \<open>e'\<close>. Only the explicit term has a semantics, so \<^text>\<open>soundness\<close> is about
  \<open>e'\<close>. The host is checked against the output environment \<open>\<Gamma>'\<close> which holds the
  program's foreign declarations.

  \<^text>\<open>soundness\<close> holds from the initial environment \<open>\<Gamma>\<^sub>0\<close> only: the
  semantics binds the primitives and nothing else, and a term typed in a richer
  environment can name what it never binds. \<^text>\<open>tc_sound\<close> holds in every
  environment, as separate compilation against the interfaces of other units
  needs.\<close>

locale type_system =
  core: language sem\<^sub>C for sem\<^sub>C :: \<open>'ffi \<Rightarrow> 'core \<Rightarrow> 'ev behaviour set\<close> +
  fixes \<Gamma>\<^sub>0 :: 'tenv
    and typecheck :: \<open>'tenv \<Rightarrow> 'src \<Rightarrow> ('tenv \<times> 'core) option\<close>
    and has_type :: \<open>'tenv \<Rightarrow> 'src \<Rightarrow> 'core \<Rightarrow> 'tenv \<Rightarrow> bool\<close>
        (\<open>_/ \<turnstile>/ _/ \<leadsto>/ _/ :/ _\<close> [51, 51, 51, 51] 50)
    and ffi_ok :: \<open>'tenv \<Rightarrow> 'ffi \<Rightarrow> bool\<close>  (\<open>_/ \<turnstile>\<^sub>f\<^sub>f\<^sub>i/ _\<close> [51, 51] 50)
  assumes tc_sound: \<open>typecheck \<Gamma> e = Some (\<Gamma>', e') \<Longrightarrow> \<Gamma> \<turnstile> e \<leadsto> e' : \<Gamma>'\<close>
      and soundness: \<open>\<Gamma>\<^sub>0 \<turnstile> e \<leadsto> e' : \<Gamma>' \<Longrightarrow> \<Gamma>' \<turnstile>\<^sub>f\<^sub>f\<^sub>i ffi \<Longrightarrow> Fail \<notin> sem\<^sub>C ffi e'\<close>

text \<open>The special case without elaboration: source and core coincide.\<close>

locale type_system_simple = language sem for sem +
  fixes \<Gamma>\<^sub>0 :: 'tenv
    and typecheck :: \<open>'tenv \<Rightarrow> 'ast \<Rightarrow> 'tenv option\<close>
    and has_type :: \<open>'tenv \<Rightarrow> 'ast \<Rightarrow> 'tenv \<Rightarrow> bool\<close>  (\<open>_/ \<turnstile>/ _/ :/ _\<close> [51, 51, 51] 50)
    and ffi_ok :: \<open>'tenv \<Rightarrow> 'ffi \<Rightarrow> bool\<close>  (\<open>_/ \<turnstile>\<^sub>f\<^sub>f\<^sub>i/ _\<close> [51, 51] 50)
  assumes tc_sound: \<open>typecheck \<Gamma> p = Some \<Gamma>' \<Longrightarrow> \<Gamma> \<turnstile> p : \<Gamma>'\<close>
      and soundness: \<open>\<Gamma>\<^sub>0 \<turnstile> p : \<Gamma>' \<Longrightarrow> \<Gamma>' \<turnstile>\<^sub>f\<^sub>f\<^sub>i ffi \<Longrightarrow> Fail \<notin> sem ffi p\<close>

sublocale type_system_simple \<subseteq> type_system
  sem \<Gamma>\<^sub>0
  \<open>\<lambda>\<Gamma> p. map_option (\<lambda>\<Gamma>'. (\<Gamma>', p)) (typecheck \<Gamma> p)\<close>
  \<open>\<lambda>\<Gamma> p p' \<Gamma>'. p' = p \<and> has_type \<Gamma> p \<Gamma>'\<close>
  ffi_ok
  by unfold_locales (auto dest: tc_sound soundness)


subsection \<open>Top-level module compiler\<close>

text \<open>The module compiler compiles one file to one target module. Three stages
  follow the frontend: the type system, from the surface to the explicit
  surface; elaboration, a phase that compiles the module language away into the
  core; and the backend, a separate phase from the core to the target, where
  linking is stated.\<close>

locale module_compiler =
  frontend read reads +
  typing: type_system sem\<^sub>E \<Gamma>\<^sub>0 typecheck has_type ffi_ok +
  elab: phase sem\<^sub>E sem\<^sub>C cfg\<^sub>E elab +
  pipeline: separate_phase sem\<^sub>C sem\<^sub>T cfg compile
             link\<^sub>S mod_sig\<^sub>S sig_join\<^sub>S compat\<^sub>S
             link\<^sub>T mod_sig\<^sub>T sig_join\<^sub>T compat\<^sub>T
  for read  :: \<open>'file \<Rightarrow> 'src option\<close>
    and reads :: \<open>'file \<Rightarrow> 'src \<Rightarrow> bool\<close>  (\<open>READ'(_')/ \<leadsto>/ _\<close> [51, 51] 50)
    and \<Gamma>\<^sub>0 :: 'tenv
    and typecheck :: \<open>'tenv \<Rightarrow> 'src \<Rightarrow> ('tenv \<times> 'exp) option\<close>
    and has_type :: \<open>'tenv \<Rightarrow> 'src \<Rightarrow> 'exp \<Rightarrow> 'tenv \<Rightarrow> bool\<close>
        (\<open>_/ \<turnstile>/ _/ \<leadsto>/ _/ :/ _\<close> [51, 51, 51, 51] 50)
    and ffi_ok   :: \<open>'tenv \<Rightarrow> 'ffi \<Rightarrow> bool\<close>           (\<open>_/ \<turnstile>\<^sub>f\<^sub>f\<^sub>i/ _\<close> [51, 51] 50)
    and sem\<^sub>E :: \<open>'ffi \<Rightarrow> 'exp \<Rightarrow> 'ev behaviour set\<close>
    and sem\<^sub>C :: \<open>'ffi \<Rightarrow> 'core \<Rightarrow> 'ev behaviour set\<close>
    and sem\<^sub>T :: \<open>'ffi \<Rightarrow> 'tgt \<Rightarrow> 'ev behaviour set\<close>
    and cfg\<^sub>E
    and elab :: \<open>'e \<Rightarrow> 'exp \<Rightarrow> 'core option\<close>
    and cfg
    and compile :: \<open>'c \<Rightarrow> 'core \<Rightarrow> 'tgt option\<close>
    and link\<^sub>S mod_sig\<^sub>S sig_join\<^sub>S
    and compat\<^sub>S :: \<open>'core \<Rightarrow> 'sig \<Rightarrow> bool\<close>
    and link\<^sub>T mod_sig\<^sub>T sig_join\<^sub>T
    and compat\<^sub>T :: \<open>'tgt \<Rightarrow> 'sig \<Rightarrow> bool\<close>
begin

text \<open>Per-file correctness: the file is read relationally, so any reader
  that satisfies \<^locale>\<open>frontend\<close> will do. The refinement is against
  \<open>sem\<^sub>E\<close>, the first semantics in the chain, since the surface AST has none.
  The proof composes \<^text>\<open>soundness\<close>, which rules \<^const>\<open>Fail\<close> out of
  \<open>sem\<^sub>E\<close>, with the two \<^text>\<open>compile_correct\<close>s.\<close>

theorem module_correct:
  assumes \<open>READ(src) \<leadsto> p\<close>
    and \<open>typecheck \<Gamma>\<^sub>0 p = Some (\<Gamma>', p\<^sub>E)\<close>
    and \<open>\<Gamma>' \<turnstile>\<^sub>f\<^sub>f\<^sub>i ffi\<close>
    and \<open>elab cfg\<^sub>E p\<^sub>E = Some p\<^sub>C\<close>
    and \<open>compile cfg p\<^sub>C = Some code\<close>
  shows \<open>sem\<^sub>T ffi code \<subseteq> ext (sem\<^sub>E ffi p\<^sub>E)\<close>
  using assms typing.tc_sound typing.soundness
    refines_trans[OF pipeline.compile_correct elab.compile_correct]
  by (fastforce simp: refines_def)

text \<open>Core modules compiled separately link to a target program that refines
  the linked core program.\<close>

lemmas separate_compilation = pipeline.separate_compilation

end

text \<open>Not covered: cross-module inlining, and other optimisations that copy
  or specialise callee code.\<close>

end
