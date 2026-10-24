theory Types
  imports CaraML_Prelude.Named_Cases CaraML_Syntax.Module_Expressions "HOL-Library.Multiset"
begin

section \<open>Types, rows and schemes\<close>

text \<open>The type language of the surface type system: Hindley--Milner with
  Koka-style row-typed effects \<^cite>\<open>\<open>Sect. 3.1\<close> in leijen2017\<close> and a
  module-dependent arrow for module binders at the term level
  \<^cite>\<open>\<open>Sect. 3.2\<close> in vivien2024\<close> \<^cite>\<open>\<open>Sect. 2\<close> in white2014\<close>. The main
  result is the characterisation of row equivalence by label multiset and
  tail (\<open>row_eq_iff\<close>); the executable matcher for the instance relation of
  schemes follows in \<open>Matching\<close>.

  The type language design decisions:

    \<^item> A function type carries a latent effect row, \<open>\<tau>\<^sub>1 \<rightarrow>\<langle>\<epsilon>\<rangle> \<tau>\<^sub>2\<close>.
      Rows are label lists with an optional tail variable, identified up to
      reordering of \<^emph>\<open>distinct\<close> labels, the scoped labels of
      \<^cite>\<open>\<open>Fig. 2\<close> in leijen2017\<close>, which make row unification syntactic without lacks or
      absence constraints. A label is the flat runtime label of an
      operation, so a \<open>handle\<close> clause discharges exactly its operation.
    \<^item> Type constructors are \<^emph>\<open>stamped\<close> (\<^cite>\<open>\<open>Sect. 4.1\<close> in milner1997\<close>, \<open>TyName\<close>):
      a declaration allocates a stamp, sealing against an abstract spec
      allocates a fresh one (generativity \<^cite>\<open>\<open>Sect. 5.6\<close> in milner1997\<close>
      \<^cite>\<open>\<open>Sect. 4\<close> in rossberg2014\<close>). A stamped name also lists the constructors of
      its declaration, so exhaustiveness of a match can be decided from the
      scrutinee's type alone, and an abstract type, whose constructors are
      hidden, is matchable only irrefutably.
    \<^item> \<^text>\<open>TDep imp sg m \<epsilon> \<tau>\<close> is the type of \<open>fn(S : sg) e\<close> and
      \<open>fn{S : sg} e\<close>: the signature's \<open>m\<close> abstract types are stamps \<open>TK k\<close>
      the derivation picks, opaque while the body is typed, and bound
      positionally in \<open>\<tau>\<close> as \<open>TA 0 i\<close> (\<open>kclose\<close>), so the stamps do not
      appear in the type; \<open>\<epsilon>\<close> is the body's ambient row, as for any arrow.
      An application opens the body at the realisation (\<open>kopen\<close>), as
      a scheme is instantiated. Sealing and functors keep stamps for abstract types,
      which nothing instantiates. The surface signature
      \<open>sg\<close> travels in the type because the explicit surface annotates every
      module argument with the callee's parameter signature
      (\<^const>\<open>AMod\<close>), and static interpretation reads that signature.\<close>

type_synonym tvar = nat
type_synonym rvar = nat

text \<open>A type name: stamp, spelling, and the constructors of its declaration
  with their arities (empty for an abstract type and for the built-in
  types).\<close>

type_synonym tyname = \<open>nat \<times> name \<times> (name \<times> nat) list\<close>

abbreviation stamp :: \<open>tyname \<Rightarrow> nat\<close> where \<open>stamp \<equiv> fst\<close>

text \<open>Three sorts of variables, each with its own substitution: \<^text>\<open>TV\<close>
  and \<^text>\<open>RV\<close> are the unification variables, the only ones ordinary
  substitution touches; \<^text>\<open>TB\<close> and \<^text>\<open>RB\<close> are the variables a
  scheme binds, replaced at instantiation; \<^text>\<open>TK\<close> is an abstract type
  of a module parameter, bound by the module-dependent arrow and replaced at
  its application. Bound variables keep their numbers, so generalisation
  and instantiation are renamings between sorts, and since substitution
  never enters a binder's sort, no capture can occur (the representation
  of the verified algorithm W \<^cite>\<open>naraschewski1999\<close>).\<close>

datatype krow =
    RNil                           \<comment> \<open>closed empty row \<open>\<langle>\<rangle>\<close>\<close>
  | RV rvar                        \<comment> \<open>open row tail \<open>\<langle>\<dots>|\<rho>\<rangle>\<close>\<close>
  | RB rvar                        \<comment> \<open>scheme-bound row tail\<close>
  | RCons name krow                \<comment> \<open>effect label\<close>

text \<open>Record types are rows over the type language itself: \<^text>\<open>TRNil\<close> is the
  closed empty record and \<^text>\<open>TRCons l \<tau> r\<close> extends the record type \<open>r\<close> by a
  field \<open>l : \<tau>\<close>. A record type is a spine of fields ending in \<^text>\<open>TRNil\<close>
  (closed) or in a variable (open), an ordinary \<^text>\<open>TV\<close>, \<^text>\<open>TB\<close> or
  \<^text>\<open>TK\<close>. The design decisions:

    \<^item> No record row datatype and no third variable sort: a record's tail is a
      type variable. Generalisation, instantiation, matching, the occurs check
      and the confinement invariants over substitutions then cover record tails
      without a new component in \<open>ksub\<close>, and the kind discipline (a tail is a
      record) holds by invariant, as it already does for the variable head of
      \<^text>\<open>TApp\<close> (\<open>wf_kty\<close>): the algorithm only ever equates a record tail
      with a record. A third sort would thread a third substitution component
      through every lemma over \<open>(\<theta>, \<rho>)\<close> pairs; reusing \<open>rvar\<close> would not save
      that, since a field row and an effect row are different types.
    \<^item> Fields are scoped labels, as effect labels are: two records are
      equivalent when every field of one can be pulled to the front of the
      other with an equivalent type and equivalent rests (\<open>fpull\<close>). Duplicate
      labels do not commute, so no lacks constraint is needed. The surface
      checker keeps labels distinct in literals, patterns and annotations;
      the kernel theory is sound with or without duplicates. The canonical
      form sorts fields stably by label (\<open>canon_ty\<close>, lexicographic on code
      points).
    \<^item> A tuple is the closed record with the decimal labels \<open>1\<close>, \<open>2\<close>, \<dots> and
      the unit type is the empty record, so a multi-argument function takes a
      record and the parameters of an effect in a handler name form one too.
    \<^item> Unification pairs fields by label through \<open>fpull\<close>; a label missing on
      one side is absorbed by that side's tail variable, with a fresh field
      type and a fresh tail.\<close>

datatype kty =
    TV tvar                        \<comment> \<open>type variable\<close>
  | TB tvar                        \<comment> \<open>scheme-bound type variable\<close>
  | TK tvar                        \<comment> \<open>abstract type of a module parameter, free\<close>
  | TA nat nat                     \<comment> \<open>abstract type of a module parameter, bound by its
                                     \<open>TDep\<close>: the binder's distance and the position in it
                                     (never free in a type of a derivation)\<close>
  | TC tyname \<open>kty list\<close>           \<comment> \<open>constructor application\<close>
  | TApp kty kty                   \<comment> \<open>application of a variable head \<open>f x\<close>\<close>
  | TFn kty krow kty               \<comment> \<open>function type with latent effect row\<close>
  | TDep bool msig nat krow kty
                                 \<comment> \<open>module-dependent arrow binding the parameter's abstract
                                     types, as many as the second field says;
                                     \<open>True\<close> for an implicit binder\<close>
  | TEv kty kty kty              \<comment> \<open>handler name: the effect (\<open>eff_ty l\<close>, or a variable while
                                     unknown), its scope, the effect's parameters as a tuple\<close>
  | TAct kty \<open>tvar list\<close> krow kty
                                 \<comment> \<open>name-taking action for an effect: binds the scope
                                     \<open>TK k\<close>, \<open>k \<in> K\<close>, of the name it receives\<close>
  | TRNil                        \<comment> \<open>closed empty record \<open>{}\<close>, the unit type\<close>
  | TRCons name kty kty          \<comment> \<open>record field \<open>l : \<tau>\<close> extending a record type, whose
                                     spine ends in \<open>TRNil\<close> or in a variable tail\<close>

text \<open>The built-in type names: literal types at stamp \<open>0\<close>, the
  prelude's \<open>bool\<close> and \<open>list\<close> at \<open>1\<close> and \<open>2\<close>; user declarations count from
  \<^text>\<open>first_stamp\<close>. An unsuffixed integer literal is an unbounded \<open>int\<close>; a
  suffixed one names its fixed-width type, \<^text>\<open>sfx_ty\<close>, and must lie in its
  range, \<^text>\<open>sfx_ok\<close>.\<close>

definition \<open>int_ty = (0, str ''int'', [])\<close>
definition \<open>f64_ty = (0, str ''f64'', [])\<close>
definition \<open>string_ty = (0, str ''string'', [])\<close>
definition \<open>char_ty = (0, str ''char'', [])\<close>
definition \<open>bool_ty = (1, str ''bool'', [(str ''True'', 0), (str ''False'', 0)])\<close>
definition \<open>list_ty = (2, str ''list'', [(str ''Nil'', 0), (str ''Cons'', 2)])\<close>

definition \<open>first_stamp = 3\<close>

fun sfx_ty :: \<open>suffix \<Rightarrow> tyname\<close> where
  \<open>sfx_ty I8 = (0, str ''i8'', [])\<close>
| \<open>sfx_ty I16 = (0, str ''i16'', [])\<close>
| \<open>sfx_ty I32 = (0, str ''i32'', [])\<close>
| \<open>sfx_ty I64 = (0, str ''i64'', [])\<close>
| \<open>sfx_ty U8 = (0, str ''u8'', [])\<close>
| \<open>sfx_ty U16 = (0, str ''u16'', [])\<close>
| \<open>sfx_ty U32 = (0, str ''u32'', [])\<close>
| \<open>sfx_ty U64 = (0, str ''u64'', [])\<close>

fun sfx_bits :: \<open>suffix \<Rightarrow> nat\<close> where
  \<open>sfx_bits I8 = 8\<close> | \<open>sfx_bits I16 = 16\<close> | \<open>sfx_bits I32 = 32\<close> | \<open>sfx_bits I64 = 64\<close>
| \<open>sfx_bits U8 = 8\<close> | \<open>sfx_bits U16 = 16\<close> | \<open>sfx_bits U32 = 32\<close> | \<open>sfx_bits U64 = 64\<close>

fun sfx_signed :: \<open>suffix \<Rightarrow> bool\<close> where
  \<open>sfx_signed I8 = True\<close> | \<open>sfx_signed I16 = True\<close> | \<open>sfx_signed I32 = True\<close>
| \<open>sfx_signed I64 = True\<close> | \<open>sfx_signed _ = False\<close>

definition sfx_ok :: \<open>suffix \<Rightarrow> int \<Rightarrow> bool\<close> where
  \<open>sfx_ok k v \<longleftrightarrow>
     (if sfx_signed k then - (2 ^ (sfx_bits k - 1)) \<le> v \<and> v < 2 ^ (sfx_bits k - 1)
      else 0 \<le> v \<and> v < 2 ^ sfx_bits k)\<close>

text \<open>An effect, identified by its label prefix, as a type constant, so that
  the effect of a handler name or an action is inferred by unification (the
  spelling is reserved, no surface type can name it). The effect type carries
  the effect's type arguments, so that the type of an action, \<^text>\<open>TAct\<close>,
  fixes the instantiation at which its name is used and a handler serves only
  actions at its own instantiation.\<close>

definition eff_ty :: \<open>name \<Rightarrow> kty list \<Rightarrow> kty\<close> where
  \<open>eff_ty l ts = TC (0, str ''%eff.'' @ l, []) ts\<close>

text \<open>The row label of an operation performed on a \<^emph>\<open>name\<close>: the operation's
  label under a reserved prefix, so that a row tells a named use of an effect
  from a plain one. A plain \<open>perform\<close> needs the plain label in the row, which
  only a plain handler provides; a named handler provides the named labels
  to its action.\<close>

definition nlbl :: \<open>name \<Rightarrow> name\<close> where
  \<open>nlbl l = str ''%n.'' @ l\<close>

lemma nlbl_inj[simp]: \<open>nlbl l = nlbl l' \<longleftrightarrow> l = l'\<close>
  by (simp add: nlbl_def)

lemma eff_ty_inj[simp]: \<open>eff_ty l ts = eff_ty l' ts' \<longleftrightarrow> l = l' \<and> ts = ts'\<close>
  by (simp add: eff_ty_def)

text \<open>A tuple is the closed record whose labels are the decimal positions
  \<open>1\<close>, \<open>2\<close>, \<dots>; the unit type is the empty record. \<open>untuple\<close> reads the
  components back positionally and inverts \<open>tuple\<close>.\<close>

function nat_digits :: \<open>nat \<Rightarrow> nat list\<close> where
  \<open>nat_digits n = (if n < 10 then [n] else nat_digits (n div 10) @ [n mod 10])\<close>
  by pat_completeness auto
termination by (relation \<open>measure id\<close>) auto

declare nat_digits.simps[simp del]

definition tuple_lbl :: \<open>nat \<Rightarrow> name\<close> where
  \<open>tuple_lbl i = map ((+) 0x30) (nat_digits i)\<close>

fun tuple_from :: \<open>nat \<Rightarrow> kty list \<Rightarrow> kty\<close> where
  \<open>tuple_from i [] = TRNil\<close>
| \<open>tuple_from i (t # ts) = TRCons (tuple_lbl i) t (tuple_from (Suc i) ts)\<close>

abbreviation unit_ty :: kty where \<open>unit_ty \<equiv> tuple_from 1 []\<close>
abbreviation tuple :: \<open>kty list \<Rightarrow> kty\<close> where \<open>tuple ts \<equiv> tuple_from 1 ts\<close>

fun untuple_from :: \<open>nat \<Rightarrow> kty \<Rightarrow> kty list option\<close> where
  \<open>untuple_from i TRNil = Some []\<close>
| \<open>untuple_from i (TRCons l t r) =
     (if l = tuple_lbl i then map_option ((#) t) (untuple_from (Suc i) r) else None)\<close>
| \<open>untuple_from i _ = None\<close>

abbreviation untuple :: \<open>kty \<Rightarrow> kty list option\<close> where \<open>untuple \<equiv> untuple_from 1\<close>

lemma untuple_from_tuple_from[simp]: \<open>untuple_from i (tuple_from i ts) = Some ts\<close>
  by (induction ts arbitrary: i) simp_all

lemma tuple_from_inj[simp]: \<open>tuple_from i ts = tuple_from i us \<longleftrightarrow> ts = us\<close>
  by (metis option.inject untuple_from_tuple_from)

lemma untuple_from_Some[simp]: \<open>untuple_from i u = Some ts \<longleftrightarrow> u = tuple_from i ts\<close>
proof
  assume \<open>untuple_from i u = Some ts\<close>
  then show \<open>u = tuple_from i ts\<close>
    by (induction i u arbitrary: ts rule: untuple_from.induct) (auto split: if_split_asm)
qed simp

text \<open>\<open>tapp\<close> is the smart apply keeping types canonical: applying to a
  constructor spine extends its argument list, otherwise it builds a
  \<^const>\<open>TApp\<close> whose head is a variable. Every type the algorithm builds
  is \<^emph>\<open>var-headed at \<^const>\<open>TApp\<close>\<close>, which keeps \<open>\<simeq>\<close> and unification
  structural and first-order.\<close>

fun tapp :: \<open>kty \<Rightarrow> kty \<Rightarrow> kty\<close> where
  \<open>tapp (TC c ts) x = TC c (ts @ [x])\<close>
| \<open>tapp f x = TApp f x\<close>

fun var_headed :: \<open>kty \<Rightarrow> bool\<close> where
  \<open>var_headed (TV _) = True\<close>
| \<open>var_headed (TApp f _) = var_headed f\<close>
| \<open>var_headed _ = False\<close>

fun rec_tailed :: \<open>kty \<Rightarrow> bool\<close> where
  \<open>rec_tailed TRNil = True\<close>
| \<open>rec_tailed (TRCons _ _ r) = rec_tailed r\<close>
| \<open>rec_tailed (TV _) = True\<close>
| \<open>rec_tailed (TB _) = True\<close>
| \<open>rec_tailed (TK _) = True\<close>
| \<open>rec_tailed _ = False\<close>

fun wf_kty :: \<open>kty \<Rightarrow> bool\<close> where
  \<open>wf_kty (TV _) = True\<close>
| \<open>wf_kty (TB _) = True\<close>
| \<open>wf_kty (TK _) = True\<close>
| \<open>wf_kty (TA _ _) = True\<close>
| \<open>wf_kty (TC _ ts) \<longleftrightarrow> (\<forall>t \<in> set ts. wf_kty t)\<close>
| \<open>wf_kty (TApp f x) \<longleftrightarrow> var_headed f \<and> wf_kty f \<and> wf_kty x\<close>
| \<open>wf_kty (TFn a _ b) \<longleftrightarrow> wf_kty a \<and> wf_kty b\<close>
| \<open>wf_kty (TDep _ _ _ _ b) = wf_kty b\<close>
| \<open>wf_kty (TEv l s t) \<longleftrightarrow> wf_kty l \<and> wf_kty s \<and> wf_kty t\<close>
| \<open>wf_kty (TAct l _ _ b) \<longleftrightarrow> wf_kty l \<and> wf_kty b\<close>
| \<open>wf_kty TRNil = True\<close>
| \<open>wf_kty (TRCons _ t r) \<longleftrightarrow> wf_kty t \<and> rec_tailed r \<and> wf_kty r\<close>

lemma tapp_var_headed: \<open>var_headed f \<Longrightarrow> tapp f x = TApp f x\<close>
  by (cases f) auto

subsection \<open>Row equivalence: scoped labels\<close>

text \<open>The display form: the least congruence generated by swapping adjacent
  \<^emph>\<open>distinct\<close> labels \<^cite>\<open>\<open>Fig. 2\<close> in leijen2017\<close>. Duplicate labels cannot swap
  past each other, which is the scoped-labels discipline.\<close>

inductive row_eq :: \<open>krow \<Rightarrow> krow \<Rightarrow> bool\<close>  (infix \<open>\<approx>\<close> 50) where
  req_refl:  \<open>r \<approx> r\<close>
| req_head:  \<open>r \<approx> r' \<Longrightarrow> RCons l r \<approx> RCons l r'\<close>
| req_swap:  \<open>l \<noteq> l' \<Longrightarrow> RCons l (RCons l' r) \<approx> RCons l' (RCons l r)\<close>
| req_trans: \<open>r \<approx> r' \<Longrightarrow> r' \<approx> r'' \<Longrightarrow> r \<approx> r''\<close>

declare req_trans[trans]

lemma row_eq_sym: \<open>r \<approx> r' \<Longrightarrow> r' \<approx> r\<close>
  by (induction rule: row_eq.induct) (auto intro: row_eq.intros)

text \<open>The implementation form: a row is determined by its label multiset
  and its tail. Labels carry no arguments, so duplicates of one label are
  interchangeable and the multiset is a complete invariant.\<close>

fun row_labels :: \<open>krow \<Rightarrow> name multiset\<close> where
  \<open>row_labels RNil = {#}\<close>
| \<open>row_labels (RV \<rho>) = {#}\<close>
| \<open>row_labels (RB \<rho>) = {#}\<close>
| \<open>row_labels (RCons l r) = add_mset l (row_labels r)\<close>

text \<open>The tail of a row is the row's end, itself a row: closed, or a
  variable of either sort.\<close>

fun row_tail :: \<open>krow \<Rightarrow> krow\<close> where
  \<open>row_tail RNil = RNil\<close>
| \<open>row_tail (RV \<rho>) = RV \<rho>\<close>
| \<open>row_tail (RB \<rho>) = RB \<rho>\<close>
| \<open>row_tail (RCons l r) = row_tail r\<close>

lemma row_eq_labels: \<open>r \<approx> r' \<Longrightarrow> row_labels r = row_labels r'\<close>
  by (induction rule: row_eq.induct) auto

lemma row_eq_tail: \<open>r \<approx> r' \<Longrightarrow> row_tail r = row_tail r'\<close>
  by (induction rule: row_eq.induct) auto

fun row_del :: \<open>name \<Rightarrow> krow \<Rightarrow> krow\<close> where
  \<open>row_del l RNil = RNil\<close>
| \<open>row_del l (RV \<rho>) = RV \<rho>\<close>
| \<open>row_del l (RB \<rho>) = RB \<rho>\<close>
| \<open>row_del l (RCons l' r) = (if l = l' then r else RCons l' (row_del l r))\<close>

lemma row_del_labels:
  \<open>l \<in># row_labels r \<Longrightarrow> row_labels (row_del l r) = row_labels r - {#l#}\<close>
  by (induction r) auto

lemma row_del_tail: \<open>row_tail (row_del l r) = row_tail r\<close>
  by (induction r) auto

lemma row_pull: \<open>l \<in># row_labels r \<Longrightarrow> r \<approx> RCons l (row_del l r)\<close>
proof (induction r)
  case (RCons l' r)
  show ?case
  proof (cases \<open>l = l'\<close>)
    case False
    with RCons.prems have \<open>l \<in># row_labels r\<close> by simp
    from RCons.IH[OF this] have \<open>RCons l' r \<approx> RCons l' (RCons l (row_del l r))\<close>
      by (rule req_head)
    also have \<open>RCons l' (RCons l (row_del l r)) \<approx> RCons l (RCons l' (row_del l r))\<close>
      using False by (intro req_swap) simp
    finally show ?thesis using False by simp
  qed (auto intro: row_eq.intros)
qed simp_all

lemma row_empty: \<open>row_labels r = {#} \<Longrightarrow> r = row_tail r\<close>
  by (induction r) auto

lemma row_eq_intro:
  \<open>row_labels r = row_labels r' \<Longrightarrow> row_tail r = row_tail r' \<Longrightarrow> r \<approx> r'\<close>
proof (induction r arbitrary: r')
  case (RCons l r\<^sub>0)
  note lab = \<open>row_labels (RCons l r\<^sub>0) = row_labels r'\<close>
  have mem: \<open>l \<in># row_labels r'\<close>
    by (simp flip: lab)
  have labels: \<open>row_labels r\<^sub>0 = row_labels (row_del l r')\<close>
    by (simp add: row_del_labels[OF mem] flip: lab)
  have tails: \<open>row_tail r\<^sub>0 = row_tail (row_del l r')\<close>
    using RCons.prems row_del_tail[of l r'] by simp
  from RCons.IH[OF labels tails]
  have \<open>RCons l r\<^sub>0 \<approx> RCons l (row_del l r')\<close> by (rule req_head)
  also have \<open>RCons l (row_del l r') \<approx> r'\<close>
    by (rule row_eq_sym) (rule row_pull[OF mem])
  finally show ?case .
qed (use row_empty in \<open>force intro: row_eq.intros\<close>)+

theorem row_eq_iff:
  \<open>r \<approx> r' \<longleftrightarrow> row_labels r = row_labels r' \<and> row_tail r = row_tail r'\<close>
  by (auto intro: row_eq_intro dest: row_eq_labels row_eq_tail)

subsection \<open>Substitution and free variables\<close>

fun rsubst :: \<open>(rvar \<Rightarrow> krow) \<Rightarrow> krow \<Rightarrow> krow\<close> where
  \<open>rsubst \<rho> RNil = RNil\<close>
| \<open>rsubst \<rho> (RV v) = \<rho> v\<close>
| \<open>rsubst \<rho> (RB v) = RB v\<close>
| \<open>rsubst \<rho> (RCons l r) = RCons l (rsubst \<rho> r)\<close>

fun tsubst :: \<open>(tvar \<Rightarrow> kty) \<Rightarrow> (rvar \<Rightarrow> krow) \<Rightarrow> kty \<Rightarrow> kty\<close> where
  \<open>tsubst \<theta> \<rho> (TV a) = \<theta> a\<close>
| \<open>tsubst \<theta> \<rho> (TB a) = TB a\<close>
| \<open>tsubst \<theta> \<rho> (TK a) = TK a\<close>
| \<open>tsubst \<theta> \<rho> (TA k i) = TA k i\<close>
| \<open>tsubst \<theta> \<rho> (TC c ts) = TC c (map (tsubst \<theta> \<rho>) ts)\<close>
| \<open>tsubst \<theta> \<rho> (TApp t\<^sub>1 t\<^sub>2) = TApp (tsubst \<theta> \<rho> t\<^sub>1) (tsubst \<theta> \<rho> t\<^sub>2)\<close>
| \<open>tsubst \<theta> \<rho> (TFn t\<^sub>1 e t\<^sub>2) = TFn (tsubst \<theta> \<rho> t\<^sub>1) (rsubst \<rho> e) (tsubst \<theta> \<rho> t\<^sub>2)\<close>
| \<open>tsubst \<theta> \<rho> (TDep i sg T e t) = TDep i sg T (rsubst \<rho> e) (tsubst \<theta> \<rho> t)\<close>
| \<open>tsubst \<theta> \<rho> (TEv l s t) = TEv (tsubst \<theta> \<rho> l) (tsubst \<theta> \<rho> s) (tsubst \<theta> \<rho> t)\<close>
| \<open>tsubst \<theta> \<rho> (TAct l K e t) = TAct (tsubst \<theta> \<rho> l) K (rsubst \<rho> e) (tsubst \<theta> \<rho> t)\<close>
| \<open>tsubst \<theta> \<rho> TRNil = TRNil\<close>
| \<open>tsubst \<theta> \<rho> (TRCons l t r) = TRCons l (tsubst \<theta> \<rho> t) (tsubst \<theta> \<rho> r)\<close>

lemma rsubst_id: \<open>(\<forall>v. \<rho> v = RV v) \<Longrightarrow> rsubst \<rho> r = r\<close>
  by (induction r) auto

lemma tsubst_id: \<open>(\<forall>a. \<theta> a = TV a) \<Longrightarrow> (\<forall>v. \<rho> v = RV v) \<Longrightarrow> tsubst \<theta> \<rho> t = t\<close>
  by (induction t) (auto simp: rsubst_id intro: map_idI)

fun ftv :: \<open>kty \<Rightarrow> tvar set\<close> where
  \<open>ftv (TV a) = {a}\<close>
| \<open>ftv (TB a) = {}\<close>
| \<open>ftv (TK a) = {}\<close>
| \<open>ftv (TA k i) = {}\<close>
| \<open>ftv (TC c ts) = \<Union>(set (map ftv ts))\<close>
| \<open>ftv (TApp t\<^sub>1 t\<^sub>2) = ftv t\<^sub>1 \<union> ftv t\<^sub>2\<close>
| \<open>ftv (TFn t\<^sub>1 e t\<^sub>2) = ftv t\<^sub>1 \<union> ftv t\<^sub>2\<close>
| \<open>ftv (TDep i sg K e t) = ftv t\<close>
| \<open>ftv (TEv l s t) = ftv l \<union> ftv s \<union> ftv t\<close>
| \<open>ftv (TAct l K e t) = ftv l \<union> ftv t\<close>
| \<open>ftv TRNil = {}\<close>
| \<open>ftv (TRCons l t r) = ftv t \<union> ftv r\<close>

fun frv_row :: \<open>krow \<Rightarrow> rvar set\<close> where
  \<open>frv_row RNil = {}\<close>
| \<open>frv_row (RV v) = {v}\<close>
| \<open>frv_row (RB v) = {}\<close>
| \<open>frv_row (RCons l r) = frv_row r\<close>

fun frv :: \<open>kty \<Rightarrow> rvar set\<close> where
  \<open>frv (TV a) = {}\<close>
| \<open>frv (TB a) = {}\<close>
| \<open>frv (TK a) = {}\<close>
| \<open>frv (TA k i) = {}\<close>
| \<open>frv (TC c ts) = \<Union>(set (map frv ts))\<close>
| \<open>frv (TApp t\<^sub>1 t\<^sub>2) = frv t\<^sub>1 \<union> frv t\<^sub>2\<close>
| \<open>frv (TFn t\<^sub>1 e t\<^sub>2) = frv t\<^sub>1 \<union> frv_row e \<union> frv t\<^sub>2\<close>
| \<open>frv (TDep i sg T e t) = frv_row e \<union> frv t\<close>
| \<open>frv (TEv l s t) = frv l \<union> frv s \<union> frv t\<close>
| \<open>frv (TAct l K e t) = frv l \<union> frv_row e \<union> frv t\<close>
| \<open>frv TRNil = {}\<close>
| \<open>frv (TRCons l t r) = frv t \<union> frv r\<close>

subsection \<open>Type equivalence: types up to row reordering\<close>

text \<open>Row unification can only make rows \<^emph>\<open>equivalent\<close> (\<open>\<approx>\<close>), never
  syntactically equal, so the typing rules compare types up to \<open>\<simeq>\<close>:
  structural equality with \<open>\<approx>\<close> at every row position. Two
  module-dependent arrows are compared on the same binder, the same
  signature and the same bound variables, then the rows and the results;
  binders written separately are distinct types, a limitation recorded
  with the open problems.\<close>

text \<open>\<open>fpull l u\<close> pulls the first field labelled \<open>l\<close> of the record type \<open>u\<close>
  to the front: its type and the rest of the record, in order. \<open>rtail\<close> is the
  end of a record spine, \<^const>\<open>TRNil\<close> or the tail variable.\<close>

fun fpull :: \<open>name \<Rightarrow> kty \<Rightarrow> (kty \<times> kty) option\<close> where
  \<open>fpull l (TRCons l' t r) =
     (if l = l' then Some (t, r)
      else map_option (\<lambda>(t', r'). (t', TRCons l' t r')) (fpull l r))\<close>
| \<open>fpull l _ = None\<close>

fun rtail :: \<open>kty \<Rightarrow> kty\<close> where
  \<open>rtail (TRCons _ _ r) = rtail r\<close>
| \<open>rtail u = u\<close>

lemma rtail_TV_ftv: \<open>rtail u = TV b \<Longrightarrow> b \<in> ftv u\<close>
  by (induction u) auto

fun ty_eq :: \<open>kty \<Rightarrow> kty \<Rightarrow> bool\<close>  (infix \<open>\<simeq>\<close> 50)
and tys_eq :: \<open>kty list \<Rightarrow> kty list \<Rightarrow> bool\<close> (infix \<open>[\<simeq>]\<close> 50) where
  \<open>TV a \<simeq> u \<longleftrightarrow> u = TV a\<close>
| \<open>TB a \<simeq> u \<longleftrightarrow> u = TB a\<close>
| \<open>TK a \<simeq> u \<longleftrightarrow> u = TK a\<close>
| \<open>TA k i \<simeq> u \<longleftrightarrow> u = TA k i\<close>
| ty_eq_TC_case: \<open>TC c ts \<simeq> u \<longleftrightarrow> (case u of TC c' ts' \<Rightarrow> c = c' \<and> ts [\<simeq>] ts' | _ \<Rightarrow> False)\<close>
| ty_eq_TApp_case: \<open>TApp t\<^sub>1 t\<^sub>2 \<simeq> u \<longleftrightarrow> (case u of TApp u\<^sub>1 u\<^sub>2 \<Rightarrow> t\<^sub>1 \<simeq> u\<^sub>1 \<and> t\<^sub>2 \<simeq> u\<^sub>2 | _ \<Rightarrow> False)\<close>
| ty_eq_TFn_case: \<open>TFn t\<^sub>1 e t\<^sub>2 \<simeq> u \<longleftrightarrow>
     (case u of TFn u\<^sub>1 g u\<^sub>2 \<Rightarrow> t\<^sub>1 \<simeq> u\<^sub>1 \<and> e \<approx> g \<and> t\<^sub>2 \<simeq> u\<^sub>2 | _ \<Rightarrow> False)\<close>
| ty_eq_TDep_case: \<open>TDep i sg T e t \<simeq> u \<longleftrightarrow>
     (case u of TDep i' sg' T' g u' \<Rightarrow> i = i' \<and> sg = sg' \<and> T = T' \<and> e \<approx> g \<and> t \<simeq> u' | _ \<Rightarrow> False)\<close>
| ty_eq_TEv_case: \<open>TEv l s t \<simeq> u \<longleftrightarrow> (case u of TEv l' s' u' \<Rightarrow> l \<simeq> l' \<and> s \<simeq> s' \<and> t \<simeq> u' | _ \<Rightarrow> False)\<close>
| ty_eq_TAct_case: \<open>TAct l K e t \<simeq> u \<longleftrightarrow>
     (case u of TAct l' K' g u' \<Rightarrow> l \<simeq> l' \<and> K = K' \<and> e \<approx> g \<and> t \<simeq> u' | _ \<Rightarrow> False)\<close>
| ty_eq_TRNil_case: \<open>TRNil \<simeq> u \<longleftrightarrow> u = TRNil\<close>
| ty_eq_TRCons_case: \<open>TRCons l t r \<simeq> u \<longleftrightarrow>
     (case fpull l u of Some (t', r') \<Rightarrow> t \<simeq> t' \<and> r \<simeq> r' | None \<Rightarrow> False)\<close>
| \<open>[] [\<simeq>] us \<longleftrightarrow> us = []\<close>
| \<open>t # ts [\<simeq>] us \<longleftrightarrow> (\<exists>u us'. us = u # us' \<and> t \<simeq> u \<and> ts [\<simeq>] us')\<close>

lemma ty_eq_TC[simp]: \<open>TC c ts \<simeq> u \<longleftrightarrow> (\<exists>us. u = TC c us \<and> ts [\<simeq>] us)\<close>
  by (cases u) auto

lemma ty_eq_TApp[simp]:
  \<open>TApp t\<^sub>1 t\<^sub>2 \<simeq> u \<longleftrightarrow> (\<exists>u\<^sub>1 u\<^sub>2. u = TApp u\<^sub>1 u\<^sub>2 \<and> t\<^sub>1 \<simeq> u\<^sub>1 \<and> t\<^sub>2 \<simeq> u\<^sub>2)\<close>
  by (cases u) auto

lemma ty_eq_TFn[simp]:
  \<open>TFn t\<^sub>1 e t\<^sub>2 \<simeq> u \<longleftrightarrow> (\<exists>u\<^sub>1 g u\<^sub>2. u = TFn u\<^sub>1 g u\<^sub>2 \<and> t\<^sub>1 \<simeq> u\<^sub>1 \<and> e \<approx> g \<and> t\<^sub>2 \<simeq> u\<^sub>2)\<close>
  by (cases u) auto

lemma ty_eq_TDep[simp]:
  \<open>TDep i sg T e t \<simeq> u \<longleftrightarrow> (\<exists>g u'. u = TDep i sg T g u' \<and> e \<approx> g \<and> t \<simeq> u')\<close>
  by (cases u) auto

lemma ty_eq_TEv[simp]:
  \<open>TEv l s t \<simeq> u \<longleftrightarrow> (\<exists>l' s' u'. u = TEv l' s' u' \<and> l \<simeq> l' \<and> s \<simeq> s' \<and> t \<simeq> u')\<close>
  by (cases u) auto

lemma ty_eq_TAct[simp]:
  \<open>TAct l K e t \<simeq> u \<longleftrightarrow> (\<exists>l' g u'. u = TAct l' K g u' \<and> l \<simeq> l' \<and> e \<approx> g \<and> t \<simeq> u')\<close>
  by (cases u) auto

lemma ty_eq_TRCons[simp]:
  \<open>TRCons l t r \<simeq> u \<longleftrightarrow> (\<exists>t' r'. fpull l u = Some (t', r') \<and> t \<simeq> t' \<and> r \<simeq> r')\<close>
  by (cases \<open>fpull l u\<close>) auto

text \<open>The equations above are the simp set; the defining equations, by cases
  on the first argument only (which keeps the function package quick), serve
  the code generator.\<close>

declare ty_eq_TC_case[simp del] ty_eq_TApp_case[simp del] ty_eq_TFn_case[simp del]
  ty_eq_TDep_case[simp del] ty_eq_TEv_case[simp del] ty_eq_TAct_case[simp del]
  ty_eq_TRCons_case[simp del]

lemma tys_eq_conv: \<open>([\<simeq>]) = list_all2 (\<simeq>)\<close>
proof (intro ext)
  fix ts us
  show \<open>ts [\<simeq>] us \<longleftrightarrow> list_all2 (\<simeq>) ts us\<close>
    by (induction ts arbitrary: us) (auto simp: list_all2_Cons1)
qed

lemma tys_eq_code[code]:
  \<open>[] [\<simeq>] us \<longleftrightarrow> us = []\<close>
  \<open>t # ts [\<simeq>] us \<longleftrightarrow> (case us of [] \<Rightarrow> False | u # us' \<Rightarrow> t \<simeq> u \<and> ts [\<simeq>] us')\<close>
  by (auto split: list.split)

lemma ty_eq_refl[simp, intro!]: \<open>t \<simeq> t\<close>
proof (induction t)
  case (TC c ts)
  then have \<open>ts [\<simeq>] ts\<close> by (induction ts) auto
  then show ?case by simp
qed (auto intro: req_refl)

lemma tys_eq_refl[simp, intro!]: \<open>ts [\<simeq>] ts\<close>
  by (induction ts) auto

text \<open>\<open>\<simeq>\<close> preserves free variables (rows preserve their tail) and commutes
  with substitution.\<close>

lemma frv_row_tail: \<open>frv_row r = (case row_tail r of RV v \<Rightarrow> {v} | _ \<Rightarrow> {})\<close>
  by (induction r) auto

lemma row_eq_frv: \<open>r \<approx> r' \<Longrightarrow> frv_row r = frv_row r'\<close>
  by (simp add: frv_row_tail row_eq_tail)

text \<open>Pulling a field commutes with every function that maps a record field by
  field, and a set-valued function that unions over fields is invariant under it.\<close>

lemma fpull_map:
  assumes f: \<open>\<And>l t r. f (TRCons l t r) = TRCons l (f t) (f r)\<close>
  shows \<open>fpull l u = Some (t', r') \<Longrightarrow> fpull l (f u) = Some (f t', f r')\<close>
  by (induction u arbitrary: t' r') (auto simp: f split: if_splits option.splits)

lemma fpull_set:
  assumes g: \<open>\<And>l t r. g (TRCons l t r) = g t \<union> g r\<close>
  shows \<open>fpull l u = Some (t', r') \<Longrightarrow> g u = g t' \<union> g r'\<close>
  by (induction u arbitrary: t' r') (auto simp: g split: if_splits option.splits)

lemma fpull_ftv: \<open>fpull l u = Some (t', r') \<Longrightarrow> ftv u = ftv t' \<union> ftv r'\<close>
  by (rule fpull_set) simp_all

lemma fpull_frv: \<open>fpull l u = Some (t', r') \<Longrightarrow> frv u = frv t' \<union> frv r'\<close>
  by (rule fpull_set) simp_all

lemma fpull_tsubst:
  \<open>fpull l u = Some (t', r') \<Longrightarrow>
     fpull l (tsubst \<theta> \<rho> u) = Some (tsubst \<theta> \<rho> t', tsubst \<theta> \<rho> r')\<close>
  by (rule fpull_map) simp_all

lemma ty_eq_ftv: \<open>t \<simeq> u \<Longrightarrow> ftv t = ftv u\<close>
proof (induction t arbitrary: u)
  case (TC c ts)
  then obtain us where us: \<open>u = TC c us\<close> \<open>ts [\<simeq>] us\<close> by auto
  from TC.IH us(2) have \<open>map ftv ts = map ftv us\<close>
    by (induction ts arbitrary: us) auto
  then show ?case using us(1) by simp
qed (auto dest: fpull_ftv)

lemma ty_eq_frv: \<open>t \<simeq> u \<Longrightarrow> frv t = frv u\<close>
proof (induction t arbitrary: u)
  case (TC c ts)
  then obtain us where us: \<open>u = TC c us\<close> \<open>ts [\<simeq>] us\<close> by auto
  from TC.IH us(2) have \<open>map frv ts = map frv us\<close>
    by (induction ts arbitrary: us) auto
  then show ?case using us(1) by simp
qed (auto simp: row_eq_frv dest: fpull_frv)

lemma row_eq_rsubst: \<open>r \<approx> r' \<Longrightarrow> rsubst \<rho> r \<approx> rsubst \<rho> r'\<close>
  by (induction rule: row_eq.induct) (auto intro: row_eq.intros)

lemma ty_eq_tsubst: \<open>t \<simeq> u \<Longrightarrow> tsubst \<theta> \<rho> t \<simeq> tsubst \<theta> \<rho> u\<close>
proof (induction t arbitrary: u)
  case (TC c ts)
  then obtain us where us: \<open>u = TC c us\<close> \<open>ts [\<simeq>] us\<close> by auto
  from TC.IH us(2) have \<open>map (tsubst \<theta> \<rho>) ts [\<simeq>] map (tsubst \<theta> \<rho>) us\<close>
    by (induction ts arbitrary: us) auto
  then show ?case using us(1) by simp
next
  case (TRCons l t r)
  then obtain t' r' where p: \<open>fpull l u = Some (t', r')\<close> and \<open>t \<simeq> t'\<close> \<open>r \<simeq> r'\<close> by auto
  then show ?case by (auto simp: fpull_tsubst[OF p] intro!: TRCons.IH)
qed (auto intro: row_eq_rsubst)

lemma tys_eq_tsubst:
  \<open>ts [\<simeq>] us \<Longrightarrow> map (tsubst \<theta> \<rho>) ts [\<simeq>] map (tsubst \<theta> \<rho>) us\<close>
  by (induction ts arbitrary: us) (auto intro: ty_eq_tsubst)

subsection \<open>Type schemes\<close>

text \<open>A scheme binds the \<^const>\<open>TB\<close> and \<^const>\<open>RB\<close> variables of its
  body; a monotype binds nothing. Instantiation replaces the bound
  variables, by \<open>bsubst\<close>, and never touches a unification variable;
  generalisation renames unification variables into bound ones. The
  instance relation \<open>\<succeq>\<close> is Standard ML's \<^cite>\<open>\<open>Sect. 4.5\<close> in milner1997\<close>.\<close>

datatype scheme =
    Sch kty            \<comment> \<open>generalised: the body's bound variables are quantified\<close>
  | Mono kty           \<comment> \<open>a monotype\<close>

abbreviation kmono :: \<open>kty \<Rightarrow> scheme\<close> where
  \<open>kmono \<tau> \<equiv> Mono \<tau>\<close>

fun brsubst :: \<open>(rvar \<Rightarrow> krow) \<Rightarrow> krow \<Rightarrow> krow\<close> where
  \<open>brsubst \<rho> RNil = RNil\<close>
| \<open>brsubst \<rho> (RV v) = RV v\<close>
| \<open>brsubst \<rho> (RB v) = \<rho> v\<close>
| \<open>brsubst \<rho> (RCons l r) = RCons l (brsubst \<rho> r)\<close>

fun bsubst :: \<open>(tvar \<Rightarrow> kty) \<Rightarrow> (rvar \<Rightarrow> krow) \<Rightarrow> kty \<Rightarrow> kty\<close> where
  \<open>bsubst \<theta> \<rho> (TV a) = TV a\<close>
| \<open>bsubst \<theta> \<rho> (TB a) = \<theta> a\<close>
| \<open>bsubst \<theta> \<rho> (TK a) = TK a\<close>
| \<open>bsubst \<theta> \<rho> (TA k i) = TA k i\<close>
| \<open>bsubst \<theta> \<rho> (TC c ts) = TC c (map (bsubst \<theta> \<rho>) ts)\<close>
| \<open>bsubst \<theta> \<rho> (TApp t\<^sub>1 t\<^sub>2) = TApp (bsubst \<theta> \<rho> t\<^sub>1) (bsubst \<theta> \<rho> t\<^sub>2)\<close>
| \<open>bsubst \<theta> \<rho> (TFn t\<^sub>1 e t\<^sub>2) = TFn (bsubst \<theta> \<rho> t\<^sub>1) (brsubst \<rho> e) (bsubst \<theta> \<rho> t\<^sub>2)\<close>
| \<open>bsubst \<theta> \<rho> (TDep i sg K e t) = TDep i sg K (brsubst \<rho> e) (bsubst \<theta> \<rho> t)\<close>
| \<open>bsubst \<theta> \<rho> (TEv l s t) = TEv (bsubst \<theta> \<rho> l) (bsubst \<theta> \<rho> s) (bsubst \<theta> \<rho> t)\<close>
| \<open>bsubst \<theta> \<rho> (TAct l K e t) = TAct (bsubst \<theta> \<rho> l) K (brsubst \<rho> e) (bsubst \<theta> \<rho> t)\<close>
| \<open>bsubst \<theta> \<rho> TRNil = TRNil\<close>
| \<open>bsubst \<theta> \<rho> (TRCons l t r) = TRCons l (bsubst \<theta> \<rho> t) (bsubst \<theta> \<rho> r)\<close>

text \<open>The bound variables of a type, and the abstract types it mentions.\<close>

fun btv :: \<open>kty \<Rightarrow> tvar set\<close> where
  \<open>btv (TV a) = {}\<close>
| \<open>btv (TB a) = {a}\<close>
| \<open>btv (TK a) = {}\<close>
| \<open>btv (TA k i) = {}\<close>
| \<open>btv (TC c ts) = \<Union>(set (map btv ts))\<close>
| \<open>btv (TApp t\<^sub>1 t\<^sub>2) = btv t\<^sub>1 \<union> btv t\<^sub>2\<close>
| \<open>btv (TFn t\<^sub>1 e t\<^sub>2) = btv t\<^sub>1 \<union> btv t\<^sub>2\<close>
| \<open>btv (TDep i sg K e t) = btv t\<close>
| \<open>btv (TEv l s t) = btv l \<union> btv s \<union> btv t\<close>
| \<open>btv (TAct l K e t) = btv l \<union> btv t\<close>
| \<open>btv TRNil = {}\<close>
| \<open>btv (TRCons l t r) = btv t \<union> btv r\<close>

fun brv_row :: \<open>krow \<Rightarrow> rvar set\<close> where
  \<open>brv_row RNil = {}\<close>
| \<open>brv_row (RV v) = {}\<close>
| \<open>brv_row (RB v) = {v}\<close>
| \<open>brv_row (RCons l r) = brv_row r\<close>

fun brv :: \<open>kty \<Rightarrow> rvar set\<close> where
  \<open>brv (TV a) = {}\<close>
| \<open>brv (TB a) = {}\<close>
| \<open>brv (TK a) = {}\<close>
| \<open>brv (TA k i) = {}\<close>
| \<open>brv (TC c ts) = \<Union>(set (map brv ts))\<close>
| \<open>brv (TApp t\<^sub>1 t\<^sub>2) = brv t\<^sub>1 \<union> brv t\<^sub>2\<close>
| \<open>brv (TFn t\<^sub>1 e t\<^sub>2) = brv t\<^sub>1 \<union> brv_row e \<union> brv t\<^sub>2\<close>
| \<open>brv (TDep i sg K e t) = brv_row e \<union> brv t\<close>
| \<open>brv (TEv l s t) = brv l \<union> brv s \<union> brv t\<close>
| \<open>brv (TAct l K e t) = brv l \<union> brv_row e \<union> brv t\<close>
| \<open>brv TRNil = {}\<close>
| \<open>brv (TRCons l t r) = brv t \<union> brv r\<close>

text \<open>The binder list of an action type is inert for the abstract-type
  variables: it records which variables are the action's own (their
  renaming at an application, \<open>G_act\<close>), while the typing rules that
  introduce an action type keep those variables out of its body, so no
  occurrence is ever bound. \<open>ktv\<close> and \<open>ksubst\<close> therefore
  look through it; erasing the list for the core commutes with
  instantiation.\<close>

fun ktv :: \<open>kty \<Rightarrow> tvar set\<close> where
  \<open>ktv (TV a) = {}\<close>
| \<open>ktv (TB a) = {}\<close>
| \<open>ktv (TK a) = {a}\<close>
| \<open>ktv (TA k i) = {}\<close>
| \<open>ktv (TC c ts) = \<Union>(set (map ktv ts))\<close>
| \<open>ktv (TApp t\<^sub>1 t\<^sub>2) = ktv t\<^sub>1 \<union> ktv t\<^sub>2\<close>
| \<open>ktv (TFn t\<^sub>1 e t\<^sub>2) = ktv t\<^sub>1 \<union> ktv t\<^sub>2\<close>
| \<open>ktv (TDep i sg K e t) = ktv t\<close>
| \<open>ktv (TEv l s t) = ktv l \<union> ktv s \<union> ktv t\<close>
| \<open>ktv (TAct l K e t) = ktv l \<union> ktv t\<close>
| \<open>ktv TRNil = {}\<close>
| \<open>ktv (TRCons l t r) = ktv t \<union> ktv r\<close>

lemma fpull_ktv: \<open>fpull l u = Some (t', r') \<Longrightarrow> ktv u = ktv t' \<union> ktv r'\<close>
  by (rule fpull_set) simp_all

text \<open>A type is name-free when no handler name and no action occurs in it: the
  types a foreign value may have, since a name cannot cross the foreign boundary.\<close>

fun name_free :: \<open>kty \<Rightarrow> bool\<close> where
  \<open>name_free (TC c ts) \<longleftrightarrow> (\<forall>t \<in> set ts. name_free t)\<close>
| \<open>name_free (TApp t\<^sub>1 t\<^sub>2) \<longleftrightarrow> name_free t\<^sub>1 \<and> name_free t\<^sub>2\<close>
| \<open>name_free (TFn t\<^sub>1 e t\<^sub>2) \<longleftrightarrow> name_free t\<^sub>1 \<and> name_free t\<^sub>2\<close>
| \<open>name_free (TDep i sg K e t) = name_free t\<close>
| \<open>name_free (TEv l s t) = False\<close>
| \<open>name_free (TAct l K e t) = False\<close>
| \<open>name_free (TRCons l t r) \<longleftrightarrow> name_free t \<and> name_free r\<close>
| \<open>name_free t = True\<close>

lemma brsubst_id: \<open>brv_row r = {} \<Longrightarrow> brsubst \<rho> r = r\<close>
  by (induction r) auto

lemma bsubst_id: \<open>btv t = {} \<Longrightarrow> brv t = {} \<Longrightarrow> bsubst \<theta> \<rho> t = t\<close>
  by (induction t) (auto simp: brsubst_id intro: map_idI)

text \<open>Replacing the abstract types of a module binder, at its application.\<close>

fun ksubst :: \<open>(tvar \<Rightarrow> kty) \<Rightarrow> kty \<Rightarrow> kty\<close> where
  \<open>ksubst \<phi> (TV a) = TV a\<close>
| \<open>ksubst \<phi> (TB a) = TB a\<close>
| \<open>ksubst \<phi> (TK a) = \<phi> a\<close>
| \<open>ksubst \<phi> (TA k i) = TA k i\<close>
| \<open>ksubst \<phi> (TC c ts) = TC c (map (ksubst \<phi>) ts)\<close>
| \<open>ksubst \<phi> (TApp t\<^sub>1 t\<^sub>2) = TApp (ksubst \<phi> t\<^sub>1) (ksubst \<phi> t\<^sub>2)\<close>
| \<open>ksubst \<phi> (TFn t\<^sub>1 e t\<^sub>2) = TFn (ksubst \<phi> t\<^sub>1) e (ksubst \<phi> t\<^sub>2)\<close>
| \<open>ksubst \<phi> (TDep i sg K e t) = TDep i sg K e (ksubst \<phi> t)\<close>
| \<open>ksubst \<phi> (TEv l s t) = TEv (ksubst \<phi> l) (ksubst \<phi> s) (ksubst \<phi> t)\<close>
| \<open>ksubst \<phi> (TAct l K e t) = TAct (ksubst \<phi> l) K e (ksubst \<phi> t)\<close>
| \<open>ksubst \<phi> TRNil = TRNil\<close>
| \<open>ksubst \<phi> (TRCons l t r) = TRCons l (ksubst \<phi> t) (ksubst \<phi> r)\<close>

lemma ksubst_id: \<open>(\<And>k. k \<in> ktv t \<Longrightarrow> \<phi> k = TK k) \<Longrightarrow> ksubst \<phi> t = t\<close>
proof (induction t arbitrary: \<phi>)
  case (TC c ts)
  have \<open>ksubst \<phi> t = t\<close> if \<open>t \<in> set ts\<close> for t
    by (rule TC.IH[OF that]) (use TC.prems that in fastforce)
  then show ?case by (simp add: map_idI)
next
  case (TDep i sg K e t)
  then show ?case by auto
next
  case (TAct l K e t)
  then show ?case by auto
qed auto

text \<open>Substitution commutes with the instantiation of abstract types when
  the substitution's range on the type's variables mentions none of the
  abstract types instantiated; the algorithm's escape check keeps a
  binder's abstract types out of every live type.\<close>

lemma tsubst_ksubst:
  assumes \<open>\<And>a k. a \<in> ftv t \<Longrightarrow> k \<in> ktv (\<theta> a) \<Longrightarrow> \<phi> k = TK k\<close>
  shows \<open>tsubst \<theta> \<rho> (ksubst \<phi> t) = ksubst (\<lambda>a. tsubst \<theta> \<rho> (\<phi> a)) (tsubst \<theta> \<rho> t)\<close>
  using assms
proof (induction t arbitrary: \<phi>)
  case (TV a)
  then show ?case by (simp add: ksubst_id[symmetric])
next
  case (TC c ts)
  have \<open>tsubst \<theta> \<rho> (ksubst \<phi> t) = ksubst (\<lambda>a. tsubst \<theta> \<rho> (\<phi> a)) (tsubst \<theta> \<rho> t)\<close>
    if \<open>t \<in> set ts\<close> for t
    by (rule TC.IH[OF that]) (use TC.prems that in fastforce)
  then show ?case by simp
next
  case (TDep i sg K e t)
  then show ?case by simp
next
  case (TEv l s t)
  have \<open>tsubst \<theta> \<rho> (ksubst \<phi> u) = ksubst (\<lambda>a. tsubst \<theta> \<rho> (\<phi> a)) (tsubst \<theta> \<rho> u)\<close>
    if \<open>u \<in> {l, s, t}\<close> for u
    using that TEv.IH TEv.prems by fastforce
  then show ?case by simp
next
  case (TAct l K e t)
  have \<open>tsubst \<theta> \<rho> (ksubst \<phi> u) = ksubst (\<lambda>a. tsubst \<theta> \<rho> (\<phi> a)) (tsubst \<theta> \<rho> u)\<close>
    if \<open>u \<in> {l, t}\<close> for u
    using that TAct.IH TAct.prems by fastforce
  then show ?case by simp
qed auto

text \<open>The abstract types a module-dependent arrow binds are positional: the
  \<open>i\<close>th abstract type of the binder \<open>d\<close> levels out is \<open>TA d i\<close>, as a scheme's
  bound variable is \<open>TB\<close>. The body of a binder is typed at free stamps
  \<open>TK K\<close> the derivation picks and closed at them when the arrow is formed
  (\<open>kclose\<close>), so the stamps themselves do not appear in the type and two
  arrows are equal exactly when their bodies are; an application opens the
  body at the realisation (\<open>kopen\<close>). Closing shifts the positions that are
  already free at its level and opening shifts them back, so a binder never
  captures a position it did not introduce and opening a closed body is the
  substitution of its stamps for \<^emph>\<open>every\<close> body (\<open>kopen_kclose\<close>). The images of a
  substitution have no free \<open>TA\<close> (\<open>taclosed\<close>), so the blind \<^const>\<open>tsubst\<close> and
  \<^const>\<open>bsubst\<close> cannot capture either.\<close>

fun tpos :: \<open>tvar \<Rightarrow> tvar list \<Rightarrow> nat option\<close> where
  \<open>tpos a [] = None\<close>
| \<open>tpos a (b # bs) = (if a = b then Some 0 else map_option Suc (tpos a bs))\<close>

lemma tpos_eq_None[simp]: \<open>tpos a K = None \<longleftrightarrow> a \<notin> set K\<close>
  by (induction K) auto

lemma tpos_notin[simp]: \<open>a \<notin> set K \<Longrightarrow> tpos a K = None\<close>
  by simp

lemma tpos_SomeD: \<open>tpos a K = Some i \<Longrightarrow> i < length K \<and> K ! i = a\<close>
  by (induction K arbitrary: i) (auto split: if_split_asm)

lemma tpos_nth[simp]: \<open>distinct K \<Longrightarrow> i < length K \<Longrightarrow> tpos (K ! i) K = Some i\<close>
  by (induction K arbitrary: i) (auto simp: nth_Cons split: nat.splits)

fun kclose_at :: \<open>nat \<Rightarrow> tvar list \<Rightarrow> kty \<Rightarrow> kty\<close> where
  \<open>kclose_at d K (TV a) = TV a\<close>
| \<open>kclose_at d K (TB a) = TB a\<close>
| \<open>kclose_at d K (TK a) = (case tpos a K of Some i \<Rightarrow> TA d i | None \<Rightarrow> TK a)\<close>
| \<open>kclose_at d K (TA k i) = TA (if d \<le> k then Suc k else k) i\<close>
| \<open>kclose_at d K (TC c ts) = TC c (map (kclose_at d K) ts)\<close>
| \<open>kclose_at d K (TApp t\<^sub>1 t\<^sub>2) = TApp (kclose_at d K t\<^sub>1) (kclose_at d K t\<^sub>2)\<close>
| \<open>kclose_at d K (TFn t\<^sub>1 e t\<^sub>2) = TFn (kclose_at d K t\<^sub>1) e (kclose_at d K t\<^sub>2)\<close>
| \<open>kclose_at d K (TDep i sg m e t) = TDep i sg m e (kclose_at (Suc d) K t)\<close>
| \<open>kclose_at d K (TEv l s t) = TEv (kclose_at d K l) (kclose_at d K s) (kclose_at d K t)\<close>
| \<open>kclose_at d K (TAct l K' e t) = TAct (kclose_at d K l) K' e (kclose_at d K t)\<close>
| \<open>kclose_at d K TRNil = TRNil\<close>
| \<open>kclose_at d K (TRCons l t r) = TRCons l (kclose_at d K t) (kclose_at d K r)\<close>

abbreviation kclose :: \<open>tvar list \<Rightarrow> kty \<Rightarrow> kty\<close> where
  \<open>kclose \<equiv> kclose_at 0\<close>

fun kopen_at :: \<open>nat \<Rightarrow> (nat \<Rightarrow> kty) \<Rightarrow> kty \<Rightarrow> kty\<close> where
  \<open>kopen_at d \<phi> (TV a) = TV a\<close>
| \<open>kopen_at d \<phi> (TB a) = TB a\<close>
| \<open>kopen_at d \<phi> (TK a) = TK a\<close>
| \<open>kopen_at d \<phi> (TA k i) = (if k = d then \<phi> i else if d < k then TA (k - 1) i else TA k i)\<close>
| \<open>kopen_at d \<phi> (TC c ts) = TC c (map (kopen_at d \<phi>) ts)\<close>
| \<open>kopen_at d \<phi> (TApp t\<^sub>1 t\<^sub>2) = TApp (kopen_at d \<phi> t\<^sub>1) (kopen_at d \<phi> t\<^sub>2)\<close>
| \<open>kopen_at d \<phi> (TFn t\<^sub>1 e t\<^sub>2) = TFn (kopen_at d \<phi> t\<^sub>1) e (kopen_at d \<phi> t\<^sub>2)\<close>
| \<open>kopen_at d \<phi> (TDep i sg m e t) = TDep i sg m e (kopen_at (Suc d) \<phi> t)\<close>
| \<open>kopen_at d \<phi> (TEv l s t) = TEv (kopen_at d \<phi> l) (kopen_at d \<phi> s) (kopen_at d \<phi> t)\<close>
| \<open>kopen_at d \<phi> (TAct l K e t) = TAct (kopen_at d \<phi> l) K e (kopen_at d \<phi> t)\<close>
| \<open>kopen_at d \<phi> TRNil = TRNil\<close>
| \<open>kopen_at d \<phi> (TRCons l t r) = TRCons l (kopen_at d \<phi> t) (kopen_at d \<phi> r)\<close>

abbreviation kopen :: \<open>(nat \<Rightarrow> kty) \<Rightarrow> kty \<Rightarrow> kty\<close> where
  \<open>kopen \<equiv> kopen_at 0\<close>

text \<open>\<open>taok d t\<close>: every \<open>TA\<close> of \<open>t\<close> is bound by a binder of \<open>t\<close> or by one of
  the \<open>d\<close> binders around it. A type of a derivation is \<open>taclosed\<close>.\<close>

fun taok :: \<open>nat \<Rightarrow> kty \<Rightarrow> bool\<close> where
  \<open>taok d (TV a) = True\<close>
| \<open>taok d (TB a) = True\<close>
| \<open>taok d (TK a) = True\<close>
| \<open>taok d (TA k i) \<longleftrightarrow> k < d\<close>
| \<open>taok d (TC c ts) = list_all (taok d) ts\<close>
| \<open>taok d (TApp t\<^sub>1 t\<^sub>2) \<longleftrightarrow> taok d t\<^sub>1 \<and> taok d t\<^sub>2\<close>
| \<open>taok d (TFn t\<^sub>1 e t\<^sub>2) \<longleftrightarrow> taok d t\<^sub>1 \<and> taok d t\<^sub>2\<close>
| \<open>taok d (TDep i sg m e t) = taok (Suc d) t\<close>
| \<open>taok d (TEv l s t) \<longleftrightarrow> taok d l \<and> taok d s \<and> taok d t\<close>
| \<open>taok d (TAct l K e t) \<longleftrightarrow> taok d l \<and> taok d t\<close>
| \<open>taok d TRNil = True\<close>
| \<open>taok d (TRCons l t r) \<longleftrightarrow> taok d t \<and> taok d r\<close>

abbreviation taclosed :: \<open>kty \<Rightarrow> bool\<close> where
  \<open>taclosed \<equiv> taok 0\<close>

lemma taok_mono: \<open>taok d t \<Longrightarrow> d \<le> d' \<Longrightarrow> taok d' t\<close>
  by (induction t arbitrary: d d') (auto simp: list_all_iff)

lemma taclosed_taok[simp]: \<open>taclosed t \<Longrightarrow> taok d t\<close>
  by (rule taok_mono) auto

lemma ktv_kclose[simp]: \<open>ktv (kclose_at d K t) = ktv t - set K\<close>
  by (induction t arbitrary: d) (auto split: option.split dest: tpos_SomeD)

lemma ftv_kclose[simp]: \<open>ftv (kclose_at d K t) = ftv t\<close>
  by (induction t arbitrary: d) (auto split: option.split)

lemma frv_kclose[simp]: \<open>frv (kclose_at d K t) = frv t\<close>
  by (induction t arbitrary: d) (auto split: option.split)

lemma btv_kclose[simp]: \<open>btv (kclose_at d K t) = btv t\<close>
  by (induction t arbitrary: d) (auto split: option.split)

lemma brv_kclose[simp]: \<open>brv (kclose_at d K t) = brv t\<close>
  by (induction t arbitrary: d) (auto split: option.split)

lemma taok_kclose: \<open>taok d t \<Longrightarrow> taok (Suc d) (kclose_at d K t)\<close>
  by (induction t arbitrary: d) (auto simp: list_all_iff split: option.split)

text \<open>Opening adds only the variables of the realisation.\<close>

lemma ftv_kopen: \<open>ftv (kopen_at d \<phi> t) \<subseteq> ftv t \<union> (\<Union>i. ftv (\<phi> i))\<close>
proof (induction t arbitrary: d)
  case (TC c ts) then show ?case by fastforce
next
  case (TEv l s t) then show ?case by fastforce
qed auto

lemma frv_kopen: \<open>frv (kopen_at d \<phi> t) \<subseteq> frv t \<union> (\<Union>i. frv (\<phi> i))\<close>
proof (induction t arbitrary: d)
  case (TC c ts) then show ?case by fastforce
next
  case (TEv l s t) then show ?case by fastforce
qed auto

lemma ktv_kopen: \<open>ktv (kopen_at d \<phi> t) \<subseteq> ktv t \<union> (\<Union>i. ktv (\<phi> i))\<close>
proof (induction t arbitrary: d)
  case (TC c ts) then show ?case by fastforce
next
  case (TEv l s t) then show ?case by fastforce
qed auto

lemma btv_kopen: \<open>btv (kopen_at d \<phi> t) \<subseteq> btv t \<union> (\<Union>i. btv (\<phi> i))\<close>
proof (induction t arbitrary: d)
  case (TC c ts) then show ?case by fastforce
next
  case (TEv l s t) then show ?case by fastforce
qed auto

lemma brv_kopen: \<open>brv (kopen_at d \<phi> t) \<subseteq> brv t \<union> (\<Union>i. brv (\<phi> i))\<close>
proof (induction t arbitrary: d)
  case (TC c ts) then show ?case by fastforce
next
  case (TEv l s t) then show ?case by fastforce
qed auto

lemma taok_kopen:
  assumes \<open>\<And>i. taclosed (\<phi> i)\<close>
  shows \<open>taok (Suc d) t \<Longrightarrow> taok d (kopen_at d \<phi> t)\<close>
  using assms by (induction t arbitrary: d) (auto simp: list_all_iff)

lemma kopen_id: \<open>taok d t \<Longrightarrow> kopen_at d \<phi> t = t\<close>
  by (induction t arbitrary: d) (auto simp: list_all_iff intro!: map_idI)

lemma kopen_closed: \<open>taclosed t \<Longrightarrow> kopen_at d \<phi> t = t\<close>
  by (rule kopen_id) simp

lemma taok_ksubst: \<open>taok d t \<Longrightarrow> (\<And>k. taclosed (\<phi> k)) \<Longrightarrow> taok d (ksubst \<phi> t)\<close>
  by (induction t arbitrary: d) (auto simp: list_all_iff intro: taok_mono)  (* ~6s *)

lemma taok_tsubst:
  \<open>taok d t \<Longrightarrow> (\<And>a. taclosed (\<theta> a)) \<Longrightarrow> taok d (tsubst \<theta> \<rho> t)\<close>
  by (induction t arbitrary: d) (auto simp: list_all_iff intro: taok_mono)  (* ~5s *)

lemma taok_bsubst:
  \<open>taok d t \<Longrightarrow> (\<And>a. taclosed (\<theta> a)) \<Longrightarrow> taok d (bsubst \<theta> \<rho> t)\<close>
  by (induction t arbitrary: d) (auto simp: list_all_iff intro: taok_mono)  (* ~5s *)

text \<open>Closing commutes with a substitution whose range avoids the closed
  stamps (the escape check), opening with any substitution whose range has no
  free bound abstract type (every type of a derivation).\<close>

lemma fpull_kclose:
  \<open>fpull l u = Some (t', r') \<Longrightarrow>
     fpull l (kclose_at d K u) = Some (kclose_at d K t', kclose_at d K r')\<close>
  by (rule fpull_map) simp_all

lemma fpull_kopen:
  \<open>fpull l u = Some (t', r') \<Longrightarrow>
     fpull l (kopen_at d \<phi> u) = Some (kopen_at d \<phi> t', kopen_at d \<phi> r')\<close>
  by (rule fpull_map) simp_all

lemma ty_eq_kclose: \<open>t \<simeq> u \<Longrightarrow> kclose_at d K t \<simeq> kclose_at d K u\<close>
proof (induction t arbitrary: u d)
  case (TC c ts)
  then obtain us where us: \<open>u = TC c us\<close> \<open>ts [\<simeq>] us\<close> by auto
  from TC.IH us(2) have \<open>map (kclose_at d K) ts [\<simeq>] map (kclose_at d K) us\<close>
    by (induction ts arbitrary: us) auto
  then show ?case using us(1) by simp
next
  case (TRCons l t r)
  then obtain t' r' where p: \<open>fpull l u = Some (t', r')\<close> and \<open>t \<simeq> t'\<close> \<open>r \<simeq> r'\<close> by auto
  then show ?case by (auto simp: fpull_kclose[OF p] intro!: TRCons.IH)
qed (auto split: option.split)

lemma ty_eq_kopen: \<open>t \<simeq> u \<Longrightarrow> kopen_at d \<phi> t \<simeq> kopen_at d \<phi> u\<close>
proof (induction t arbitrary: u d)
  case (TC c ts)
  then obtain us where us: \<open>u = TC c us\<close> \<open>ts [\<simeq>] us\<close> by auto
  from TC.IH us(2) have \<open>map (kopen_at d \<phi>) ts [\<simeq>] map (kopen_at d \<phi>) us\<close>
    by (induction ts arbitrary: us) auto
  then show ?case using us(1) by simp
next
  case (TRCons l t r)
  then obtain t' r' where p: \<open>fpull l u = Some (t', r')\<close> and \<open>t \<simeq> t'\<close> \<open>r \<simeq> r'\<close> by auto
  then show ?case by (auto simp: fpull_kopen[OF p] intro!: TRCons.IH)
qed auto

lemma kopen_cong:
  \<open>(\<And>i. \<phi> i = \<psi> i) \<Longrightarrow> kopen_at d \<phi> t = kopen_at d \<psi> t\<close>
  by (induction t arbitrary: d) (auto intro!: map_cong)

lemma kclose_id: \<open>set K \<inter> ktv t = {} \<Longrightarrow> taok d t \<Longrightarrow> kclose_at d K t = t\<close>
  by (induction t arbitrary: d) (auto simp: list_all_iff intro!: map_idI split: option.split, blast)

lemma tsubst_kclose:
  assumes \<open>\<And>a. a \<in> ftv t \<Longrightarrow> set K \<inter> ktv (\<theta> a) = {}\<close> \<open>\<And>a. a \<in> ftv t \<Longrightarrow> taclosed (\<theta> a)\<close>
  shows \<open>tsubst \<theta> \<rho> (kclose_at d K t) = kclose_at d K (tsubst \<theta> \<rho> t)\<close>
  using assms by (induction t arbitrary: d) (auto simp: kclose_id split: option.split, blast)

lemma tsubst_kopen:
  assumes \<open>\<And>a. taclosed (\<theta> a)\<close>
  shows \<open>tsubst \<theta> \<rho> (kopen_at d \<phi> t) =
         kopen_at d (\<lambda>i. tsubst \<theta> \<rho> (\<phi> i)) (tsubst \<theta> \<rho> t)\<close>
  by (induction t arbitrary: d) (auto simp: kopen_closed[OF assms])

lemma bsubst_kopen:
  assumes \<open>\<And>a. taclosed (\<theta> a)\<close>
  shows \<open>bsubst \<theta> \<rho> (kopen_at d \<phi> t) =
         kopen_at d (\<lambda>i. bsubst \<theta> \<rho> (\<phi> i)) (bsubst \<theta> \<rho> t)\<close>
  by (induction t arbitrary: d) (auto simp: kopen_closed[OF assms])

text \<open>Opening the body a binder closed realises the stamps it closed: the
  point of the sort. No hygiene is needed -- the bound stamps are positions,
  so a binder inside the body cannot capture them.\<close>

lemma kopen_kclose:
  \<open>kopen_at d \<phi> (kclose_at d K t) =
   ksubst (\<lambda>k. case tpos k K of Some i \<Rightarrow> \<phi> i | None \<Rightarrow> TK k) t\<close>
  by (induction t arbitrary: d) (auto split: option.split)

text \<open>Substitution: congruence, identity, the free and bound variables of a
  substituted type.\<close>

lemma rsubst_cong:
  \<open>(\<And>v. v \<in> frv_row r \<Longrightarrow> \<rho> v = \<rho>' v) \<Longrightarrow> rsubst \<rho> r = rsubst \<rho>' r\<close>
  by (induction r) auto

lemma tsubst_cong:
  \<open>(\<And>a. a \<in> ftv t \<Longrightarrow> \<theta> a = \<theta>' a) \<Longrightarrow> (\<And>v. v \<in> frv t \<Longrightarrow> \<rho> v = \<rho>' v) \<Longrightarrow>
   tsubst \<theta> \<rho> t = tsubst \<theta>' \<rho>' t\<close>
  by (induction t) (auto intro!: rsubst_cong cong: map_cong, blast)

lemma rsubst_id_on:
  \<open>(\<And>v. v \<in> frv_row r \<Longrightarrow> \<rho> v = RV v) \<Longrightarrow> rsubst \<rho> r = r\<close>
  by (subst rsubst_cong[of r \<rho> RV]) (auto simp: rsubst_id)

lemma tsubst_id_on:
  \<open>(\<And>a. a \<in> ftv t \<Longrightarrow> \<theta> a = TV a) \<Longrightarrow> (\<And>v. v \<in> frv t \<Longrightarrow> \<rho> v = RV v) \<Longrightarrow> tsubst \<theta> \<rho> t = t\<close>
  by (subst tsubst_cong[of t \<theta> TV \<rho> RV]) (auto simp: tsubst_id)

lemma ftv_tsubst: \<open>ftv (tsubst \<theta> \<rho> t) = (\<Union>a\<in>ftv t. ftv (\<theta> a))\<close>
  by (induction t) auto

lemma frv_rsubst: \<open>frv_row (rsubst \<rho> r) = (\<Union>v\<in>frv_row r. frv_row (\<rho> v))\<close>
  by (induction r) auto

lemma brv_rsubst: \<open>brv_row (rsubst \<rho> r) = brv_row r \<union> (\<Union>v\<in>frv_row r. brv_row (\<rho> v))\<close>
  by (induction r) auto

lemma btv_tsubst: \<open>btv (tsubst \<theta> \<rho> t) = btv t \<union> (\<Union>a\<in>ftv t. btv (\<theta> a))\<close>
  by (induction t) auto

lemma brv_tsubst:
  \<open>brv (tsubst \<theta> \<rho> t) = brv t \<union> (\<Union>a\<in>ftv t. brv (\<theta> a)) \<union> (\<Union>v\<in>frv t. brv_row (\<rho> v))\<close>
  by (induction t) (auto simp: brv_rsubst)

lemma brv_brsubst: \<open>brv_row (brsubst \<rho> r) = (\<Union>v\<in>brv_row r. brv_row (\<rho> v))\<close>
  by (induction r) auto

lemma btv_bsubst: \<open>btv (bsubst \<theta> \<rho> t) = (\<Union>a\<in>btv t. btv (\<theta> a))\<close>
  by (induction t) auto

lemma brv_bsubst: \<open>brv (bsubst \<theta> \<rho> t) = (\<Union>a\<in>btv t. brv (\<theta> a)) \<union> (\<Union>v\<in>brv t. brv_row (\<rho> v))\<close>
  by (induction t) (auto simp: brv_brsubst)

lemma brsubst_cong: \<open>(\<And>v. v \<in> brv_row r \<Longrightarrow> \<rho> v = \<rho>' v) \<Longrightarrow> brsubst \<rho> r = brsubst \<rho>' r\<close>
  by (induction r) auto

lemma bsubst_cong_eq:
  \<open>(\<And>a. a \<in> btv t \<Longrightarrow> \<theta> a = \<theta>' a) \<Longrightarrow> (\<And>v. v \<in> brv t \<Longrightarrow> \<rho> v = \<rho>' v) \<Longrightarrow> bsubst \<theta> \<rho> t = bsubst \<theta>' \<rho>' t\<close>
proof (induction t)
  case (TC c ts)
  have \<open>bsubst \<theta> \<rho> u = bsubst \<theta>' \<rho>' u\<close> if \<open>u \<in> set ts\<close> for u
    by (rule TC.IH[OF that]) (use TC.prems that in auto)
  then show ?case by (simp cong: map_cong)
qed (auto intro!: brsubst_cong)

text \<open>An instance of a generalised scheme is a monotype: it has no bound
  variables of its own. Without the restriction a scheme could be
  instantiated at a bound variable a monotype in scope happens to mention,
  and generalising that monotype would capture it.\<close>

fun sinst :: \<open>scheme \<Rightarrow> kty \<Rightarrow> bool\<close>  (infix \<open>\<succeq>\<close> 50) where
  sinst_Sch: \<open>Sch t \<succeq> \<tau> \<longleftrightarrow> btv \<tau> = {} \<and> brv \<tau> = {} \<and> (\<exists>\<theta> \<rho>. bsubst \<theta> \<rho> t = \<tau> \<and> (\<forall>a. taclosed (\<theta> a)))\<close>
| \<open>Mono t \<succeq> \<tau> \<longleftrightarrow> \<tau> = t\<close>

text \<open>The defining equation of \<open>\<succeq>\<close> for a generalised scheme is an
  existential and useless as a rewrite; proofs go through the matcher
  below.\<close>

declare sinst_Sch[simp del]

lemma sinst_refl[simp, intro!]: \<open>kmono \<tau> \<succeq> \<tau>\<close>
  by simp

fun ftv_sch :: \<open>scheme \<Rightarrow> tvar set\<close> where
  \<open>ftv_sch (Sch t) = ftv t\<close>
| \<open>ftv_sch (Mono t) = ftv t\<close>

fun frv_sch :: \<open>scheme \<Rightarrow> rvar set\<close> where
  \<open>frv_sch (Sch t) = frv t\<close>
| \<open>frv_sch (Mono t) = frv t\<close>

fun sch_body :: \<open>scheme \<Rightarrow> kty\<close> where
  \<open>sch_body (Sch t) = t\<close>
| \<open>sch_body (Mono t) = t\<close>

subsection \<open>Tuples as records\<close>

text \<open>The structural functions pass through a tuple field by field, and two
  tuples are equal types exactly when their components are.\<close>

lemma ftv_tuple_from[simp]: \<open>ftv (tuple_from i ts) = \<Union>(set (map ftv ts))\<close>
  by (induction ts arbitrary: i) simp_all

lemma frv_tuple_from[simp]: \<open>frv (tuple_from i ts) = \<Union>(set (map frv ts))\<close>
  by (induction ts arbitrary: i) simp_all

lemma btv_tuple_from[simp]: \<open>btv (tuple_from i ts) = \<Union>(set (map btv ts))\<close>
  by (induction ts arbitrary: i) simp_all

lemma brv_tuple_from[simp]: \<open>brv (tuple_from i ts) = \<Union>(set (map brv ts))\<close>
  by (induction ts arbitrary: i) simp_all

lemma ktv_tuple_from[simp]: \<open>ktv (tuple_from i ts) = \<Union>(set (map ktv ts))\<close>
  by (induction ts arbitrary: i) simp_all

lemma tsubst_tuple_from[simp]:
  \<open>tsubst \<theta> \<rho> (tuple_from i ts) = tuple_from i (map (tsubst \<theta> \<rho>) ts)\<close>
  by (induction ts arbitrary: i) simp_all

lemma bsubst_tuple_from[simp]:
  \<open>bsubst \<theta> \<rho> (tuple_from i ts) = tuple_from i (map (bsubst \<theta> \<rho>) ts)\<close>
  by (induction ts arbitrary: i) simp_all

lemma ty_eq_tuple_from[simp]: \<open>tuple_from i ts \<simeq> tuple_from i us \<longleftrightarrow> ts [\<simeq>] us\<close>
proof (induction ts arbitrary: i us)
  case Nil
  then show ?case by (cases us) simp_all
next
  case Cons
  then show ?case by (cases us) simp_all
qed

end
