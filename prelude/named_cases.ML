(* Stable case names for the induction and case rules of fun/function. *)

signature NAMED_CASES =
sig
  val derive: string list -> thm -> string list
  val expand_prefixes: Proof.context -> string list -> string list
  val named_cases: Proof.context -> string list -> thm -> thm
end

structure Named_Cases: NAMED_CASES =
struct

(* the label of constructor in a case name *)
fun const_label c =
  (case c of
    \<^const_name>\<open>Groups.zero_class.zero\<close> => "0"
  | \<^const_name>\<open>Groups.one_class.one\<close> => "1"
  | \<^const_name>\<open>Num.numeral_class.numeral\<close> => "num"
  | \<^const_name>\<open>Char\<close> => "chr"
  | _ => Long_Name.base_name c)

(* the head of a pattern *)
fun head t =
  (case strip_comb t of
    (Const (c, _), args) => SOME (c, args)
  | _ => NONE)

(* disc ts, for patterns ts indexed by case *)
fun disc (ts: (int * term) list) : (int * string list) list =
  let
    val idx = map fst ts
    val classes = map (apsnd head) ts
    val consts = distinct (op =) (map_filter (Option.map fst o snd) classes)
    val uniform = length consts = 1 andalso forall (is_some o snd) classes
    fun sub c =
      let val members = map_filter (fn (i, SOME (c', args)) =>
            if c' = c then SOME (i, args) else NONE | _ => NONE) classes
      in if length members < 2 then map (rpair []) (map fst members)
         else disc_args members end
    val own = map (fn (i, h) => (i, case h of SOME (c, _) =>
                 if uniform orelse c = \<^const_name>\<open>Pair\<close> then [] else [const_label c]
               | NONE => [])) classes
    val rest = maps sub consts
  in map (fn i => (i, the (AList.lookup (op =) own i) @
                      the_default [] (AList.lookup (op =) rest i))) idx end
(* disc_args members, for the argument lists of patterns with one constructor *)
and disc_args (members: (int * term list) list) =
  let
    val n = length (snd (hd members))
    val per = map (fn p => disc (map (fn (i, args) => (i, nth args p)) members))
      (0 upto n - 1)
  in map (fn (i, _) => (i, maps (fn d => the (AList.lookup (op =) d i)) per)) members end

(* case_shape thesis prem, ?P and args of:
   - \<And>xs. H \<Longrightarrow> ?P args (an induction rule) or
   - \<And>xs. x = (args) \<Longrightarrow> H \<Longrightarrow> ?thesis (a case rule) *)
fun case_shape thesis prem =
  let
    val concl = HOLogic.dest_Trueprop (Logic.strip_imp_concl (Term.strip_all_body prem))
      handle TERM _ => Logic.strip_imp_concl (Term.strip_all_body prem)
    val (P, args) = strip_comb concl
  in
    if P aconv thesis then
      (case Logic.strip_imp_prems (Term.strip_all_body prem) of
        eq :: _ => (P, HOLogic.strip_tuple (snd (HOLogic.dest_eq (HOLogic.dest_Trueprop eq))))
      | [] => (P, []))
    else (P, args)
  end

(* case_shape of each case of rule (consumes premises) *)
fun case_shapes th =
  let
    val (_, consumes) = Rule_Cases.get th
    val thesis = HOLogic.dest_Trueprop (Thm.concl_of th) handle TERM _ => Thm.concl_of th
  in map (case_shape thesis) (drop consumes (Thm.prems_of th)) end

(* components shapes per case index (in order) *)
fun components shapes =
  let
    val indexed = map_index I shapes
    fun of_pred P =
      let
        val members = filter (fn (_, (Q, _)) => Q aconv P) indexed
        val n = length (snd (snd (hd members)))
        val per = map (fn p => disc (map (fn (i, (_, args)) => (i, nth args p)) members))
          (0 upto n - 1)
      in map (fn (i, _) => (i, map (fn d => the (AList.lookup (op =) d i)) per)) members end
  in sort (int_ord o apply2 fst) (maps of_pred (distinct (op aconv) (map fst shapes))) end

fun drop_positions name_of comps =
  let
    val npos = fold (fn (_, cs) => fn m => Int.max (m, length cs)) comps 0
    fun drop_pos p comps =
      fold (fn (i, cs) => fn acc =>
        let
          val cs' = map_index (fn (q, c) => if q = p then [] else c) cs
          val cand = name_of i cs'
          val others = map (fn (j, ds) => name_of j ds) (filter (fn (j, _) => j <> i) acc)
        in
          if p < length cs andalso not (null (flat cs')) andalso not (member (op =) others cand)
          then AList.update (op =) (i, cs') acc else acc
        end) comps comps
  in fold drop_pos (0 upto npos - 1) comps end

(* number the names that are still equal *)
fun dedup names =
  let
    fun go (n :: ns) seen =
          let val k = length (filter (fn m => m = n) seen)
          in
            (if k = 0 andalso not (member (op =) ns n) then n
             else n ^ "_" ^ string_of_int (k + 1)) :: go ns (n :: seen)
          end
      | go [] _ = []
  in go names [] end

fun derive prefixes th =
  let
    val shapes = case_shapes th
    (* the predicates in the order of the functions' declaration, which is the order of the
       prefixes: the function package names them ?P, ?Q, \<dots> or ?P1, ?P2, \<dots> in that order,
       whereas their first appearance in the cases follows the equations *)
    fun pred_ord (Var ((a, i), _), Var ((b, j), _)) =
          prod_ord int_ord (prod_ord string_ord int_ord) ((size a, (a, i)), (size b, (b, j)))
      | pred_ord _ = EQUAL
    val preds = sort pred_ord (distinct (op aconv) (map fst shapes))
    fun prefix_of P =
      if null prefixes then "" else nth prefixes (find_index (fn Q => Q aconv P) preds)
    fun name_of i cs =
      space_implode "_" (filter_out (fn s => s = "") (prefix_of (fst (nth shapes i)) :: flat cs))
    val full = components shapes
    val names = map (uncurry name_of) (drop_positions name_of full)
    fun clashes n = length (filter (fn m => m = n) names) > 1
    fun spelled (i, cs) = name_of i (map (fn [] => ["any"] | c => c) cs)
  in dedup (map2 (fn n => fn c => if clashes n then spelled c else n) names full) end

fun expand_prefixes ctxt [f] =
      (let
         val fs = #fs (Function.get_info ctxt (Syntax.read_term ctxt f))
       in
         if length fs < 2 then []
         else map (Long_Name.base_name o fst o dest_Const o head_of) fs
       end
       handle ERROR _ => [f] | Empty => [f])
  | expand_prefixes _ prefixes = prefixes

fun named_cases ctxt prefixes th =
  Rule_Cases.name (derive (expand_prefixes ctxt prefixes) th) th

end

val _ = Theory.setup
  (Attrib.setup \<^binding>\<open>named_cases\<close>
    (Scan.lift (Scan.repeat Args.name) >> (fn prefixes => Thm.rule_attribute [] (fn context =>
      Named_Cases.named_cases (Context.proof_of context) prefixes)))
    "derive stable case names for fun/function induction and case rules")
