theory Grammar
  imports LR_Parser.LR_Parser Lexer_Correct CaraML_Syntax.Module_Expressions CaraML_Spec.Pipeline
begin

section \<open>Decoding\<close>

text \<open>The decoders of the grammar below build the AST of \<^theory>\<open>CaraML_Syntax.Module_Expressions\<close>
  from token spans, with the readers of \<^theory>\<open>CaraML_Parser.Lexer\<close> for literal
  values, selector and operator names (\<open>grammar.md\<close> \<section>7).\<close>

subsection \<open>Tokens\<close>

type_synonym ctok = \<open>(trivia, tok, nat) token\<close>

definition loc_of_span :: \<open>nat span \<Rightarrow> loc\<close> where
  \<open>loc_of_span s = \<lparr> l_line = s_line s, l_col = s_col s,
                      l_off = s_off s, l_len = s_len s \<rparr>\<close>

definition nm_of_span :: \<open>nat span \<Rightarrow> nm\<close> where
  \<open>nm_of_span s = \<lparr> l_line = s_line s, l_col = s_col s,
                     l_off = s_off s, l_len = s_len s, n_txt = s_txt s \<rparr>\<close>

lemma truncate_nm_of_span[simp]: \<open>loc.truncate (nm_of_span s) = loc_of_span s\<close>
  by (simp add: nm_of_span_def loc_of_span_def loc.defs)

definition tloc :: \<open>ctok \<Rightarrow> loc\<close> where
  \<open>tloc t = loc_of_span (Token.span t)\<close>

definition tnm :: \<open>ctok \<Rightarrow> nm\<close> where
  \<open>tnm t = nm_of_span (Token.span t)\<close>

definition ttxt :: \<open>ctok \<Rightarrow> ustring\<close> where
  \<open>ttxt t = s_txt (Token.span t)\<close>

text \<open>A selector's name drops its dot, an operator's its backticks; an extern's
  symbol is its decoded text.\<close>

definition sel_nm :: \<open>ctok \<Rightarrow> nm\<close> where
  \<open>sel_nm t = n_txt_update (\<lambda>_. sel_name (ttxt t)) (tnm t)\<close>

definition op_nm :: \<open>ctok \<Rightarrow> nm\<close> where
  \<open>op_nm t = n_txt_update (\<lambda>_. op_name (ttxt t)) (tnm t)\<close>

definition str_text :: \<open>ctok \<Rightarrow> ustring\<close> where
  \<open>str_text t = concat (map (\<lambda>p. case p of Txt cs \<Rightarrow> cs | Hole _ \<Rightarrow> []) (str_pieces (ttxt t)))\<close>

definition str_nm :: \<open>ctok \<Rightarrow> nm\<close> where
  \<open>str_nm t = n_txt_update (\<lambda>_. str_text t) (tnm t)\<close>

text \<open>A reserved name introduced by the decoders sits at the token it comes from.\<close>

definition rnm :: \<open>ctok \<Rightarrow> string \<Rightarrow> nm\<close> where
  \<open>rnm t s = n_txt_update (\<lambda>_. str s) (tnm t)\<close>

definition p1 :: \<open>nm \<Rightarrow> mpath\<close> where
  \<open>p1 x = MkPath [x]\<close>

definition path_snoc :: \<open>mpath \<Rightarrow> nm \<Rightarrow> mpath\<close> where
  \<open>path_snoc p x = (case p of MkPath xs \<Rightarrow> MkPath (xs @ [x]))\<close>

definition upper :: \<open>nm \<Rightarrow> bool\<close> where
  \<open>upper x = (case n_txt x of c # _ \<Rightarrow> 0x41 \<le> c \<and> c \<le> 0x5A | [] \<Rightarrow> False)\<close>

definition wild :: \<open>nm \<Rightarrow> bool\<close> where
  \<open>wild x \<longleftrightarrow> n_txt x = str ''_''\<close>

subsection \<open>Literals\<close>

definition int_atom :: \<open>ctok \<Rightarrow> matom\<close> where
  \<open>int_atom t = (case int_of_lexeme (ttxt t) of (v, sfx) \<Rightarrow> ANum (tloc t) v sfx)\<close>

definition int_pat :: \<open>ctok \<Rightarrow> mpatom\<close> where
  \<open>int_pat t = (case int_of_lexeme (ttxt t) of (v, sfx) \<Rightarrow> PNum (tloc t) v sfx)\<close>

text \<open>An interpolated string is \<open>%cat [s\<^sub>0, %show x\<^sub>1, s\<^sub>1, \<dots>]\<close>.\<close>

definition interp :: \<open>ctok \<Rightarrow> matom\<close> where
  \<open>interp t = AParen [ESpine [APath (p1 (rnm t ''%cat'')), AList (map (\<lambda>p. case p of
       Txt cs \<Rightarrow> ESpine [AStr (tloc t) cs]
     | Hole xs \<Rightarrow> ESpine [APath (p1 (rnm t ''%show'')),
                          APath (MkPath (map (\<lambda>x. n_txt_update (\<lambda>_. x) (tnm t)) xs))])
     (str_pieces (ttxt t)))]]\<close>

subsection \<open>Chains\<close>

text \<open>An operator chain as parsed: the operands with the operator after each, then
  the last operand.\<close>

type_synonym chain = \<open>(matom list \<times> nm) list \<times> matom list\<close>

definition chain_to :: \<open>(matom list \<times> nm) list \<Rightarrow> expr \<Rightarrow> expr\<close> where
  \<open>chain_to pre e = foldr (\<lambda>(ats, opr) r. EOp ats opr r) pre e\<close>

definition expr_of_chain :: \<open>chain \<Rightarrow> expr\<close> where
  \<open>expr_of_chain c = chain_to (fst c) (ESpine (snd c))\<close>

text \<open>The decoders build a pair-valued result as a literal pair and read a child's
  pair only through a definition: the relation's introduction rules then match the
  decoded values.\<close>

definition chain_ops :: \<open>chain \<Rightarrow> nm \<Rightarrow> (matom list \<times> nm) list\<close> where
  \<open>chain_ops c opr = fst c @ [(snd c, opr)]\<close>

definition chain_kw :: \<open>chain \<Rightarrow> nm \<Rightarrow> expr \<Rightarrow> expr\<close> where
  \<open>chain_kw c opr e = chain_to (chain_ops c opr) e\<close>

definition atom_of_expr :: \<open>expr \<Rightarrow> matom\<close> where
  \<open>atom_of_expr e = (case e of ESpine [a] \<Rightarrow> a | _ \<Rightarrow> AParen [e])\<close>

definition atom_of_spine :: \<open>matom list \<Rightarrow> matom\<close> where
  \<open>atom_of_spine ats = atom_of_expr (ESpine ats)\<close>

subsection \<open>Sugar\<close>

text \<open>\<open>(P : S)\<close> is a module atom when \<open>P\<close> is a bare module path (rule 3 of
  \<open>grammar.md\<close>), an error otherwise.\<close>

definition amod :: \<open>chain \<Rightarrow> msig \<Rightarrow> matom\<close> where
  \<open>amod c s = (case c of
     ([], [APath (MkPath xs)]) \<Rightarrow> if xs \<noteq> [] \<and> upper (last xs) then AMod (MkPath xs) s else AParen [EErr]
   | _ \<Rightarrow> AParen [EErr])\<close>

text \<open>\<open>(x \<oplus>)\<close> is \<open>(\<oplus>) x\<close>; \<open>(\<oplus> x)\<close> is \<open>let %s = x\<close> then \<open>\<lambda>%t -> %t \<oplus> %s\<close>.\<close>

definition lsection :: \<open>chain \<Rightarrow> ctok \<Rightarrow> matom\<close> where
  \<open>lsection c t = AParen [ESpine [APath (p1 (op_nm t)), atom_of_expr (expr_of_chain c)]]\<close>

definition rsection :: \<open>ctok \<Rightarrow> expr \<Rightarrow> matom\<close> where
  \<open>rsection t e = AParen [ELet (PatApp [PQid (p1 (rnm t ''%s''))]) e
     (EFn [PatApp [PQid (p1 (rnm t ''%t''))]]
        (EOp [APath (p1 (rnm t ''%t''))] (op_nm t) (ESpine [APath (p1 (rnm t ''%s''))])))]\<close>

definition lam :: \<open>mpatom list \<Rightarrow> expr \<Rightarrow> expr\<close> where
  \<open>lam ps e = foldr (\<lambda>p r. EFn [PatApp [p]] r) ps e\<close>

definition ann :: \<open>ty option \<Rightarrow> expr \<Rightarrow> expr\<close> where
  \<open>ann t e = (case t of None \<Rightarrow> e | Some \<tau> \<Rightarrow> EAnn e \<tau>)\<close>

text \<open>The guards of the alternative \<open>| _\<close>, the otherwise alternative, are empty.\<close>

definition alt_gs :: \<open>expr list \<Rightarrow> expr list\<close> where
  \<open>alt_gs gs = (case gs of [ESpine [APath (MkPath [x])]] \<Rightarrow> if wild x then [] else gs
               | _ \<Rightarrow> gs)\<close>

subsection \<open>Types\<close>

text \<open>A record domain of one name-typed field is the dependent name arrow (rule 4).\<close>

definition tarrow :: \<open>tatom list \<Rightarrow> ty option \<times> ty \<Rightarrow> ty\<close> where
  \<open>tarrow ts rt = TArrow ts (fst rt) (snd rt)\<close>

definition arrow :: \<open>tatom list \<Rightarrow> ty option \<times> ty \<Rightarrow> ty\<close> where
  \<open>arrow ts rt = (case (ts, rt) of
     ([TParen [TRec [(f, TSpine [TName e])] None]], (r, t)) \<Rightarrow> TArrowName f e r t
   | (_, (r, t)) \<Rightarrow> TArrow ts r t)\<close>

definition row1 :: \<open>tatom list \<Rightarrow> ty\<close> where
  \<open>row1 e = TRow [TSpine e] None\<close>

definition lid_ty :: \<open>ctok \<Rightarrow> ty\<close> where
  \<open>lid_ty x = TSpine [TPath (p1 (tnm x))]\<close>

subsection \<open>Left-hand sides\<close>

text \<open>A left-hand side is parsed as a chain and read as a pattern, or as a clause head
  (\<open>grammar.md\<close> \<section>7).\<close>

fun pat_of_expr :: \<open>expr \<Rightarrow> mpat option\<close>
and pat_of_atom :: \<open>matom \<Rightarrow> mpatom option\<close>
where
  \<open>pat_of_expr (ESpine as) = map_option PatApp (those (map pat_of_atom as))\<close>
| \<open>pat_of_expr (EOp as opr e) =
     (case (those (map pat_of_atom as), pat_of_expr e) of
        (Some ps, Some p) \<Rightarrow> Some (PatOp ps opr p) | _ \<Rightarrow> None)\<close>
| \<open>pat_of_expr (EAnn e t) = map_option (\<lambda>p. PatAnn p t) (pat_of_expr e)\<close>
| \<open>pat_of_expr _ = None\<close>
| \<open>pat_of_atom (APath (MkPath xs)) =
     Some (case xs of [x] \<Rightarrow> if wild x then PWild x else PQid (MkPath xs) | _ \<Rightarrow> PQid (MkPath xs))\<close>
| \<open>pat_of_atom (ANum l v s) = Some (PNum l v s)\<close>
| \<open>pat_of_atom (AStr l cs) = Some (PStr l cs)\<close>
| \<open>pat_of_atom (AChar l c) = Some (PChar l c)\<close>
| \<open>pat_of_atom (AParen es) = map_option PParen (those (map pat_of_expr es))\<close>
| \<open>pat_of_atom (AList es) = map_option PList (those (map pat_of_expr es))\<close>
| \<open>pat_of_atom (ARec fs) =
     map_option (\<lambda>ps. PRec (zip (map fst fs) ps) False) (those (map (\<lambda>(_, e). pat_of_expr e) fs))\<close>
| \<open>pat_of_atom _ = None\<close>

definition pat_of_spine :: \<open>matom list \<Rightarrow> mpat option\<close> where
  \<open>pat_of_spine ats = pat_of_expr (ESpine ats)\<close>

fun binder_of :: \<open>matom \<Rightarrow> mbind option\<close> where
  \<open>binder_of (AMod (MkPath [m]) s) = Some (BMod m s)\<close>
| \<open>binder_of (ABind m s) = Some (BImp m s)\<close>
| \<open>binder_of _ = None\<close>

datatype lhs = LhsFun nm \<open>mbind list\<close> \<open>mpat list\<close> | LhsPat mpat | LhsErr

definition fun_name :: \<open>nm \<Rightarrow> bool\<close> where
  \<open>fun_name f \<longleftrightarrow> \<not> wild f \<and> \<not> upper f\<close>

definition head_lhs :: \<open>nm \<Rightarrow> matom list \<Rightarrow> lhs\<close> where
  \<open>head_lhs f args =
     (let bs = takeWhile (\<lambda>a. binder_of a \<noteq> None) args;
          ps = dropWhile (\<lambda>a. binder_of a \<noteq> None) args
      in case those (map pat_of_atom ps) of
           Some ps' \<Rightarrow> LhsFun f (map (the \<circ> binder_of) bs) (map (\<lambda>p. PatApp [p]) ps')
         | None \<Rightarrow> LhsErr)\<close>

definition pat_lhs :: \<open>chain \<Rightarrow> lhs\<close> where
  \<open>pat_lhs c = (case pat_of_expr (expr_of_chain c) of Some p \<Rightarrow> LhsPat p | None \<Rightarrow> LhsErr)\<close>

definition lhs_of :: \<open>chain \<Rightarrow> lhs\<close> where
  \<open>lhs_of c = (case c of
     ([], APath (MkPath [f]) # args) \<Rightarrow> if fun_name f then head_lhs f args else pat_lhs c
   | ([(a, opr)], b) \<Rightarrow>
       (case (pat_of_spine a, pat_of_spine b) of
          (Some p, Some q) \<Rightarrow> LhsFun opr [] [p, q]
        | _ \<Rightarrow> LhsErr)
   | _ \<Rightarrow> pat_lhs c)\<close>

definition decl_of :: \<open>chain \<Rightarrow> ty option \<Rightarrow> expr \<Rightarrow> mdecl\<close> where
  \<open>decl_of c t e = (case lhs_of c of LhsFun f bs ps \<Rightarrow> DFun f bs [(ps, ann t e)] | _ \<Rightarrow> DErr)\<close>

datatype lbind = LFun nm \<open>mbind list\<close> \<open>mpat list \<times> expr\<close> | LPat mpat expr | LErr

definition bind_of :: \<open>chain \<Rightarrow> ty option \<Rightarrow> expr \<Rightarrow> lbind\<close> where
  \<open>bind_of c t e = (case lhs_of c of
     LhsFun f bs ps \<Rightarrow> LFun f bs (ps, ann t e) | LhsPat p \<Rightarrow> LPat p (ann t e) | LhsErr \<Rightarrow> LErr)\<close>

subsection \<open>Bodies\<close>

text \<open>A body decodes right-nested; it ends in an expression statement.\<close>

datatype stmt = SLet \<open>lbind list\<close> | SWithN nm expr | SWith expr | SExpr expr

fun let_wrap :: \<open>lbind \<Rightarrow> expr \<Rightarrow> expr\<close> where
  \<open>let_wrap (LFun f bs cl) r = ELetFun f bs [cl] r\<close>
| \<open>let_wrap (LPat p e) r = ELet p e r\<close>
| \<open>let_wrap LErr r = EErr\<close>

fun stmt_wrap :: \<open>stmt \<Rightarrow> expr \<Rightarrow> expr\<close> where
  \<open>stmt_wrap (SLet bs) r = foldr let_wrap bs r\<close>
| \<open>stmt_wrap (SWithN x h) r = EWith x h r\<close>
| \<open>stmt_wrap (SWith (EHandlerN cls)) r = EHandle r cls\<close>
| \<open>stmt_wrap (SWith h) r = ESpine [atom_of_expr h, AParen [EFn [PatApp [PParen []]] r]]\<close>
| \<open>stmt_wrap (SExpr e) r = ESeq e r\<close>

fun body_expr :: \<open>stmt list \<Rightarrow> expr\<close> where
  \<open>body_expr [] = EErr\<close>
| \<open>body_expr [SExpr e] = e\<close>
| \<open>body_expr [_] = EErr\<close>
| \<open>body_expr (s # ss) = stmt_wrap s (body_expr ss)\<close>

section \<open>Grammar\<close>

text \<open>The grammar of \<open>grammar.md\<close> \<section>5 in the encoding of the \<^theory_text>\<open>grammar\<close>
  command \<^cite>\<open>adams2013\<close>. The owner of a block item puts \<open>\<^sup>=\<close> on its first symbol
  and \<open>\<^sup>>\<close> on the rest; a continuation nonterminal uses \<open>\<^sup>\<ge>\<close> throughout and is
  referenced with \<open>\<^sup>>\<close>; a bracket opener is \<open>\<^sup>=\<close>, its contents \<open>\<^sup>*\<close>, its closer
  \<open>\<^sup>>\<close>. Repetitions are left-recursive nonterminals, and a few forms are factored
  for LR(1):
  \<^item> a declaration's left-hand side is a \<open>DChain\<close>, whose first atom is a name;
  \<^item> \<open>[ Eff ]\<close> is \<open>BrEff\<close>, the common prefix of a one-entry row and a name type;
    after an arrow, \<open>ArrTail\<close> reads it once and the next token decides (rule 5);
  \<^item> a constructor's arguments, and the rest of an arrow type after \<open>-> [E]\<close>, are
    pinned to the constructor and to the bracket (\<open>grammar.md\<close> \<section>2).\<close>

grammar (relation) caraml =
  tokens \<open>ctok\<close>
  terminals
    "let" = KLet and "with" = KWith and "if" = KIf and "then" = KThen and "else" = KElse and
    "match" = KMatch and "handler" = KHandler and "mask" = KMask and "return" = KReturn and
    "finally" = KFinally and "as" = KAs and "type" = KType and "extern" = KExtern and
    "infixl" = KInfixl and "infixr" = KInfixr and "infix" = KInfix and "effect" = KEffect and
    "module" = KModule and "signature" = KSignature and "instance" = KInstance and
    "open" = KOpen and "include" = KInclude and
    "=" = Assign and ":" = Colon and "->" = Arrow and "|" = Bar and "," = Comma and ";" = Semi and
    "(" = LP and ")" = RP and "[" = LB and "]" = RB and "{" = LC and "}" = RC and
    "\<lambda>" = KLambda
  productions
      File :: \<open>mdecl list\<close>
        =                                   \<Rightarrow> \<open>[]\<close>
        | Decls^=                           \<Rightarrow> \<open>\<lambda>ds. ds\<close>
        | "{"^= "}"^>                       \<Rightarrow> \<open>[]\<close>
        | "{"^= DItems^* "}"^>              \<Rightarrow> \<open>\<lambda>ds. ds\<close>
        | "{"^= DItems^* ";"^* "}"^>        \<Rightarrow> \<open>\<lambda>ds. ds\<close>
    and
      Decls :: \<open>mdecl list\<close>
        = Decl^=                            \<Rightarrow> \<open>\<lambda>d. [d]\<close>
        | Decls^= Decl^=                    \<Rightarrow> \<open>\<lambda>ds d. ds @ [d]\<close>
    and
      DItems :: \<open>mdecl list\<close>
        = Decl^*                            \<Rightarrow> \<open>\<lambda>d. [d]\<close>
        | DItems^* ";"^* Decl^*             \<Rightarrow> \<open>\<lambda>ds d. ds @ [d]\<close>
    and
      Decl :: \<open>mdecl\<close>
        = DBind^=                           \<Rightarrow> \<open>\<lambda>d. d\<close>
        | "extern"^= LId^> ":"^> Ty^> "="^> StrL^>
            \<Rightarrow> \<open>\<lambda>x t s. DExtern (tnm x) t (str_nm s)\<close>
        | "type"^= LId^> TVars^> "="^> Ty^> \<Rightarrow> \<open>\<lambda>x vs t. DType (tnm x) vs t\<close>
        | "type"^= LId^> TVars^> "="^> Ctors^>
            \<Rightarrow> \<open>\<lambda>x vs cs. DData (tnm x) vs cs\<close>
        | Fixity^= IntL^> Op^>              \<Rightarrow> \<open>\<lambda>f p q. DFix f (tnm p) (op_nm q)\<close>
        | Fixity^= IntL^> LId^>             \<Rightarrow> \<open>\<lambda>f p q. DFix f (tnm p) (tnm q)\<close>
        | "effect"^= UId^> TVars^> OpBlock^>
            \<Rightarrow> \<open>\<lambda>e vs ops. DEff (tnm e) vs ops\<close>
        | "module"^= UId^> Params^> SigAnn^> "="^> MExpr^>
            \<Rightarrow> \<open>\<lambda>m ps s me. DMod (tnm m) ps s me\<close>
        | "signature"^= UId^> "="^> Sig^>   \<Rightarrow> \<open>\<lambda>s sg. DSig (tnm s) sg\<close>
        | "instance"^= UId^> Params^> SigAnn^> "="^> MExpr^>
            \<Rightarrow> \<open>\<lambda>m ps s me. DImpl (tnm m) ps s me\<close>
        | "open"^= UPath^>                  \<Rightarrow> \<open>\<lambda>p. DOpen p\<close>
        | "include"^= MAtom^>               \<Rightarrow> \<open>\<lambda>m. DInc m\<close>
    and
      Fixity :: \<open>fixity\<close>
        = "infixl"^=                        \<Rightarrow> \<open>FixL\<close>
        | "infixr"^=                        \<Rightarrow> \<open>FixR\<close>
        | "infix"^=                         \<Rightarrow> \<open>FixN\<close>
    and
      DBind :: \<open>mdecl\<close>
        = DChain^= RhsEq^>                  \<Rightarrow> \<open>\<lambda>c e. decl_of c None e\<close>
        | DChain^= ":"^> Ty^> RhsEq^>       \<Rightarrow> \<open>\<lambda>c t e. decl_of c (Some t) e\<close>
    and
      DChain :: \<open>chain\<close>
        = DOperand^=                        \<Rightarrow> \<open>\<lambda>q. ([], q)\<close>
        | DChain^= Op^> Operand^>           \<Rightarrow> \<open>\<lambda>c p q. (chain_ops c (op_nm p), q)\<close>
    and
      DOperand :: \<open>matom list\<close>
        = DSpine^=                          \<Rightarrow> \<open>\<lambda>s. s\<close>
        | DOperand^= LSel^>                 \<Rightarrow> \<open>\<lambda>q l. [ADot (atom_of_spine q) l]\<close>
        | DOperand^= LSel^> Spine^>         \<Rightarrow> \<open>\<lambda>q l s. ADot (atom_of_spine q) l # s\<close>
    and
      DSpine :: \<open>matom list\<close>
        = DAtom^=                           \<Rightarrow> \<open>\<lambda>a. [a]\<close>
        | DSpine^= Atom^>                   \<Rightarrow> \<open>\<lambda>s a. s @ [a]\<close>
        | DSpine^= Binder^>                 \<Rightarrow> \<open>\<lambda>s a. s @ [a]\<close>
    and
      DAtom :: \<open>matom\<close>
        = DBase^=                           \<Rightarrow> \<open>\<lambda>a. a\<close>
        | DAtom^= TSel^>                    \<Rightarrow> \<open>\<lambda>a l. ADot a l\<close>
    and
      DBase :: \<open>matom\<close>
        = LId^=                             \<Rightarrow> \<open>\<lambda>x. APath (p1 (tnm x))\<close>
        | KWild^=                             \<Rightarrow> \<open>\<lambda>x. APath (p1 (tnm x))\<close>
        | "("^= Op^* ")"^>                  \<Rightarrow> \<open>\<lambda>q. APath (p1 (op_nm q))\<close>
    and
      Ctors :: \<open>(nm \<times> tatom list) list\<close>
        = Ctor^>=                           \<Rightarrow> \<open>\<lambda>c. [c]\<close>
        | Ctors^>= "|"^>= Ctor^>=           \<Rightarrow> \<open>\<lambda>cs c. cs @ [c]\<close>
    and
      Ctor :: \<open>nm \<times> tatom list\<close>
        = UId^= TAtoms^>=                   \<Rightarrow> \<open>\<lambda>c as. (tnm c, as)\<close>
        | "("^= Op^* ")"^>= TAtoms^>=       \<Rightarrow> \<open>\<lambda>q as. (op_nm q, as)\<close>
    and
      OpBlock :: \<open>(nm \<times> ty) list\<close>
        = OpSpecs^=                         \<Rightarrow> \<open>\<lambda>os. os\<close>
        | "{"^= "}"^>                       \<Rightarrow> \<open>[]\<close>
        | "{"^= OpItems^* "}"^>             \<Rightarrow> \<open>\<lambda>os. os\<close>
        | "{"^= OpItems^* ";"^* "}"^>       \<Rightarrow> \<open>\<lambda>os. os\<close>
    and
      OpSpecs :: \<open>(nm \<times> ty) list\<close>
        = OpSpec^=                          \<Rightarrow> \<open>\<lambda>q. [q]\<close>
        | OpSpecs^= OpSpec^=                \<Rightarrow> \<open>\<lambda>os q. os @ [q]\<close>
    and
      OpItems :: \<open>(nm \<times> ty) list\<close>
        = OpSpec^*                          \<Rightarrow> \<open>\<lambda>q. [q]\<close>
        | OpItems^* ";"^* OpSpec^*          \<Rightarrow> \<open>\<lambda>os q. os @ [q]\<close>
    and
      OpSpec :: \<open>nm \<times> ty\<close>
        = LId^= ":"^> Ty^>                  \<Rightarrow> \<open>\<lambda>x t. (tnm x, t)\<close>
    and
      Params :: \<open>(nm \<times> msig) list\<close>
        =                                   \<Rightarrow> \<open>[]\<close>
        | Params^>= "("^>= UId^* ":"^* Sig^* ")"^>=
            \<Rightarrow> \<open>\<lambda>ps m s. ps @ [(tnm m, s)]\<close>
    and
      SigAnn :: \<open>msig option\<close>
        =                                   \<Rightarrow> \<open>None\<close>
        | ":"^>= SigAtom^>=                 \<Rightarrow> \<open>\<lambda>s. Some s\<close>
    \<comment> \<open>Module expressions and signatures\<close>
    and
      MExpr :: \<open>mexpr\<close>
        = MApp^=                            \<Rightarrow> \<open>\<lambda>m. m\<close>
        | MApp^= ":"^> Sig^>                \<Rightarrow> \<open>\<lambda>m s. MSeal m s\<close>
        | Decls^=                           \<Rightarrow> \<open>\<lambda>ds. MStruct ds\<close>
    and
      MApp :: \<open>mexpr\<close>
        = MAtom^=                           \<Rightarrow> \<open>\<lambda>m. m\<close>
        | MApp^= MAtom^>                    \<Rightarrow> \<open>\<lambda>f m. MApp f m\<close>
    and
      MAtom :: \<open>mexpr\<close>
        = UPath^=                           \<Rightarrow> \<open>\<lambda>p. MPath p\<close>
        | "("^= MExpr^* ")"^>               \<Rightarrow> \<open>\<lambda>m. m\<close>
        | "{"^= "}"^>                       \<Rightarrow> \<open>MStruct []\<close>
        | "{"^= DItems^* "}"^>              \<Rightarrow> \<open>\<lambda>ds. MStruct ds\<close>
        | "{"^= DItems^* ";"^* "}"^>        \<Rightarrow> \<open>\<lambda>ds. MStruct ds\<close>
    and
      UPath :: \<open>mpath\<close>
        = UId^=                             \<Rightarrow> \<open>\<lambda>x. p1 (tnm x)\<close>
        | UPath^= TSelU^>                   \<Rightarrow> \<open>\<lambda>p x. path_snoc p (sel_nm x)\<close>
    and
      Sig :: \<open>msig\<close>
        = SigAtom^=                         \<Rightarrow> \<open>\<lambda>s. s\<close>
        | Specs^=                           \<Rightarrow> \<open>\<lambda>ss. SLit ss\<close>
    and
      SigAtom :: \<open>msig\<close>
        = UPath^=                           \<Rightarrow> \<open>\<lambda>p. SPath p []\<close>
        | UPath^= "["^> Refns^* "]"^>       \<Rightarrow> \<open>\<lambda>p rs. SPath p rs\<close>
        | "{"^= "}"^>                       \<Rightarrow> \<open>SLit []\<close>
        | "{"^= SpItems^* "}"^>             \<Rightarrow> \<open>\<lambda>ss. SLit ss\<close>
        | "{"^= SpItems^* ";"^* "}"^>       \<Rightarrow> \<open>\<lambda>ss. SLit ss\<close>
    and
      Refns :: \<open>mrefn list\<close>
        = Refn^*                            \<Rightarrow> \<open>\<lambda>r. [r]\<close>
        | Refns^* ","^* Refn^*              \<Rightarrow> \<open>\<lambda>rs r. rs @ [r]\<close>
    and
      Refn :: \<open>mrefn\<close>
        = LId^* "="^* Ty^*                  \<Rightarrow> \<open>\<lambda>x t. RType (tnm x) t\<close>
        | UId^* "="^* UPath^*               \<Rightarrow> \<open>\<lambda>m p. RMod (tnm m) p\<close>
    and
      Specs :: \<open>mspec list\<close>
        = Spec^=                            \<Rightarrow> \<open>\<lambda>s. [s]\<close>
        | Specs^= Spec^=                    \<Rightarrow> \<open>\<lambda>ss s. ss @ [s]\<close>
    and
      SpItems :: \<open>mspec list\<close>
        = Spec^*                            \<Rightarrow> \<open>\<lambda>s. [s]\<close>
        | SpItems^* ";"^* Spec^*            \<Rightarrow> \<open>\<lambda>ss s. ss @ [s]\<close>
    and
      Spec :: \<open>mspec\<close>
        = "type"^= LId^> TVars^>            \<Rightarrow> \<open>\<lambda>x vs. SpType (tnm x) vs None\<close>
        | "type"^= LId^> TVars^> "="^> Ty^> \<Rightarrow> \<open>\<lambda>x vs t. SpType (tnm x) vs (Some t)\<close>
        | "type"^= LId^> TVars^> "="^> Ctors^>
            \<Rightarrow> \<open>\<lambda>x vs cs. SpData (tnm x) vs cs\<close>
        | Head^= ":"^> Ty^>                 \<Rightarrow> \<open>\<lambda>x t. SpVal x t\<close>
        | "effect"^= UId^> TVars^> OpBlock^>
            \<Rightarrow> \<open>\<lambda>e vs ops. SpEff (tnm e) vs ops\<close>
        | Fixity^= IntL^> Op^>              \<Rightarrow> \<open>\<lambda>f p q. SpFix f (tnm p) (op_nm q)\<close>
        | Fixity^= IntL^> LId^>             \<Rightarrow> \<open>\<lambda>f p q. SpFix f (tnm p) (tnm q)\<close>
        | "module"^= UId^> ":"^> Sig^>      \<Rightarrow> \<open>\<lambda>m s. SpMod (tnm m) s\<close>
        | "include"^= SigAtom^>             \<Rightarrow> \<open>\<lambda>s. SpInc s\<close>
    and
      Head :: \<open>nm\<close>
        = LId^=                             \<Rightarrow> \<open>\<lambda>x. tnm x\<close>
        | "("^= Op^* ")"^>                  \<Rightarrow> \<open>\<lambda>q. op_nm q\<close>
    and
      TVars :: \<open>nm list\<close>
        =                                   \<Rightarrow> \<open>[]\<close>
        | TVars^>= LId^>=                   \<Rightarrow> \<open>\<lambda>vs x. vs @ [tnm x]\<close>
    \<comment> \<open>Types\<close>
    and
      Ty :: \<open>ty\<close>
        = TyNB^=                            \<Rightarrow> \<open>\<lambda>t. t\<close>
        | NameTy^=                          \<Rightarrow> \<open>\<lambda>e. TSpine [TName e]\<close>
        | NameTy^= "->"^> ArrTail^>         \<Rightarrow> \<open>\<lambda>e rt. tarrow [TName e] rt\<close>
    and
      TyNB :: \<open>ty\<close>
        = TSpine^=                          \<Rightarrow> \<open>\<lambda>ts. TSpine ts\<close>
        | TSpine^= "->"^> ArrTail^>         \<Rightarrow> \<open>\<lambda>ts rt. arrow ts rt\<close>
        | MBind^= "->"^> Ty^>               \<Rightarrow> \<open>\<lambda>b t. TArrowMod b t\<close>
        | "handler"^= NameTy^> TSpine^> "->"^> TSpine^>
            \<Rightarrow> \<open>\<lambda>e a r. THand e a None r\<close>
        | "handler"^= NameTy^> TSpine^> "->"^> Row^> TSpine^>
            \<Rightarrow> \<open>\<lambda>e a w r. THand e a (Some w) r\<close>
    and
      ArrTail :: \<open>ty option \<times> ty\<close>
        = TyNB^>=                           \<Rightarrow> \<open>\<lambda>t. (None, t)\<close>
        | RowNB^>= Ty^>=                    \<Rightarrow> \<open>\<lambda>w t. (Some w, t)\<close>
        | BrEff^=                           \<Rightarrow> \<open>\<lambda>e. (None, TSpine [TName e])\<close>
        | BrEff^= "->"^>= ArrTail^>=        \<Rightarrow> \<open>\<lambda>e rt. (None, tarrow [TName e] rt)\<close>
        | BrEff^= Ty^>=                     \<Rightarrow> \<open>\<lambda>e t. (Some (row1 e), t)\<close>
    and
      Row :: \<open>ty\<close>
        = RowNB^=                           \<Rightarrow> \<open>\<lambda>w. w\<close>
        | BrEff^=                           \<Rightarrow> \<open>\<lambda>e. row1 e\<close>
    and
      RowNB :: \<open>ty\<close>
        = "["^= "]"^>                       \<Rightarrow> \<open>TRow [] None\<close>
        | "["^= LId^* "]"^>                 \<Rightarrow> \<open>\<lambda>x. TRow [lid_ty x] None\<close>
        | "["^= REnts^* ","^* REnt^* "]"^>  \<Rightarrow> \<open>\<lambda>rs r. TRow (rs @ [r]) None\<close>
        | "["^= REnts^* "|"^* Ty^* "]"^>    \<Rightarrow> \<open>\<lambda>rs t. TRow rs (Some t)\<close>
    and
      BrEff :: \<open>tatom list\<close>
        = "["^= Eff^* "]"^>                 \<Rightarrow> \<open>\<lambda>e. e\<close>
    and
      NameTy :: \<open>tatom list\<close>
        = BrEff^=                           \<Rightarrow> \<open>\<lambda>e. e\<close>
    and
      REnts :: \<open>ty list\<close>
        = REnt^*                            \<Rightarrow> \<open>\<lambda>r. [r]\<close>
        | REnts^* ","^* REnt^*              \<Rightarrow> \<open>\<lambda>rs r. rs @ [r]\<close>
    and
      REnt :: \<open>ty\<close>
        = Eff^*                             \<Rightarrow> \<open>\<lambda>e. TSpine e\<close>
        | LId^*                             \<Rightarrow> \<open>\<lambda>x. lid_ty x\<close>
    and
      Eff :: \<open>tatom list\<close>
        = UPath^* TAtoms^*                  \<Rightarrow> \<open>\<lambda>p as. TPath p # as\<close>
    and
      MBind :: \<open>mbind\<close>
        = "("^= UId^* ":"^* Sig^* ")"^>     \<Rightarrow> \<open>\<lambda>m s. BMod (tnm m) s\<close>
        | "{"^= UId^* ":"^* Sig^* "}"^>     \<Rightarrow> \<open>\<lambda>m s. BImp (tnm m) s\<close>
    and
      TSpine :: \<open>tatom list\<close>
        = TAtom^=                           \<Rightarrow> \<open>\<lambda>a. [a]\<close>
        | TSpine^= TAtom^>                  \<Rightarrow> \<open>\<lambda>ts a. ts @ [a]\<close>
    and
      TAtoms :: \<open>tatom list\<close>
        =                                   \<Rightarrow> \<open>[]\<close>
        | TAtoms^>= TAtom^>=                \<Rightarrow> \<open>\<lambda>ts a. ts @ [a]\<close>
    and
      TAtom :: \<open>tatom\<close>
        = TPath^=                           \<Rightarrow> \<open>\<lambda>p. TPath p\<close>
        | KWild^=                             \<Rightarrow> \<open>\<lambda>x. TWild (tnm x)\<close>
        | "("^= ")"^>                       \<Rightarrow> \<open>TParen []\<close>
        | "("^= Tys^* ")"^>                 \<Rightarrow> \<open>\<lambda>ts. TParen ts\<close>
        | "("^= TFields^* ")"^>             \<Rightarrow> \<open>\<lambda>fs. TParen [TRec fs None]\<close>
        | "("^= TFields^* "|"^* Ty^* ")"^>  \<Rightarrow> \<open>\<lambda>fs t. TParen [TRec fs (Some t)]\<close>
    and
      Tys :: \<open>ty list\<close>
        = Ty^*                              \<Rightarrow> \<open>\<lambda>t. [t]\<close>
        | Tys^* ","^* Ty^*                  \<Rightarrow> \<open>\<lambda>ts t. ts @ [t]\<close>
    and
      TFields :: \<open>(nm \<times> ty) list\<close>
        = LId^* ":"^* Ty^*                  \<Rightarrow> \<open>\<lambda>x t. [(tnm x, t)]\<close>
        | TFields^* ","^* LId^* ":"^* Ty^*  \<Rightarrow> \<open>\<lambda>fs x t. fs @ [(tnm x, t)]\<close>
    and
      TPath :: \<open>mpath\<close>
        = LId^=                             \<Rightarrow> \<open>\<lambda>x. p1 (tnm x)\<close>
        | UPath^= TSelL^>                   \<Rightarrow> \<open>\<lambda>p x. path_snoc p (sel_nm x)\<close>
    \<comment> \<open>Bindings and bodies\<close>
    and
      RhsEq :: \<open>expr\<close>
        = "="^>= Body^>=                    \<Rightarrow> \<open>\<lambda>e. e\<close>
        | AltsEq^=                          \<Rightarrow> \<open>\<lambda>as. EGuards as\<close>
    and
      AltsEq :: \<open>(expr list \<times> expr) list\<close>
        = AltEq^=                           \<Rightarrow> \<open>\<lambda>a. [a]\<close>
        | AltsEq^= AltEq^=                  \<Rightarrow> \<open>\<lambda>as a. as @ [a]\<close>
    and
      AltEq :: \<open>expr list \<times> expr\<close>
        = "|"^= Guards^> "="^> Expr^>       \<Rightarrow> \<open>\<lambda>gs e. (alt_gs gs, e)\<close>
    and
      RhsArrow :: \<open>expr\<close>
        = "->"^>= Body^>=                   \<Rightarrow> \<open>\<lambda>e. e\<close>
        | AltsArrow^=                       \<Rightarrow> \<open>\<lambda>as. EGuards as\<close>
    and
      AltsArrow :: \<open>(expr list \<times> expr) list\<close>
        = AltArrow^=                        \<Rightarrow> \<open>\<lambda>a. [a]\<close>
        | AltsArrow^= AltArrow^=            \<Rightarrow> \<open>\<lambda>as a. as @ [a]\<close>
    and
      AltArrow :: \<open>expr list \<times> expr\<close>
        = "|"^= Guards^> "->"^> Expr^>      \<Rightarrow> \<open>\<lambda>gs e. (alt_gs gs, e)\<close>
    and
      Guards :: \<open>expr list\<close>
        = Guard^>=                          \<Rightarrow> \<open>\<lambda>g. [g]\<close>
        | Guards^>= ","^>= Guard^>=         \<Rightarrow> \<open>\<lambda>gs g. gs @ [g]\<close>
    and
      Guard :: \<open>expr\<close>
        = Chain^>=                          \<Rightarrow> \<open>\<lambda>c. expr_of_chain c\<close>
        | Chain^>= ":"^>= TSpine^>=         \<Rightarrow> \<open>\<lambda>c ts. EAnn (expr_of_chain c) (TSpine ts)\<close>
    and
      Body :: \<open>expr\<close>
        = Stmts^=                           \<Rightarrow> \<open>\<lambda>ss. body_expr ss\<close>
        | "{"^= SItems^* "}"^>              \<Rightarrow> \<open>\<lambda>ss. body_expr ss\<close>
        | "{"^= SItems^* ";"^* "}"^>        \<Rightarrow> \<open>\<lambda>ss. body_expr ss\<close>
    and
      Stmts :: \<open>stmt list\<close>
        = Stmt^=                            \<Rightarrow> \<open>\<lambda>s. [s]\<close>
        | Stmts^= Stmt^=                    \<Rightarrow> \<open>\<lambda>ss s. ss @ [s]\<close>
    and
      SItems :: \<open>stmt list\<close>
        = Stmt^*                            \<Rightarrow> \<open>\<lambda>s. [s]\<close>
        | SItems^* ";"^* Stmt^*             \<Rightarrow> \<open>\<lambda>ss s. ss @ [s]\<close>
    and
      Stmt :: \<open>stmt\<close>
        = "let"^= BindBlock^>               \<Rightarrow> \<open>\<lambda>bs. SLet bs\<close>
        | "with"^= LId^> "="^> Expr^>       \<Rightarrow> \<open>\<lambda>x e. SWithN (tnm x) e\<close>
        | "with"^= Expr^>                   \<Rightarrow> \<open>\<lambda>e. SWith e\<close>
        | Expr^=                            \<Rightarrow> \<open>\<lambda>e. SExpr e\<close>
    and
      BindBlock :: \<open>lbind list\<close>
        = Binds^=                           \<Rightarrow> \<open>\<lambda>bs. bs\<close>
        | "{"^= BItems^* "}"^>              \<Rightarrow> \<open>\<lambda>bs. bs\<close>
        | "{"^= BItems^* ";"^* "}"^>        \<Rightarrow> \<open>\<lambda>bs. bs\<close>
    and
      Binds :: \<open>lbind list\<close>
        = Bind^=                            \<Rightarrow> \<open>\<lambda>b. [b]\<close>
        | Binds^= Bind^=                    \<Rightarrow> \<open>\<lambda>bs b. bs @ [b]\<close>
    and
      BItems :: \<open>lbind list\<close>
        = Bind^*                            \<Rightarrow> \<open>\<lambda>b. [b]\<close>
        | BItems^* ";"^* Bind^*             \<Rightarrow> \<open>\<lambda>bs b. bs @ [b]\<close>
    and
      Bind :: \<open>lbind\<close>
        = Chain^= RhsEq^>                   \<Rightarrow> \<open>\<lambda>c e. bind_of c None e\<close>
        | Chain^= ":"^> Ty^> RhsEq^>        \<Rightarrow> \<open>\<lambda>c t e. bind_of c (Some t) e\<close>
    \<comment> \<open>Expressions\<close>
    and
      Expr :: \<open>expr\<close>
        = Chain^=                           \<Rightarrow> \<open>\<lambda>c. expr_of_chain c\<close>
        | Chain^= ":"^> Ty^>                \<Rightarrow> \<open>\<lambda>c t. EAnn (expr_of_chain c) t\<close>
        | KwExpr^=                          \<Rightarrow> \<open>\<lambda>e. e\<close>
        | Chain^= Op^> KwExpr^>             \<Rightarrow> \<open>\<lambda>c p e. chain_kw c (op_nm p) e\<close>
    and
      Chain :: \<open>chain\<close>
        = Operand^=                         \<Rightarrow> \<open>\<lambda>q. ([], q)\<close>
        | Chain^= Op^> Operand^>            \<Rightarrow> \<open>\<lambda>c p q. (chain_ops c (op_nm p), q)\<close>
    and
      Operand :: \<open>matom list\<close>
        = Spine^=                           \<Rightarrow> \<open>\<lambda>s. s\<close>
        | Operand^= LSel^>                  \<Rightarrow> \<open>\<lambda>q l. [ADot (atom_of_spine q) l]\<close>
        | Operand^= LSel^> Spine^>          \<Rightarrow> \<open>\<lambda>q l s. ADot (atom_of_spine q) l # s\<close>
    and
      LSel :: \<open>nm\<close>
        = LSelL^=                           \<Rightarrow> \<open>\<lambda>x. sel_nm x\<close>
        | LSelU^=                           \<Rightarrow> \<open>\<lambda>x. sel_nm x\<close>
        | LSelN^=                           \<Rightarrow> \<open>\<lambda>x. sel_nm x\<close>
    and
      Spine :: \<open>matom list\<close>
        = Atom^=                            \<Rightarrow> \<open>\<lambda>a. [a]\<close>
        | Spine^= Atom^>                    \<Rightarrow> \<open>\<lambda>s a. s @ [a]\<close>
        | Spine^= Binder^>                  \<Rightarrow> \<open>\<lambda>s a. s @ [a]\<close>
    and
      Binder :: \<open>matom\<close>
        = "{"^= UId^* ":"^* Sig^* "}"^>     \<Rightarrow> \<open>\<lambda>m s. ABind (tnm m) s\<close>
    and
      Atom :: \<open>matom\<close>
        = UPath^=                           \<Rightarrow> \<open>\<lambda>p. APath p\<close>
        | SelAtom^=                         \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      SelAtom :: \<open>matom\<close>
        = SelBase^=                         \<Rightarrow> \<open>\<lambda>a. a\<close>
        | SelAtom^= TSel^>                  \<Rightarrow> \<open>\<lambda>a l. ADot a l\<close>
    and
      TSel :: \<open>nm\<close>
        = TSelL^=                           \<Rightarrow> \<open>\<lambda>x. sel_nm x\<close>
        | TSelU^=                           \<Rightarrow> \<open>\<lambda>x. sel_nm x\<close>
        | TSelN^=                           \<Rightarrow> \<open>\<lambda>x. sel_nm x\<close>
    and
      SelBase :: \<open>matom\<close>
        = LId^=                             \<Rightarrow> \<open>\<lambda>x. APath (p1 (tnm x))\<close>
        | UPath^= TSelL^>                   \<Rightarrow> \<open>\<lambda>p x. APath (path_snoc p (sel_nm x))\<close>
        | KWild^=                             \<Rightarrow> \<open>\<lambda>x. APath (p1 (tnm x))\<close>
        | IntL^=                            \<Rightarrow> \<open>\<lambda>n. int_atom n\<close>
        | FloatL^=                          \<Rightarrow> \<open>\<lambda>n. AFloat (tnm n)\<close>
        | StrL^=                            \<Rightarrow> \<open>\<lambda>s. AStr (tloc s) (str_text s)\<close>
        | StrI^=                            \<Rightarrow> \<open>\<lambda>s. interp s\<close>
        | CharL^=                           \<Rightarrow> \<open>\<lambda>c. AChar (tloc c) (char_value (ttxt c))\<close>
        | "["^= "]"^>                       \<Rightarrow> \<open>AList []\<close>
        | "["^= Exprs^* "]"^>               \<Rightarrow> \<open>\<lambda>es. AList es\<close>
        | ParenBase^=                       \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      ParenBase :: \<open>matom\<close>
        = "("^= ")"^>                       \<Rightarrow> \<open>AParen []\<close>
        | "("^= Expr^* ")"^>                \<Rightarrow> \<open>\<lambda>e. AParen [e]\<close>
        | "("^= Expr^* ","^* Exprs^* ")"^>  \<Rightarrow> \<open>\<lambda>e es. AParen (e # es)\<close>
        | "("^= Fields^* ")"^>              \<Rightarrow> \<open>\<lambda>fs. ARec fs\<close>
        | "("^= Chain^* ":"^* SigAtom^* ")"^>
            \<Rightarrow> \<open>\<lambda>c s. amod c s\<close>
        | "("^= Op^* ")"^>                  \<Rightarrow> \<open>\<lambda>q. APath (p1 (op_nm q))\<close>
        | "("^= Chain^* Op^* ")"^>          \<Rightarrow> \<open>\<lambda>c q. lsection c q\<close>
        | "("^= Op^* Expr^* ")"^>           \<Rightarrow> \<open>\<lambda>q e. rsection q e\<close>
    and
      Fields :: \<open>(nm \<times> expr) list\<close>
        = LId^* "="^* Expr^*                \<Rightarrow> \<open>\<lambda>x e. [(tnm x, e)]\<close>
        | Fields^* ","^* LId^* "="^* Expr^* \<Rightarrow> \<open>\<lambda>fs x e. fs @ [(tnm x, e)]\<close>
    and
      Exprs :: \<open>expr list\<close>
        = Expr^*                            \<Rightarrow> \<open>\<lambda>e. [e]\<close>
        | Exprs^* ","^* Expr^*              \<Rightarrow> \<open>\<lambda>es e. es @ [e]\<close>
    \<comment> \<open>Keyword expressions\<close>
    and
      KwExpr :: \<open>expr\<close>
        = "\<lambda>"^= PatAtoms^> RhsArrow^>       \<Rightarrow> \<open>\<lambda>ps e. lam ps e\<close>
        | "if"^= Chain^> "then"^> Body^> "else"^>= Body^>
            \<Rightarrow> \<open>\<lambda>c t e. EIf (expr_of_chain c) t (Some e)\<close>
        | "match"^= Chain^> "with"^> Arms^> \<Rightarrow> \<open>\<lambda>c as. EMatch (expr_of_chain c) as\<close>
        | "handler"^= HCls^>                \<Rightarrow> \<open>\<lambda>cs. EHandlerN cs\<close>
        | "mask"^= LId^> Expr^>             \<Rightarrow> \<open>\<lambda>l e. EMask (tnm l) e\<close>
    and
      PatAtoms :: \<open>mpatom list\<close>
        = PatAtom^>=                        \<Rightarrow> \<open>\<lambda>p. [p]\<close>
        | PatAtoms^>= PatAtom^>=            \<Rightarrow> \<open>\<lambda>ps p. ps @ [p]\<close>
    and
      Arms :: \<open>(mpat \<times> expr) list\<close>
        = ArmsL^=                           \<Rightarrow> \<open>\<lambda>as. as\<close>
        | "{"^= ArmItems^* "}"^>            \<Rightarrow> \<open>\<lambda>as. as\<close>
        | "{"^= ArmItems^* ";"^* "}"^>      \<Rightarrow> \<open>\<lambda>as. as\<close>
    and
      ArmsL :: \<open>(mpat \<times> expr) list\<close>
        = Arm^=                             \<Rightarrow> \<open>\<lambda>a. [a]\<close>
        | ArmsL^= Arm^=                     \<Rightarrow> \<open>\<lambda>as a. as @ [a]\<close>
    and
      ArmItems :: \<open>(mpat \<times> expr) list\<close>
        = Arm^*                             \<Rightarrow> \<open>\<lambda>a. [a]\<close>
        | ArmItems^* ";"^* Arm^*            \<Rightarrow> \<open>\<lambda>as a. as @ [a]\<close>
    and
      Arm :: \<open>mpat \<times> expr\<close>
        = Pat^= RhsArrow^>                  \<Rightarrow> \<open>\<lambda>p e. (p, e)\<close>
    and
      HCls :: \<open>hclause list\<close>
        = HClsL^=                           \<Rightarrow> \<open>\<lambda>cs. cs\<close>
        | "{"^= HClItems^* "}"^>            \<Rightarrow> \<open>\<lambda>cs. cs\<close>
        | "{"^= HClItems^* ";"^* "}"^>      \<Rightarrow> \<open>\<lambda>cs. cs\<close>
    and
      HClsL :: \<open>hclause list\<close>
        = HCl^=                             \<Rightarrow> \<open>\<lambda>c. [c]\<close>
        | HClsL^= HCl^=                     \<Rightarrow> \<open>\<lambda>cs c. cs @ [c]\<close>
    and
      HClItems :: \<open>hclause list\<close>
        = HCl^*                             \<Rightarrow> \<open>\<lambda>c. [c]\<close>
        | HClItems^* ";"^* HCl^*            \<Rightarrow> \<open>\<lambda>cs c. cs @ [c]\<close>
    and
      HCl :: \<open>hclause\<close>
        = LId^= PatAtom^> RhsArrow^>        \<Rightarrow> \<open>\<lambda>x p e. HOp (tnm x) [PatApp [p]] None e\<close>
        | LId^= PatAtom^> "as"^> LId^> RhsArrow^>
            \<Rightarrow> \<open>\<lambda>x p k e. HOp (tnm x) [PatApp [p]] (Some (tnm k)) e\<close>
        | "return"^= PatAtom^> RhsArrow^>   \<Rightarrow> \<open>\<lambda>p e. HRet (PatApp [p]) e\<close>
        | "finally"^= RhsArrow^>            \<Rightarrow> \<open>\<lambda>e. HFin e\<close>
    \<comment> \<open>Patterns\<close>
    and
      Pat :: \<open>mpat\<close>
        = PatChain^=                        \<Rightarrow> \<open>\<lambda>p. p\<close>
        | PatChain^= "as"^> LId^>           \<Rightarrow> \<open>\<lambda>p x. PatAs p (tnm x)\<close>
    and
      PatChain :: \<open>mpat\<close>
        = PatApp^=                          \<Rightarrow> \<open>\<lambda>ps. PatApp ps\<close>
        | PatApp^= Op^> PatChain^>          \<Rightarrow> \<open>\<lambda>ps q p. PatOp ps (op_nm q) p\<close>
    and
      PatApp :: \<open>mpatom list\<close>
        = PatAtom^=                         \<Rightarrow> \<open>\<lambda>p. [p]\<close>
        | PatApp^= PatAtom^>                \<Rightarrow> \<open>\<lambda>ps p. ps @ [p]\<close>
    and
      PatAtom :: \<open>mpatom\<close>
        = Qid^=                             \<Rightarrow> \<open>\<lambda>p. PQid p\<close>
        | KWild^=                             \<Rightarrow> \<open>\<lambda>x. PWild (tnm x)\<close>
        | IntL^=                            \<Rightarrow> \<open>\<lambda>n. int_pat n\<close>
        | StrL^=                            \<Rightarrow> \<open>\<lambda>s. PStr (tloc s) (str_text s)\<close>
        | CharL^=                           \<Rightarrow> \<open>\<lambda>c. PChar (tloc c) (char_value (ttxt c))\<close>
        | "("^= ")"^>                       \<Rightarrow> \<open>PParen []\<close>
        | "("^= PatAnns^* ")"^>             \<Rightarrow> \<open>\<lambda>ps. PParen ps\<close>
        | "("^= PFields^* ")"^>             \<Rightarrow> \<open>\<lambda>fs. PRec fs False\<close>
        | "("^= PFields^* "|"^* KWild^* ")"^> \<Rightarrow> \<open>\<lambda>fs _. PRec fs True\<close>
        | "["^= "]"^>                       \<Rightarrow> \<open>PList []\<close>
        | "["^= PatAnns^* "]"^>             \<Rightarrow> \<open>\<lambda>ps. PList ps\<close>
    and
      PatAnns :: \<open>mpat list\<close>
        = PatAnn^*                          \<Rightarrow> \<open>\<lambda>p. [p]\<close>
        | PatAnns^* ","^* PatAnn^*          \<Rightarrow> \<open>\<lambda>ps p. ps @ [p]\<close>
    and
      PatAnn :: \<open>mpat\<close>
        = Pat^*                             \<Rightarrow> \<open>\<lambda>p. p\<close>
        | Pat^* ":"^* Ty^*                  \<Rightarrow> \<open>\<lambda>p t. PatAnn p t\<close>
    and
      PFields :: \<open>(nm \<times> mpat) list\<close>
        = LId^* "="^* PatAnn^*              \<Rightarrow> \<open>\<lambda>x p. [(tnm x, p)]\<close>
        | PFields^* ","^* LId^* "="^* PatAnn^*
            \<Rightarrow> \<open>\<lambda>fs x p. fs @ [(tnm x, p)]\<close>
    and
      Qid :: \<open>mpath\<close>
        = LId^=                             \<Rightarrow> \<open>\<lambda>x. p1 (tnm x)\<close>
        | UPath^=                           \<Rightarrow> \<open>\<lambda>p. p\<close>
        | UPath^= TSelL^>                   \<Rightarrow> \<open>\<lambda>p x. path_snoc p (sel_nm x)\<close>

parser caraml_parse for caraml

section \<open>Source to surface AST\<close>

text \<open>The executable frontend: UTF-8 decoding, the lexer, the generated
  parser. A file is a declaration list.\<close>

definition read_src :: \<open>string \<Rightarrow> mdecl list option\<close> where
  \<open>read_src src = utf8_decode' src \<bind> caraml_lex \<bind> caraml_parse \<circ> snd\<close>

text \<open>The relational specification it is measured against, composed from the
  three stages' own specifications; the parse relation is taken at the start
  indentation \<open>0\<close>.\<close>

definition reads :: \<open>string \<Rightarrow> mdecl list \<Rightarrow> bool\<close> where
  \<open>reads src ast \<longleftrightarrow>
     (\<exists>cps h ts. utf8 src cps \<and> lexed 0 0 0 cps (h, ts) \<and> caraml_File 0 ts ast)\<close>

text \<open>The executable frontend reads exactly what the specification says:
  soundness and completeness of the three stages compose into the
  interpretation of \<^locale>\<open>frontend\<close>.\<close>

interpretation caraml_frontend: frontend read_src reads
proof
  fix f a
  show \<open>read_src f = Some a \<Longrightarrow> reads f a\<close>
    by (fastforce simp: read_src_def reads_def bind_eq_Some_conv utf8_decode'_Some_iff
        dest: caraml_lex_sound caraml_parse.sound)
  show \<open>reads f a \<Longrightarrow> read_src f = Some a\<close>
    by (fastforce simp: read_src_def reads_def bind_eq_Some_conv utf8_decode'_Some_iff
        intro: caraml_lex_complete caraml_parse.complete)
qed

end
