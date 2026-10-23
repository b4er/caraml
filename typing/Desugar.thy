theory Desugar
  imports CaraML_Syntax.Module_Expressions
begin

section \<open>Desugaring function declarations\<close>

text \<open>\<^const>\<open>DFun\<close> is frontend sugar. A function binding \<open>f p\<^sub>1 \<dots> p\<^sub>n = e | \<dots>\<close>
  is lowered to a value binding whose right-hand side is a \<^emph>\<open>curried\<close>
  nest of single-pattern \<^const>\<open>EFn\<close>s, under one \<^const>\<open>EFnMod\<close> per
  module binder, which static interpretation then binds recursively.
  Several clauses share one \<^const>\<open>EMatch\<close> on the tuple of the arguments,
  bound to reserved \<open>%a\<dots>\<close> names (\<open>fvalbind\<close> \<^cite>\<open>\<open>App. A\<close> in milner1997\<close>).
  The type checker types the clauses and \<^emph>\<open>emits\<close> the lowered form, so
  the explicit surface never contains \<^const>\<open>DFun\<close> (static interpretation
  rejects it).\<close>

text \<open>The name, the signature and the implicitness of a module binder.\<close>

fun mbind_nm :: \<open>mbind \<Rightarrow> name\<close> and
  mbind_sig :: \<open>mbind \<Rightarrow> msig\<close> and
  is_imp :: \<open>mbind \<Rightarrow> bool\<close>
where
  \<open>mbind_nm (BMod x _) = n_txt x\<close>
| \<open>mbind_nm (BImp x _) = n_txt x\<close>
| \<open>mbind_sig (BMod _ sg) = sg\<close>
| \<open>mbind_sig (BImp _ sg) = sg\<close>
| \<open>is_imp (BMod _ _) = False\<close>
| \<open>is_imp (BImp _ _) = True\<close>

text \<open>The reserved name of the \<open>i\<close>-th argument.\<close>

definition argnm :: \<open>nat \<Rightarrow> nm\<close> where
  \<open>argnm i = \<lparr>l_line = 0, l_col = 0, l_off = 0, l_len = 0,
              n_txt = str (''%a'' @ replicate i (CHR ''x''))\<rparr>\<close>

text \<open>The lowered right-hand side of a function's clauses.\<close>

fun dfun_rhs :: \<open>(mpat list \<times> expr) list \<Rightarrow> expr\<close> where
  \<open>dfun_rhs [] = EErr\<close>
| \<open>dfun_rhs [(ps, e)] = foldr (\<lambda>p acc. EFn [p] acc) ps e\<close>
| \<open>dfun_rhs cls =
     (let args = map argnm [0..<length (fst (hd cls))];
          scrut = (case args of [a] \<Rightarrow> ESpine [APath (MkPath [a])]
                   | _ \<Rightarrow> ESpine [AParen (map (\<lambda>a. ESpine [APath (MkPath [a])]) args)]);
          arms = map (\<lambda>(ps, e). ((case ps of [p] \<Rightarrow> p | _ \<Rightarrow> PatApp [PParen ps]), e)) cls
      in foldr (\<lambda>a acc. EFn [PatApp [PQid (MkPath [a])]] acc) args (EMatch scrut arms))\<close>

text \<open>The lowering, through structures, functor applications and sealings.\<close>

fun dsg_decl :: \<open>mdecl \<Rightarrow> mdecl\<close> and
  dsg_mexpr :: \<open>mexpr \<Rightarrow> mexpr\<close>
where
  \<open>dsg_decl (DFun f mbs cls) = DLet f (foldr EFnMod mbs (dfun_rhs cls))\<close>
| \<open>dsg_decl (DMod x ps s m) = DMod x ps s (dsg_mexpr m)\<close>
| \<open>dsg_decl (DImpl x ps s m) = DImpl x ps s (dsg_mexpr m)\<close>
| \<open>dsg_decl d = d\<close>
| \<open>dsg_mexpr (MStruct ds) = MStruct (map dsg_decl ds)\<close>
| \<open>dsg_mexpr (MApp a b) = MApp (dsg_mexpr a) (dsg_mexpr b)\<close>
| \<open>dsg_mexpr (MSeal m s) = MSeal (dsg_mexpr m) s\<close>
| \<open>dsg_mexpr m = m\<close>

end
