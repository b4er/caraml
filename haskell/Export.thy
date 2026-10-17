theory Export
  imports
    CaraML_Typing.Infer
    "HOL-Library.Code_Target_Numeral"
begin

text \<open>Haskell code for the \<open>caraml\<close> executable. \<^theory>\<open>HOL-Library.Code_Target_Numeral\<close>
  implements \<^typ>\<open>nat\<close> by target integers, so \<^term>\<open>0::nat\<close> and \<^const>\<open>Suc\<close> are no
  longer patterns. The preprocessor of \<^theory>\<open>HOL-Library.Code_Abstract_Nat\<close> removes them
  only where each \<^const>\<open>Suc\<close> equation has a \<^term>\<open>0::nat\<close> equation of its own; a fueled
  function that matches the fuel and another argument in several equations is
  split here instead, without touching its definition: a \<open>_suc\<close> constant takes the
  \<^const>\<open>Suc\<close> equations, folded, and one pattern-free equation tests the fuel.\<close>

subsection \<open>Fueled functions\<close>

text \<open>\<^const>\<open>kunify\<close> with positive fuel.\<close>

definition kunify_suc where \<open>kunify_suc f = kunify (Suc f)\<close>

lemma kunify_code[code]:
  \<open>kunify f cs n = (if f = 0 then None else kunify_suc (f - 1) cs n)\<close>
  by (cases f) (simp_all add: kunify_suc_def)

lemmas kunify_suc_code[code] = kunify.simps[folded kunify_suc_def]

lemma kunify_0[code del]: \<open>kunify 0 cs n = None\<close>
  by simp

text \<open>\<^const>\<open>con_result\<close> with positive arity.\<close>

definition con_result_suc where \<open>con_result_suc k = con_result (Suc k)\<close>

lemma con_result_code[code]:
  \<open>con_result k \<tau> = (if k = 0 then Some \<tau> else con_result_suc (k - 1) \<tau>)\<close>
  by (cases k) (simp_all add: con_result_suc_def)

lemmas con_result_suc_code[code] = con_result.simps[folded con_result_suc_def]

lemma con_result_0[code del]: \<open>con_result 0 \<tau> = Some \<tau>\<close>
  by simp

text \<open>\<^const>\<open>con_ty\<close> with positive arity.\<close>

definition con_ty_suc where \<open>con_ty_suc k = con_ty (Suc k)\<close>

lemma con_ty_code[code]:
  \<open>con_ty k \<tau> = (if k = 0 then Some ([], \<tau>) else con_ty_suc (k - 1) \<tau>)\<close>
  by (cases k) (simp_all add: con_ty_suc_def)

lemmas con_ty_suc_code[code] = con_ty.simps[folded con_ty_suc_def]

lemma con_ty_0[code del]: \<open>con_ty 0 \<tau> = Some ([], \<tau>)\<close>
  by simp

subsection \<open>Export\<close>

export_code \<open>infer\<close> in Haskell
  module_name CaraML.Verified
  file_prefix caraml

end
