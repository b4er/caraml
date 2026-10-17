theory Foreign
  imports Core "HOL-Library.Sublist"
begin

section \<open>The precise foreign boundary\<close>

text \<open>What the host, and an observer of the trace, see of a Core run.
  \<^const>\<open>crun\<close> exchanges raw values with the host. The language semantics
  (theory \<^text>\<open>Behaviour\<close>) runs it at the host \<open>opaque\<close> and observes the
  result through \<open>obs\<close>:
  \<^item> \<^emph>\<open>Code is opaque at the boundary.\<close> The host and the observed trace see a
    performed argument \<^emph>\<open>erased\<close>: each closure or continuation in it becomes
    a handle \<open>%code i\<close>, numbered in the order the pieces of code cross the
    boundary (through the earlier events, then left to right).
  \<^item> \<^emph>\<open>Code is refused in answers.\<close> An answer carrying code counts as no
    answer (stuck). \<^text>\<open>ffi_ok\<close> hosts answer first-order values, so
    nothing typed changes.

  So a compiler pass may change code unobserved.\<close>

subsection \<open>Erasure\<close>

fun codes :: \<open>cval \<Rightarrow> nat\<close> and codes_list :: \<open>cval list \<Rightarrow> nat\<close> where
  \<open>codes (Vclos env x e) = 1\<close>
| \<open>codes (Vclosrec env f x e) = 1\<close>
| \<open>codes (VCont fs) = 1\<close>
| \<open>codes (Vcon c vs) = codes_list vs\<close>
| \<open>codes (Vlit l) = 0\<close>
| \<open>codes (Vname i) = 0\<close>
| \<open>codes_list [] = 0\<close>
| \<open>codes_list (v # vs) = codes v + codes_list vs\<close>

definition handle :: \<open>nat \<Rightarrow> cval\<close> where
  \<open>handle i = Vcon (str ''%code'') [Vlit (LNat i)]\<close>

text \<open>\<open>herase n v\<close>: \<open>v\<close> with its pieces of code numbered from \<open>n\<close>.\<close>

fun herase :: \<open>nat \<Rightarrow> cval \<Rightarrow> cval\<close>
  and herase_list :: \<open>nat \<Rightarrow> cval list \<Rightarrow> cval list\<close> where
  \<open>herase n (Vclos env x e) = handle n\<close>
| \<open>herase n (Vclosrec env f x e) = handle n\<close>
| \<open>herase n (VCont fs) = handle n\<close>
| \<open>herase n (Vcon c vs) = Vcon c (herase_list n vs)\<close>
| \<open>herase n (Vlit l) = Vlit l\<close>
| \<open>herase n (Vname i) = Vname i\<close>
| \<open>herase_list n [] = []\<close>
| \<open>herase_list n (v # vs) = herase n v # herase_list (n + codes v) vs\<close>

fun ev_codes :: \<open>ffi_ev \<Rightarrow> nat\<close> where
  \<open>ev_codes (FFIev sy w a) = codes w\<close>

fun erase_ev :: \<open>nat \<Rightarrow> ffi_ev \<Rightarrow> ffi_ev\<close> where
  \<open>erase_ev n (FFIev sy w a) = FFIev sy (herase n w) a\<close>

text \<open>A history is erased event by event (each argument numbered from the
  count of the pieces of code before it), answers stay as the host gave them.\<close>

fun erase_evs :: \<open>nat \<Rightarrow> ffi_ev list \<Rightarrow> ffi_ev list\<close> where
  \<open>erase_evs n [] = []\<close>
| \<open>erase_evs n (ev # evs) = erase_ev n ev # erase_evs (n + ev_codes ev) evs\<close>

definition hcount :: \<open>ffi_ev list \<Rightarrow> nat\<close> where
  \<open>hcount evs = sum_list (map ev_codes evs)\<close>

abbreviation erase_hist :: \<open>ffi_ev list \<Rightarrow> ffi_ev list\<close> where
  \<open>erase_hist \<equiv> erase_evs 0\<close>

lemma hcount_simps[simp]:
  \<open>hcount [] = 0\<close>
  \<open>hcount (ev # evs) = ev_codes ev + hcount evs\<close>
  \<open>hcount (evs @ evs') = hcount evs + hcount evs'\<close>
  by (simp_all add: hcount_def)

lemma erase_evs_append:
  \<open>erase_evs n (evs @ evs') = erase_evs n evs @ erase_evs (n + hcount evs) evs'\<close>
  by (induction evs arbitrary: n) (simp_all add: add.assoc)

lemma erase_hist_snoc:
  \<open>erase_hist (evs @ [FFIev sy w a]) = erase_hist evs @ [FFIev sy (herase (hcount evs) w) a]\<close>
  by (simp add: erase_evs_append)

lemma erase_hist_prefix: \<open>prefix evs evs' \<Longrightarrow> prefix (erase_hist evs) (erase_hist evs')\<close>
  by (auto simp: prefix_def erase_evs_append)

subsection \<open>The opaque host\<close>

definition opaque :: \<open>ffi \<Rightarrow> ffi\<close> where
  \<open>opaque ffi sy evs w =
     (case ffi sy (erase_hist evs) (herase (hcount evs) w) of
        Some (FRet v) \<Rightarrow> if codes v = 0 then Some (FRet v) else None
      | a \<Rightarrow> a)\<close>

lemma opaque_ret: \<open>opaque ffi sy evs w = Some (FRet v) \<Longrightarrow> codes v = 0\<close>
  by (auto simp: opaque_def split: option.splits ffi_res.splits if_splits)

subsection \<open>Observation\<close>

text \<open>What is observed of a run: the erased trace, and the erased event of a
  host error. The value of a successful run is not observed
  (\<^text>\<open>outcome\<close> of the specification).\<close>

fun obs_res :: \<open>ffi_ev list \<Rightarrow> 'a cres \<Rightarrow> 'a cres\<close> where
  \<open>obs_res evs (Rhost ev) = Rhost (erase_ev (hcount evs) ev)\<close>
| \<open>obs_res evs r = r\<close>

definition obs :: \<open>'a cres \<times> ffi_ev list \<Rightarrow> 'a cres \<times> ffi_ev list\<close> where
  \<open>obs r = (obs_res (snd r) (fst r), erase_hist (snd r))\<close>

lemma obs_le: \<open>r \<sqsubseteq>\<^sub>t r' \<Longrightarrow> obs r \<sqsubseteq>\<^sub>t obs r'\<close>
  by (auto simp: tres_le_def obs_def erase_evs_append)

lemma obs_res_eq_iff[simp]:
  \<open>obs_res evs r = Rerr \<longleftrightarrow> r = Rerr\<close>
  \<open>obs_res evs r = Rtimeout \<longleftrightarrow> r = Rtimeout\<close>
  by (cases r; simp)+

lemma fst_obs: \<open>fst (obs r) = obs_res (snd r) (fst r)\<close>
  by (simp add: obs_def)

end
