theory Protocol_Test
  imports CaraML_Syntax.Protocol
begin

section \<open>Example: a file effect\<close>

datatype file_op = Open | Read | Close

definition file_prot :: \<open>file_op ltlf\<close> where
  \<open>file_prot \<equiv> Match (Atom Open ~~ Star (Atom Read) ~~ Atom Close)\<close>

value \<open>sat [Open, Read, Read, Close] file_prot\<close>
value \<open>sat [Read, Close] file_prot\<close>
value \<open>sat [Open, Read] file_prot\<close>

abbreviation \<open>op_open \<equiv> str ''open''\<close>
abbreviation \<open>op_read \<equiv> str ''read''\<close>
abbreviation \<open>op_close \<equiv> str ''close''\<close>

definition file_prot' :: \<open>name ltlf\<close> where
  \<open>file_prot' \<equiv> Match (Atom op_open ~~ Star (Atom op_read) ~~ Atom op_close)\<close>

lemma \<open>check_rl (Atom op_open ~~ Atom op_read ~~ Atom op_read ~~ Atom op_close) file_prot'\<close>
  by eval

lemma \<open>\<not> check_rl (Atom op_read ~~ Atom op_close) file_prot'\<close>
  by eval

lemma \<open>check_rl (Atom op_open ~~ Star (Atom op_read)) (Match (Atom op_open ~~ Star (Atom op_read)))\<close>
  by eval

lemma \<open>\<not> check_rl (Atom op_open ~~ Star (Atom op_read)) file_prot'\<close>
  by eval

lemma \<open>incl_ll [op_open, op_read, op_close] file_prot'
  (SImp (Star (Plus (Atom op_open) (Atom op_read)) ~~ Atom op_close) Last)\<close>
  by eval

lemma \<open>incl_ll [op_open, op_read, op_close] file_prot' (Prop [op_open])\<close>
  by eval

end