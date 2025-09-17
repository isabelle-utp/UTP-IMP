section \<open> Simple Imperative Language with Code Generation Support \<close>

theory UTP_IMP
  imports "UTP2.utp" "Interaction_Trees.ITrees"
begin

subsection \<open> Type and Constructors \<close>

typedef 's prog = "UNIV :: 's hrel set" ..

setup_lifting type_definition_prog

lift_definition assigns_prog :: "'s subst \<Rightarrow> 's prog" is "\<lambda> \<sigma> :: 's \<Rightarrow> 's. assigns_r \<sigma>" .

definition skip_prog :: "'s prog" where
[code_unfold]: "skip_prog = assigns_prog id"

lift_definition seq_prog :: "'s prog \<Rightarrow> 's prog \<Rightarrow> 's prog" is seq .

lift_definition cond_prog :: "'s prog \<Rightarrow> (bool, 's) expr \<Rightarrow> 's prog \<Rightarrow> 's prog" is "\<lambda> P ( b::(bool, 's) expr) Q. rcond P b Q" .

lift_definition while_prog :: "(bool, 's) expr \<Rightarrow> 's prog \<Rightarrow> 's prog" is while_top .

text \<open> Here, we use plus to model nondeterministic choice \<close>

instantiation prog :: (type) plus
begin
lift_definition plus_prog :: "'s prog \<Rightarrow> 's prog \<Rightarrow> 's prog" is sup .

instance ..
end

subsection \<open> Overloaded Syntax \<close>

adhoc_overloading uassigns \<rightleftharpoons> assigns_prog
adhoc_overloading uskip \<rightleftharpoons> skip_prog
adhoc_overloading useq \<rightleftharpoons> seq_prog
adhoc_overloading ucond \<rightleftharpoons> cond_prog
adhoc_overloading uwhile \<rightleftharpoons> while_prog

subsection \<open> ITree Code Generation \<close>

lift_definition itree_prog :: "(nat, 's) htree \<Rightarrow> 's prog" ("\<lbrakk>_\<rbrakk>\<^sub>I") is "\<lambda> P (s, s'). s' \<in> \<^bold>R (P s)" .

definition final_states :: "'s prog \<Rightarrow> 's \<Rightarrow> 's set" where
"final_states P s = {s'. Rep_prog P (s, s')}"

lemma some_elem_set_single [code]: "some_elem (set [x]) = x"
  by simp

text \<open> Run a program starting from a default state, and provides a status report on the final state(s) \<close>

datatype 's status = 
  terminate 's |  \<comment> \<open> The program terminated with a single finale state \<close>
  abort |  \<comment> \<open> The program provided no final state, and so terminated \<close>
  multiple \<comment> \<open> There were multiple final states, implying non-determinism \<close>

definition exec_prog :: "'s::default prog \<Rightarrow> 's status" where
"exec_prog P = (let S = final_states P default in
                if S = {} then abort
                else if card S = 1 then terminate (some_elem S)
                else multiple)"

lemma finals_itree_prog [code]: "final_states \<lbrakk>P\<rbrakk>\<^sub>I s = \<^bold>R (P s)"
  by (metis (mono_tags, lifting) Collect_cong case_prodD case_prodI final_states_def itree_prog.rep_eq mem_Collect_eq retvals_def)

declare retvals_Ret [code]
declare retvals_Sil [code]
declare retvals_Vis [code]

code_datatype itree_prog

lemma code_assigns [code]: "assigns_prog \<sigma> = \<lbrakk>\<lambda>s. \<checkmark> (\<sigma> s)\<rbrakk>\<^sub>I"
  by (simp add: itree_prog_def assigns_prog_def assigns_r_def)

lemma code_seq [code]: "seq_prog \<lbrakk>P\<rbrakk>\<^sub>I \<lbrakk>Q\<rbrakk>\<^sub>I = \<lbrakk>P >=> Q\<rbrakk>\<^sub>I"
  by (transfer, auto simp add: kcomp_itree_def seq_def)

lemma code_cond [code]: "cond_prog \<lbrakk>P\<rbrakk>\<^sub>I b \<lbrakk>Q\<rbrakk>\<^sub>I = \<lbrakk>\<lambda> s. if b s then P s else Q s\<rbrakk>\<^sub>I"
  by (transfer, auto simp add: rcond_def, expr_auto)

lemma code_choice [code]: "\<lbrakk>P\<rbrakk>\<^sub>I + \<lbrakk>Q\<rbrakk>\<^sub>I = \<lbrakk>\<lambda> s. Vis {0 \<mapsto> P s, 1 \<mapsto> Q s}\<rbrakk>\<^sub>I"
  by (transfer, auto)

lemma code_while [code]: "while_prog b \<lbrakk>P\<rbrakk>\<^sub>I = \<lbrakk>iterate b P\<rbrakk>\<^sub>I"
  by (transfer, auto simp add: retvals_iterate while_chain_form itree_chain_iff_rtc_chain)

end