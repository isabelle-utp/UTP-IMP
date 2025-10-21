section \<open> Simple Imperative Language with Code Generation Support built on UTP Relations \<close>

theory UTP_IMP
  imports "Explorer.Explorer" "UTP2.utp" "Interaction_Trees.ITrees" 
  keywords "execute" :: "diag" and "program" :: "thy_decl"
begin

unbundle UTP_Syntax

subsection \<open> Type and Constructors \<close>

text \<open> We first define a new (sub)type for programs. Generally for UTP, this type will correspond to a
  characteristic non-empty subset of the relations over a particular alphabet that satisfy a number of 
  healthiness conditions. Here, our programs are modelled simply as homogeneous relations over a state
  type @{typ "'s"}, that is  @{typ "'s hrel"}, which is the underlying type of our definition. \<close>

typedef 's prog = "UNIV :: 's hrel set" ..

text \<open> The next command sets up the lifting package, which will allow us to define constructors for
  programs in terms of underlying functions on relations. \<close>

setup_lifting type_definition_prog

text \<open> We can now proceed to define the core constructors for programs, including, assignment,
  sequential composition, conditional, etc. We do this by using the command @{command lift_definition},
  which lifts a function on the underlying type into the defined subtype. This requires us to prove
  that the expression following @{text "is"} inhabits the characteristic subset when all of its
  arguments also do, that is, the characteristic subset set is closed under the given operator.
  For UTP, the underlying type is the relation type over some alphabet family, and the characteristic
  set is the set of healthy relations. 

  In each definition, we give a type for each construct, and then give its definition as an existing 
  constructor on UTP relations. We define assignment as the basic UTP relational assignment operator,
  @{const assigns_r}. The "skip" operator is then an empty assignment. The other program operators
  are defined similarly. The proofs in this case are trivial, since there are no healthiness conditions.
\<close>

lift_definition assigns_prog :: "'s subst \<Rightarrow> 's prog" is assigns_r .

definition skip_prog :: "'s prog" where
[code_unfold]: "skip_prog = assigns_prog id"

lift_definition seq_prog :: "'s prog \<Rightarrow> 's prog \<Rightarrow> 's prog" is seq .

lift_definition cond_prog :: "'s prog \<Rightarrow> (bool, 's) expr \<Rightarrow> 's prog \<Rightarrow> 's prog" is rcond .

lift_definition while_prog :: "(bool, 's) expr \<Rightarrow> 's prog \<Rightarrow> 's prog" is while_top .

text \<open> Here, we use the plus operator to model nondeterministic choice. \<close>

instantiation prog :: (type) plus
begin
lift_definition plus_prog :: "'s prog \<Rightarrow> 's prog \<Rightarrow> 's prog" is sup .

instance ..
end

subsection \<open> Overloaded Syntax \<close>

text \<open> In order to help the process of setting up syntax for a language, we have defined a number
  of polymorphic constants and associated syntax translation rules in 
  @{theory Abstract_Prog_Syntax.Abstract_Prog_Syntax}. If we overload one of the constants,
  such as @{const uassigns}, with a concrete constant, such as @{const assigns_prog}, the parser
  will be extended with support for abstract program notation for these programs. \<close>

adhoc_overloading uassigns \<rightleftharpoons> assigns_prog
adhoc_overloading uskip \<rightleftharpoons> skip_prog
adhoc_overloading useq \<rightleftharpoons> seq_prog
adhoc_overloading ucond \<rightleftharpoons> cond_prog
adhoc_overloading uwhile \<rightleftharpoons> while_prog

text \<open> We also turn off the notation for UTP relations, so there is no ambiguity with the notation
  on the @{typ "'s prog"} type. \<close>

no_adhoc_overloading uassigns \<rightleftharpoons> assigns_r
no_adhoc_overloading uskip \<rightleftharpoons> skip
no_adhoc_overloading useq \<rightleftharpoons> seq
no_adhoc_overloading ucond \<rightleftharpoons> rcond
no_adhoc_overloading uwhile \<rightleftharpoons> while_top

text \<open> With these overloaded constants, we can now use intuitive program notation such as
  @{term "x := e ;; if $x > 1 then y := 0 else II fi"}. \<close>

subsection \<open> Hoare Logic \<close>

text \<open> Next, we similarly lift the relational definition of Hoare triples (resp. partial and total 
  correctness) to our program type, and import the notation. \<close>

lift_definition hoare_prog :: "('s \<Rightarrow> bool) \<Rightarrow> 's prog \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  is "hoare_rel_r" .

lift_definition thoare_prog :: "('s \<Rightarrow> bool) \<Rightarrow> 's prog \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  is "thoare_rel_r" .

ML_file \<open>Spec_Utils.ML\<close>

adhoc_overloading hoare_rel \<rightleftharpoons> hoare_prog
adhoc_overloading thoare_rel \<rightleftharpoons> thoare_prog

text \<open> We can now also lift the Hoare logic laws using the theorems justified on the underlying
  UTP theory. For example, we can use the consequence law for relational Hoare logic, @{thm hoare_r_conseq}.
  We use the method @{method transfer} to recast the theorems on the underlying type, analogous to
  the @{command lift_definition} command. \<close>

lemma hl_conseq: "\<lbrakk> H{P\<^sub>2} C :: 's prog {Q\<^sub>2}; `P\<^sub>1 \<longrightarrow> P\<^sub>2`; `Q\<^sub>2 \<longrightarrow> Q\<^sub>1` \<rbrakk> \<Longrightarrow> H{P\<^sub>1} C {Q\<^sub>1}"
  by (transfer, fact hoare_r_conseq)

lemma thl_conseq: "\<lbrakk> H[P\<^sub>2] C :: 's prog [Q\<^sub>2]; `P\<^sub>1 \<longrightarrow> P\<^sub>2`; `Q\<^sub>2 \<longrightarrow> Q\<^sub>1` \<rbrakk> \<Longrightarrow> H[P\<^sub>1] C [Q\<^sub>1]"
  by (transfer, fact thoare_r_conseq)

lemma hl_assigns:
  assumes "`P \<longrightarrow> \<sigma> \<dagger> Q`"
  shows "H{P} \<langle>\<sigma>\<rangle>\<^sub>a :: 's prog {Q}"
  using assms by (transfer, simp add: assigns_hoare_r)

lemma thl_assigns:
  assumes "`P \<longrightarrow> \<sigma> \<dagger> Q`"
  shows "H[P] \<langle>\<sigma>\<rangle>\<^sub>a :: 's prog [Q]"
  using assms by (transfer, simp add: assigns_thoare_r)

lemma hl_assign [hoare_safe]:
  assumes "`P \<longrightarrow> Q\<lbrakk>e/x\<rbrakk>`"
  shows "H{P} x := e :: 's prog {Q}"
  using assms by (fact hl_assigns)

lemma thl_assign [hoare_safe]:
  assumes "`P \<longrightarrow> Q\<lbrakk>e/x\<rbrakk>`"
  shows "H[P] x := e :: 's prog [Q]"
  using assms by (fact thl_assigns)

lemma hl_forward_assign [hoare_safe]:
  fixes C :: "'s prog"
  assumes "vwb_lens x" "\<And> x\<^sub>0. H{$x = v\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk> \<and> P\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk>} C {Q}"
  shows "H{P} x := v ;; C {Q}"
  using assms
  apply transfer
  using assigns_init_hoare_general apply blast
  done

lemma hl_seq: 
  fixes C\<^sub>1 C\<^sub>2 :: "'s prog"
  assumes "H{P} C\<^sub>1 {Q}" "H{Q} C\<^sub>2 {R}"
  shows "H{P} C\<^sub>1 ;; C\<^sub>2 {R}"
  using assms by (transfer, simp add: seq_hoare_r)

lemma thl_seq: 
  fixes C\<^sub>1 C\<^sub>2 :: "'s prog"
  assumes "H[P] C\<^sub>1 [Q]" "H[Q] C\<^sub>2 [R]"
  shows "H[P] C\<^sub>1 ;; C\<^sub>2 [R]"
  using assms by (transfer, simp add: seq_thoare_r)

lemma hl_cond [hoare_safe]:
  fixes C\<^sub>1 C\<^sub>2 :: "'s prog"
  assumes "H{B \<and> P} C\<^sub>1 {Q}" "H{\<not>B \<and> P} C\<^sub>2 {Q}"
  shows "H{P} if B then C\<^sub>1 else C\<^sub>2 fi {Q}"
  using assms
  by (transfer, simp add: cond_hoare_r)

lemma thl_cond:
  fixes C\<^sub>1 C\<^sub>2 :: "'s prog"
  assumes "H[B \<and> P] C\<^sub>1 [Q]" "H[\<not>B \<and> P] C\<^sub>2 [Q]"
  shows "H[P] if B then C\<^sub>1 else C\<^sub>2 fi [Q]"
  using assms
  by (transfer, simp add: cond_thoare_r)

lemma hl_choice:
  fixes C\<^sub>1 C\<^sub>2 :: "'s prog"
  assumes "H{P} C\<^sub>1 {Q}" "H{P} C\<^sub>2 {Q}"
  shows "H{P} C\<^sub>1 + C\<^sub>2 {Q}"
  using assms
  by (transfer, simp add: hoare_ndet)

lemma thl_choice:
  fixes C\<^sub>1 C\<^sub>2 :: "'s prog"
  assumes "H[P] C\<^sub>1 [Q]" "H[P] C\<^sub>2 [Q]"
  shows "H[P] C\<^sub>1 + C\<^sub>2 [Q]"
  using assms
  by (transfer, simp add: thoare_ndet)

lemma hl_while_core:
  fixes C :: "'s prog"
  assumes "H{P \<and> B} C {P}"
  shows "H{P} while B do C od {\<not>B \<and> P}"
  using assms by (transfer, simp add: while_hoare_r)

lemma hl_while:
  fixes C :: "'s prog"
  assumes "`P \<longrightarrow> I`" "H{I \<and> B} C {I}" "`\<not>B \<and> I \<longrightarrow> Q`"
  shows "H{P} while B do C od {Q}"
  using assms(1,2,3) hl_conseq hl_while_core by blast

lemma thl_while_core [hoare_safe]:
  fixes V :: "'s \<Rightarrow> 'a::wellorder" and S :: "'s prog"
  assumes "\<And> z. H[P \<and> B \<and> V = \<guillemotleft>z\<guillemotright>] S [P \<and> V < \<guillemotleft>z\<guillemotright>]"
  shows "H[P] while B do S od [\<not> B \<and> P]"
  using assms by (transfer, metis (mono_tags) while_thoare_r)

lemma thl_while [hoare_safe]:
  fixes V :: "'s \<Rightarrow> 'a::wellorder" and S :: "'s prog"
  assumes "`P \<longrightarrow> I`" "\<And> z. H[I \<and> B \<and> V = \<guillemotleft>z\<guillemotright>] S [I \<and> V < \<guillemotleft>z\<guillemotright>]" "`\<not> B \<and> I \<longrightarrow> Q`"
  shows "H[P] while B do S od [Q]"
  using assms(1,2,3) thl_conseq thl_while_core by blast

definition while_invariant :: "(bool, 's) expr \<Rightarrow> (bool, 's) expr \<Rightarrow> 's prog \<Rightarrow> 's prog" where
"while_invariant B I C = while_prog B C"

syntax
  "_while_inv_itree" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(while _ /(2invariant/ _) //(2do //_) //od)")

translations
  "_while_inv_itree B I P" == "CONST while_invariant (B)\<^sub>e (I)\<^sub>e P"

lemma hl_while_invariant [hoare_safe]:
  assumes "H{I \<and> B} S {I}" "`P \<longrightarrow> I`" "`(\<not> B \<and> I) \<longrightarrow> Q`"
  shows "H{P} while B invariant I do S od {Q}"
  by (metis assms(1,2,3) hl_while[of P I B S Q] while_invariant_def[of "(B)\<^sub>e" "(I)\<^sub>e" S])

subsection \<open> Proof Methods \<close>

method assign = (rule hl_assign thl_assign)

method if_then_else = (rule hl_cond thl_cond)

method choice = (rule hl_choice thl_choice)

method_setup sequence =
\<open>
Scan.peek (Args.named_term o Syntax.parse_term o Context.proof_of) >>
   (fn rt => fn ctx => 
     SIMPLE_METHOD (SUBGOAL (fn (goal, i) => Spec_Utils.inst_hoare_rule_tac @{thm hl_seq} "Q" ctx rt goal) 1))
\<close> "apply the sequential law with an intermediate condition"

method_setup while =
\<open>
Scan.peek (Args.named_term o Syntax.parse_term o Context.proof_of) >>
   (fn rt => fn ctx => 
     SIMPLE_METHOD (SUBGOAL (fn (goal, i) => Spec_Utils.inst_hoare_rule_tac @{thm hl_while} "I" ctx rt goal) 1))
\<close> "while loop with invariant"

named_theorems hoare_lemmas

named_theorems prog_defs

method hoare = ((simp add: prog_defs usubst usubst_eval)?, (auto intro!: hoare_safe hoare_lemmas; (simp add: usubst_eval)?))[1]

method vcg_lens = (hoare; expr_lens_taut?; safe?; simp?) \<comment> \<open> Most useful when multiple states are present \<close>

method vcg = (hoare; expr_taut?; safe?; simp?)

subsection \<open> ITree Code Generation \<close>

text \<open> The program of an ITree captures all possible initial/final state pairs. Any divergent or
  abortive behaviour is simply excluded from the relation. The function @{term "\<^bold>R"} determines
  the set of all final states (i.e. returning states) of an interaction tree. Programs in
  ITrees are modelled as the type @{typ "'s \<Rightarrow> (nat, 's) itree"}, which has the synonym
  @{typ "(nat, 's) htree"}. The natural number event type allows us to use events to model 
  nondeterministic choices. \<close>

lift_definition itree_prog :: "(nat, 's) htree \<Rightarrow> 's prog" ("\<lbrakk>_\<rbrakk>\<^sub>I") is "\<lambda> P (s, s'). s' \<in> \<^bold>R (P s)" .

lemma hoare_itree_meaning:
  "H{P} itree_prog C {Q} = (\<forall> s s'. P s \<and> s' \<in> \<^bold>R(C s) \<longrightarrow> Q s')"
  by (transfer, auto simp add: hoare_meaning)

lemma thoare_itree_meaning:
  "H[P] itree_prog C [Q] = (\<forall> s. P s \<longrightarrow> (\<forall> s' \<in> \<^bold>R(C s). Q s') \<and> (\<exists> s'. s' \<in> \<^bold>R(C s)))"
  by (transfer, auto simp add: thoare_rel_r_def)

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

subsection \<open> Commands \<close>

text \<open> We create a command to allow definition of programs. \<close>

ML \<open>
structure UTP_Program =
struct

fun mk_program (((n, p), st), body) ctx =
  let open Syntax
      val stT = read_typ ctx st
      val ty = (check_typ ctx (Type (@{type_name prog}, [stT])))
      val pat = read_term ctx p
      val vs = map (fst o dest_Free) (HOLogic.strip_tuple pat)
      val pat' = HOLogic.mk_tuple (map free vs)
      val pty = HOLogic.mk_tupleT (map (snd o dest_Free) (HOLogic.strip_tuple pat))
      val pbody = Type.constraint ty (parse_term ctx body)
      val def = HOLogic.tupled_lambda pat' pbody
      val attrs = @{attributes [code_unfold, prog_defs]};
      fun mk_def ty x v = check_term ctx (Const ("Pure.eq", ty --> ty --> Term.propT) $ Free (x, ty) $ v);
      val def_ty = pty --> ty        
  in snd (Specification.definition (SOME (Binding.name n, SOME def_ty, NoSyn)) [] [] ((Binding.name (n ^ "_def"), attrs), mk_def def_ty n def) ctx) 
  end;

val parse_program =
  let open Scan; open Parse in
  ((name -- (Scan.optional term "()")) -- 
   (Scan.optional (@{keyword "over"} |-- typ) "_") --
   (@{keyword "="} |-- term))
   end;  

end;

Outer_Syntax.command @{command_keyword program} "define an ITree program"
  (UTP_Program.parse_program >> (Toplevel.local_theory NONE NONE o UTP_Program.mk_program));
\<close>

text \<open> We create a command to allow execution of programs. \<close>

ML \<open> 
let fun execute_cmd t ctx =
  let val tm = Syntax.check_term ctx (Syntax.const @{const_name exec_prog} $ Syntax.parse_term ctx t)
      val _ = Pretty.writeln (Syntax.pretty_term ctx (Value_Command.value ctx tm))
  in ctx end;
in
Outer_Syntax.command @{command_keyword execute} "execute a UTP program"
  (Parse.term >> (Toplevel.local_theory NONE NONE o execute_cmd))
end
\<close>

subsection \<open> Usability Setup \<close>

declare [[literal_variables]]

notation useq (infixr ";" 54)

setup Explorer_Lib.switch_to_quotes

(* Should lens gets appear in VCs, it's better they are concise and pretty *)

notation lens_get ("_<_>" [999,0] 999)

(* Prevent the dollar variable annotations appearing in printed expressions *)

translations
  "x" <= "_sexp_var x"

end