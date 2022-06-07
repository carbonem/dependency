From mathcomp Require Import all_ssreflect zify finmap.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Dep Require Import Global_Syntax Inductive_Linearity Substitutions Predicates.
Let inE := Predicates.inE.


Ltac norm_eqs := repeat (match goal with 
                   | [ H : (_ == _) |- _ ] => move : H => /eqP=>H
                   | [ H : (_ == _) = true |- _ ] => move : H => /eqP=>H
                   | [ H : (_ == _) = false |- _ ] => move : H => /negbT=>H

                  end);subst;repeat (match goal with 
                   | [ H : is_true (?a != ?a_) |- _ ] => rewrite eqxx in H;done 

                  end).



Definition preds (A : eqType) (l : seq (pred A)) : pred A := (foldr predI predT l).

Definition lpreds := locked preds.


Class CHint (b : Prop) : Prop:= { _ : (b : Prop) }.


Hint Resolve  Build_CHint : typeclass_instances.


Class CGoal (b : Prop) : Prop := { _ : (b : Prop) }.
Generalizable Variables D E.

Lemma cgoal_imp : forall (P0 P1 : Prop), (P0 -> P1)  -> CGoal P0 -> CGoal P1.
Proof. intros. destruct H0. constructor. auto. Qed.

Lemma chint_imp : forall (P0 P1 : Prop), (P0 -> P1)  -> CHint P0 -> CGoal P1.
Proof. intros. destruct H0. constructor. auto. Qed.

Instance CGoal_Hint `{H : CHint D} : CGoal D. destruct H. constructor. done. Defined.



Check ptcps.


Lemma notin_big : forall (p : ptcp) gs i, p \notin \bigcup_(j <- gs) (ptcps j) -> i < size gs -> p \notin ptcps (nth GEnd gs i).
Proof.
intros. apply/negP=>HH. apply (negP H). apply/bigfcupP. exists (nth GEnd gs i). rewrite mem_nth //=. apply HH. Qed.

Hint Resolve notin_big.

Ltac brute :=  typeclasses eauto with typeclass_instances.

Lemma CGoal_imp2 : forall P, CGoal P -> P. intros. destruct H. done. Defined.


Ltac to_goal := apply CGoal_imp2.

Lemma lock_lpreds  : preds = lpreds.
Proof. unlock lpreds. done. Qed.
Ltac ul := unlock lpreds.
Ltac usl := ul; rewrite /= lock_lpreds.

Ltac apply_typeclasses := to_goal;typeclasses eauto with typeclass_instances.
Ltac pre_process := unlock lpreds;rewrite /=;split_and.
Definition notin_pred p g :=  p \notin (ptcps g).  
Lemma notin_pred_eq p : notin_pred p =  (fun g => p \notin (ptcps g)). done. Qed.


Ltac cc := match goal with 
           | [ |- is_true (lpreds _ _) ] => (try apply_typeclasses);pre_process; try apply_typeclasses
           | _ => try apply_typeclasses
           end;try done.

Ltac cc_fail := 
           match goal with 
           | [ |- is_true (lpreds _ _) ] => pre_process; apply_typeclasses
           | _ => apply_typeclasses
           end;try done.


Notation "{hint P }" := (@CHint  P)(format "{hint  P }").
Notation "{goal P }" := (@CGoal  P)(format "{goal  P }").

Class CFind (A : Type) (a : A) (l : seq A) := {_ : In a l}.

Instance Find_now (A : Type) (a : A) l : CFind a (a::l).
constructor. simpl. auto. 
Qed.

Instance Find_later (A : Type) (a a0 : A) l : CFind a l -> CFind a (a0::l).
case. move => H. constructor. simpl. auto. 
Qed.



Notation npred := notin_pred.
Notation apred := action_pred.
Notation spred := size_pred.
Notation ppred := project_pred.

Definition rec_pred := [::apred;spred;ppred]. 

Class CGPred (A : eqType) (p : pred A) := { _ : pred A }.

Instance apred_CGPred : CGPred apred. constructor. constructor. Qed.
Instance spred_CGPred : CGPred spred. constructor. constructor. Qed.
Instance ppred_CGPred : CGPred ppred. constructor. constructor. Qed.
Instance npred_CGPred p : CGPred (npred p). constructor. constructor. Qed.


Class CStructural (A : eqType) (p : pred A) (g0 g1 : A) := { cimp : p g0 -> p g1}. 
Instance  CStructural_overlap (A : eqType) p (g : A) : CStructural p g g. Proof. constructor. done. Qed.

Instance  CStructural_apredr n g : CStructural apred (GRec n g) g. Proof. constructor. simpl. done. Qed.
Instance  CStructural_spredr n g : CStructural spred (GRec n g) g. Proof. constructor. simpl. done. Qed.
Instance  CStructural_ppredr n g : CStructural ppred (GRec n g) g. Proof. constructor. simpl. done. Qed.
Instance  CStructural_npredr p n g : CStructural (npred p) (GRec n g) g. Proof. constructor. simpl. done. Qed.

Instance  CStructural_apredm a u g : CStructural apred (GMsg a u g) g. Proof. constructor. simpl. lia. Qed.
Instance  CStructural_spredm a u g : CStructural spred (GMsg a u g) g. Proof. constructor. simpl. lia. Qed.
Instance  CStructural_ppredm a u g : CStructural ppred (GMsg a u g) g. Proof. constructor. simpl. lia. Qed.
Instance  CStructural_npredm p a u g : CStructural (npred p) (GMsg a u g) g. Proof. constructor.  rewrite /npred /= !inE. Locate inE.  Check inE.  split_and. Qed.

Instance  CStructural_apredb a gs g : {goal g \in gs} -> CStructural apred (GBranch a gs) g. 
Proof. move=>[] H. constructor. simpl. split_and. apply (allP H2). done.  Qed.
Instance  CStructural_spredb a gs g : {goal g \in gs} ->  CStructural spred (GBranch a gs) g. 
Proof. move=>[] H. constructor. simpl. split_and. apply (allP H2). done.  Qed.
Instance  CStructural_ppredb a gs g :  {goal g \in gs} -> CStructural ppred (GBranch a gs) g. 
Proof. move=>[] H. constructor. simpl. split_and. apply (allP H2). done.  Qed.
Instance  CStructural_npredb p a gs g : {goal g \in gs} ->  CStructural (npred p) (GBranch a gs) g. 
Proof. move=>[] H. constructor. rewrite /npred /= big_map !inE. split_and. 
       move : H. move/nthP=>Hnth. specialize Hnth with GEnd. destruct Hnth. rewrite -H1. apply/notin_big. done. done. 
Qed.


Lemma In_l_preds : forall (A : eqType) l (g : A) p, In p l -> lpreds l g ->  p g.
Proof. move=> A. elim. done. simpl. intros. destruct H0. subst.  move : H1. unlock lpreds. simpl. lia. apply H. done. move : H1. unlock lpreds. simpl. lia. 
Qed.

Instance resolve_to_lpreds  : forall (A : eqType ) (l : seq (pred A)) g0 g1 p, CGPred p -> {hint lpreds l g0} -> CFind p l ->  CStructural p g0 g1 -> {goal p g1}.
Proof. move => A l g0 g1 p [] H [] H0 [] H1 [] H2. constructor. apply H2. apply : In_l_preds;eauto. Qed.


Lemma index_lpreds : forall (A :eqType) l (g : A) n, lpreds l g -> (nth (fun _ => true) l n g).
Proof.  move => A. elim. intros. destruct n.   done. done. simpl. intros. destruct n. simpl. apply : In_l_preds;eauto. simpl. auto. simpl. apply H. move : H0. unlock lpreds. simpl. lia. Qed.
Ltac nth_lpreds n H := move : (@index_lpreds _ _ _ n H); rewrite {1}/nth /npred.

Ltac list_lpreds l H := match l with 
                        | nil =>  move 
                        | ?a::?l' => nth_lpreds a H;list_lpreds l' H 
                        end. 

Instance nth_size_pred n l : {goal n < size l} -> {goal nth GEnd l n \in l}.
Proof. move => [] H.  constructor. apply/mem_nth. done. Qed.

Instance zero_lt_size_spred a gs  : {goal spred (GBranch a gs)} -> {goal 0 < size gs}.
Proof. move =>[] H. constructor. simpl in H. lia. Qed.

Instance  CGoal_all_apredb a gs : {goal apred (GBranch a gs)} -> {goal all apred gs}. 
Proof. move=>[] H. constructor. simpl in H. lia. Qed.
Instance  CGoal_all_spredb a gs : {goal spred (GBranch a gs)} -> {goal all spred gs}. 
Proof. move=>[] H. constructor. simpl in H. lia. Qed.
Instance  CGoal_all_ppredb a gs : {goal ppred (GBranch a gs)} -> {goal all ppred gs}. 
Proof. move=>[] H. constructor. simpl in H. lia. Qed.
Instance  CGoal_all_npredb a gs p : {goal (npred p) (GBranch a gs)} -> {goal all (npred p) gs}. 
Proof. move=>[] H. constructor. unfold npred in H. simpl in H. move :H. rewrite !inE. split_and. move : H1. rewrite big_map. intros. 
apply/allP=> k Hin. move : Hin.  move/nthP=>Hnth. specialize Hnth with GEnd. destruct Hnth. rewrite -H3.
eapply notin_big in H1. apply : H1. done. Qed.



Instance Goal_msg_action a v g : {goal (apred (GMsg a v g))} -> {goal ptcp_from a != ptcp_to a}. move=>[] H. constructor. simpl in H. split_and. Qed.
Instance Goal_branch_action a gs : {goal (apred (GBranch a gs))} -> {goal ptcp_from a != ptcp_to a}. move=>[] H. constructor. simpl in H. split_and. Qed.

Instance traverse_action_pred_unf : forall g0 g1 i, {goal lpreds [::apred] g0} -> {goal lpreds [::apred] g1} -> {goal apred (g0[s g1//i])}.
Proof.  intros. destruct H,H0. constructor.
elim : g0 g1 i H H0 ;intros;rewrite /=;rs;try done. 
- rifliad. cc. 
- rifliad. cc.  apply H;cc. 
- split_and; cc. apply : H; cc. 
- split_and. cc. rewrite all_map. apply/allP=> ll Hin /=. apply : H;cc. 
Qed.

(*Instance traverse_action_pred_unfG : forall g0 g1 i, {goal lpreds [::apred] g0} -> {goal lpreds  [::apred] g1} -> {goal lpreds  [::apred]  (substitution i g0 g1)}.
Proof. intros. constructor. destruct H,H0. apply traverse_action_pred_unf;cc. Qed.
*)

Lemma size_pred_subst : forall g0 g1 i, size_pred g0 -> size_pred g1 -> size_pred (g0[s g1//i]).
Proof.  
elim;intros;rewrite /=;rs; simpl in *;try done;auto.
- rifliad. rifliad. simpl.  auto. 
- rewrite all_map. apply/andP. split. rewrite size_map. split_and. apply/allP=> ll Hin /=. apply H. done. split_and. apply (allP H3). done. done. 
Qed.


Instance traverse_size_pred_unf : forall g0 g1 i, {goal lpreds [::spred] g0} -> {goal lpreds [::spred] g1} -> {goal spred (g0[s g1//i])}.
Proof.  intros.  constructor.  apply size_pred_subst.   destruct H. cc. destruct H0. cc. Qed.
Print bound.
Check @bound. Check CGPred.
Instance bound_CGPred (A : substType) : CGPred (@bound A). repeat constructor. Qed.
Check CStructural.
Check bound.
Instance CStructural_bound_msg  a u g: CStructural (bound)  (GMsg a u g) g.
constructor. rewrite  /=. done. Qed.

Instance  CGoal_all_boundb a gs : {goal bound (GBranch a gs)} -> {goal all bound gs}. 
move => [] H. constructor.  simpl in H. move : H. rewrite /bound.  rs. rewrite big_map. induction gs. rewrite big_nil. done. rewrite big_cons. rewrite /=. move/eqP=>HH. rewrite IHgs //=. split_and. 
apply/eqP/fsetP=>k. rewrite !inE.
have :  (k \in fv a0 `|` \bigcup_(j <- gs) fv j) = (k \in fset0). move : HH. move/fsetP=>HH. rewrite HH. done. 
rewrite !inE. move/orP/orP. rewrite negb_or. split_and. by apply/negbTE. 

apply/eqP/fsetP=>k. rewrite !inE.
have :  (k \in fv a0 `|` \bigcup_(j <- gs) fv j) = (k \in fset0). move : HH. move/fsetP=>HH. rewrite HH. done. 
rewrite !inE. move/orP/orP. rewrite negb_or. split_and. by apply/negbTE. 
Qed.


Instance  CStructural_boundb a gs g : {goal g \in gs} ->  CStructural bound (GBranch a gs) g. 
Proof. move=>[] H. constructor.  move/Build_CGoal. move/CGoal_all_boundb=>[]. move/allP=>Hall. apply Hall. done. 
Qed.

Instance bound_unf g n : {goal bound (GRec n g)} -> {goal bound (g[s GRec n g//n])}.
Proof. move => [].  constructor. move : b. intros.  rewrite /bound. rewrite fv_subst  /=.  by simpl in b. 
rs. rs_in b. by apply/eqP. Qed.



(*Instance bounde_CGPred : CGPred bounde. repeat constructor. Qed.*)


Instance CStructural_bounde_msg d a u g: CStructural bound (EMsg d a u g) g.
constructor. rewrite  /=. done. Qed.

Instance  CGoal_all_boundeb d a gs : {goal bound (EBranch d a gs)} -> {goal all bound gs}. 
move => [] H. constructor.  simpl in H. move : H.  rewrite /bound. rs. rewrite big_map.  induction gs. rewrite big_nil. done. rewrite big_cons. rewrite /=. move/eqP=>HH. rewrite IHgs //=. split_and. 
apply/eqP/fsetP=>k. rewrite !inE.
have :  (k \in fv a0 `|` \bigcup_(j <- gs) fv j) = (k \in fset0). move : HH. move/fsetP=>HH. rewrite HH. done. 
rewrite !inE. move/orP/orP. rewrite negb_or. split_and. by apply/negbTE. 

apply/eqP/fsetP=>k. rewrite !inE.
have :  (k \in fv a0 `|` \bigcup_(j <- gs) fv j) = (k \in fset0). move : HH. move/fsetP=>HH. rewrite HH. done. 
rewrite !inE. move/orP/orP. rewrite negb_or. split_and. by apply/negbTE. 
Qed.


Instance  CStructural_boundeb d a gs g : {goal g \in gs} ->  CStructural bound (EBranch d a gs) g. 
Proof. move=>[] H. constructor.  move/Build_CGoal. move/CGoal_all_boundeb=>[]. move/allP=>Hall. apply Hall. done. 
Qed.

Instance bounde_unf g n : {goal bound (ERec n g)} -> {goal bound (g[s ERec n g//n])}.
Proof. move => [].  constructor. move : b.   intros.   rewrite /bound. rewrite fv_subst /=. by simpl in b. 
rs. rs_in b. by apply/eqP. Qed.

Instance goallpreds_cons (A : eqType) (p : pred A) g (l : seq (pred A)): {goal p g} -> {goal (lpreds l g) } -> {goal lpreds (p::l) g}. move => [] H [] H0. constructor. unlock lpreds. simpl. unlock lpreds in H0.  split_and. Qed.

Instance goallpreds_nil (A : eqType) (g : A) : {goal lpreds nil g}. constructor. unlock lpreds. simpl. done. Qed. 

Instance goallpreds_allcons (A : eqType) (p : pred A) gs (l : seq (pred A)): {goal all p gs} -> {goal all (lpreds l) gs } -> {goal all (lpreds (p::l)) gs}. move => [] H [] H0. constructor. unlock lpreds. simpl. unlock lpreds in H0. rewrite all_predI. split_and. Qed.

Lemma lpredsT (A : eqType) : forall g, lpreds [::(predT : pred A)] g = true.
Proof. ul. intros. by simpl. Qed.

Instance traverse_predTG (A : eqType)  g : {goal lpreds [::predT : pred A] g}.
constructor. rewrite lpredsT. done. Defined. 

Instance traverse_predTallG  (A : eqType)  (gs : seq A) : {goal all predT gs}.
constructor. apply/allP=>k. done. Defined. 

Instance goallpreds_allnil (A : eqType) (gs : seq A) : {goal all (lpreds nil) gs}. constructor. unlock lpreds. simpl. induction gs. done. simpl. done. Qed. 



Instance all_ForallG : forall (A : eqType)  (l l' : seq A) (P0 P1 : pred A), {hint Forall (fun p => P0 p.1 -> P1 p.2) (zip l l')} -> {hint exists (a : A),True} -> {hint size l = size l'} -> {goal all P0 l} -> {goal all P1 l'}.
Proof. 
move => A l l' P0 P1 [] H0 [] H1 [] H2 [] H3. constructor.  apply/allP => x' Hin.  
move : H0. move/Forall_forall=>Hall.
move : Hin. move/nthP=>Hnth. specialize Hnth with x'. destruct Hnth. rewrite -H0. 
specialize Hall with (nth (x',x') (zip l l') x). move : Hall. rewrite nth_zip /=. intros. apply : Hall. rewrite -nth_zip.  apply/mem_nth. by rewrite size_zip minnE H2  nat_fact. done. apply (allP H3). apply/mem_nth. rewrite H2. done. done. 
Qed.

Instance gType_existsH : {hint exists _ : gType_EqType, True}.
constructor. exists GEnd.  done. Qed.
Check lpreds.

Instance hint_size_eq2  (A : eqType)  (gs gs' : seq A) x0 : {hint size gs = size gs'} -> {goal x0 < size gs'} -> {goal x0 < size gs}.
Proof. case. move => H. case. move => H0. constructor. rewrite H. done. Qed.

(*Definition in_prede p g  := p \in efv g.
Notation iprede := in_pred.

Instance ipred_CGPred p : CGPred (ipred p). constructor. constructor. Qed.*)

(*Important for membership to work*)
Hint Resolve mem_nth : typeclass_instances.

Instance step_action : forall g l g', {goal step g l g'} -> {goal lpreds [::apred;spred] g} -> {goal apred g'}.  
Proof.
move => g l g' [] H [] H0. constructor. elim : H H0; rewrite /=;split_and;cc.
apply H0. cc.
apply H0. cc.
Qed.

Instance step_size : forall g l g',{goal step g l g'} -> {goal lpreds [::apred;spred] g} -> {goal spred g'}.  
Proof.
move => g l g' [] H [] H0. constructor.  elim : H H0; rewrite /=;intros;split_and;cc.
apply H0. cc. rewrite -H.  cc. apply H0. cc. 
Qed.


Instance linear_sgmsg : forall a u g0, {hint Linear (GMsg a u g0)} -> {goal Linear g0}.
Proof. 
move => a u g0. apply chint_imp. rewrite /Linear /=.  intros. move : (H (a::aa_p) a0 aa a1). rewrite cat_cons /=. 
  destruct ( aa_p ++ a0 :: rcons aa a1) eqn:Heqn. case : aa_p H0 Heqn.  done. done.
  intros. have : Tr ((a::aa_p ++ (a0::aa) ++ [::a1])) (GMsg a u g0). auto.  move/H2 => H3.  move : (H3 H1). 
  move => [] mi [] mo. intros. auto. 
Qed.

Instance linear_branch_aux : forall a gs, {hint Linear (GBranch a gs)} -> {goal Forall Linear gs}.  
Proof.
move => a gs. apply chint_imp. intros. apply/List.Forall_forall. intros. rewrite /Linear. intros. unfold Linear in H. have : Tr (a::aa_p ++ a0::aa ++ ([::a1])) (GBranch a gs). move : H0.  move/In_in. move/nthP=>Hnth. specialize Hnth with GEnd. destruct Hnth. rewrite -H3 in H1. apply : TRBranch. eauto. apply : H1. 
intros. apply : H. rewrite -cat_cons in x0. apply : x0. done. 
Qed.

Instance linear_branch : forall a gs n, {hint Linear (GBranch a gs)} -> {goal n < size gs} -> {goal Linear (nth GEnd gs n)}.
Proof. intros. destruct H,H0.  apply Build_CHint in H. apply linear_branch_aux in H. destruct H. move : H. move/Forall_forall. intros. constructor. eauto. cc. Qed.


Instance linear_unf : forall g n, {hint Linear (GRec n g)} -> {goal Linear g[s GRec n g//n]}.
Proof. move => g n. apply chint_imp.
intros.  unfold Linear in *. intros. apply : H. constructor. eauto. done. 
Qed.

