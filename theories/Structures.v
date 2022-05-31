From mathcomp Require Import all_ssreflect zify finmap.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Dep Require Import Global_Syntax Substitutions Predicates.
Let inE := Predicates.inE.


Ltac norm_eqs := repeat (match goal with 
                   | [ H : (_ == _) |- _ ] => move : H => /eqP=>H
                   | [ H : (_ == _) = true |- _ ] => move : H => /eqP=>H
                   | [ H : (_ == _) = false |- _ ] => move : H => /negbT=>H

                  end);subst;repeat (match goal with 
                   | [ H : is_true (?a != ?a_) |- _ ] => rewrite eqxx in H;done 

                  end).
Ltac split_and := intros;repeat (match goal with 
                   | [ H : is_true (_ && _) |- _ ] => destruct (andP H);clear H
                   | [ |- is_true (_ && _) ] => apply/andP;split 

                  end);auto.


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






Lemma notin_big : forall (p : ptcp) gs i, p \notin \bigcup_(j <- gs) (ptcps_of_g j) -> i < size gs -> p \notin ptcps_of_g (nth GEnd gs i).
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
Definition notin_pred p g :=  p \notin (ptcps_of_g g).  
Lemma notin_pred_eq p : notin_pred p =  (fun g => p \notin (ptcps_of_g g)). done. Qed.


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

Class CGPred (A : eqType) (p : pred A) := { _ : pred gType }.

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

Instance resolve_to_lpreds  : forall (l : seq (pred gType)) g0 g1 p, CGPred p -> {hint lpreds l g0} -> CFind p l ->  CStructural p g0 g1 -> {goal p g1}.
Proof. move => l g0 g1 p [] H [] H0 [] H1 [] H2. constructor. apply H2. apply : In_l_preds;eauto. Qed.


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

Instance traverse_action_pred_unf : forall g0 g1 i, {goal lpreds [::apred] g0} -> {goal lpreds [::apred] g1} -> {goal apred (substitution i g0 g1)}.
Proof.  intros. destruct H,H0. constructor.
elim : g0 g1 i H H0 ;intros;rewrite /=;try done. 
- rifliad. cc. 
- rifliad. cc.  apply H;cc. 
- split_and; cc. apply : H; cc. 
- split_and. cc. rewrite all_map. apply/allP=> ll Hin /=. apply : H;cc. 
Qed.

(*Instance traverse_action_pred_unfG : forall g0 g1 i, {goal lpreds [::apred] g0} -> {goal lpreds  [::apred] g1} -> {goal lpreds  [::apred]  (substitution i g0 g1)}.
Proof. intros. constructor. destruct H,H0. apply traverse_action_pred_unf;cc. Qed.
*)
Instance traverse_size_pred_unf : forall g0 g1 i, {goal lpreds [::spred] g0} -> {goal lpreds [::spred] g1} -> {goal spred (substitution i g0 g1)}.
Proof.  intros. constructor.  destruct H ,H0. 
elim : g0 g1 i H H0;intros;rewrite /=; simpl in *;try done;auto.
- rifliad. cc. 
- rifliad. cc. apply H. cc. cc. 
- apply H. cc. cc. 
- split_and. rewrite size_map. cc. 
- rewrite all_map. apply/allP=> ll Hin /=. apply : H;cc. 
Qed.

(*Instance traverse_size_pred_unfG : forall g0 g1 i, {goal lpreds [::size_pred] g0} -> {goal lpreds [::size_pred] g1} -> {goal lpreds [::size_pred] (substitution i g0 g1)}.
Proof. intros. constructor. destruct H,H0.  apply traverse_size_pred_unf;cc. Qed.
*)


Instance bound_CGPred : CGPred bound. repeat constructor. Qed.
Instance CStructural_bound_msg a u g: CStructural bound (GMsg a u g) g.
constructor. rewrite /bound /=. done. Qed.

Instance  CGoal_all_boundb a gs : {goal bound (GBranch a gs)} -> {goal all bound gs}. 
move => [] H. constructor.  unfold bound in H. simpl in H. move : H.  rewrite big_map. rewrite /bound. induction gs. rewrite big_nil. done. rewrite big_cons. rewrite /=. move/eqP=>HH. rewrite IHgs //=. split_and. 
apply/eqP/fsetP=>k. rewrite !inE.
have :  (k \in fv_g a0 `|` \bigcup_(j <- gs) fv_g j) = (k \in fset0). move : HH. move/fsetP=>HH. rewrite HH. done. 
rewrite !inE. move/orP/orP. rewrite negb_or. split_and. by apply/negbTE. 

apply/eqP/fsetP=>k. rewrite !inE.
have :  (k \in fv_g a0 `|` \bigcup_(j <- gs) fv_g j) = (k \in fset0). move : HH. move/fsetP=>HH. rewrite HH. done. 
rewrite !inE. move/orP/orP. rewrite negb_or. split_and. by apply/negbTE. 
Qed.


Instance  CStructural_boundb a gs g : {goal g \in gs} ->  CStructural bound (GBranch a gs) g. 
Proof. move=>[] H. constructor.  move/Build_CGoal. move/CGoal_all_boundb=>[]. move/allP=>Hall. apply Hall. done. 
Qed.

Instance bound_unf g n : {goal bound (GRec n g)} -> {goal bound (g[g GRec n g//n])}.
Proof. move => [].  constructor. move : b.  rewrite /bound. intros. rewrite fv_g_unf /=. by simpl in b. 
cc. Qed.



Instance bounde_CGPred : CGPred bounde. repeat constructor. Qed.
Instance CStructural_bounde_msg d a u g: CStructural bounde (EMsg d a u g) g.
constructor. rewrite /bounde /=. done. Qed.

Instance  CGoal_all_boundeb d a gs : {goal bounde (EBranch d a gs)} -> {goal all bounde gs}. 
move => [] H. constructor.  unfold bounde in H. simpl in H. move : H.  rewrite big_map. rewrite /bounde. induction gs. rewrite big_nil. done. rewrite big_cons. rewrite /=. move/eqP=>HH. rewrite IHgs //=. split_and. 
apply/eqP/fsetP=>k. rewrite !inE.
have :  (k \in efv a0 `|` \bigcup_(j <- gs) efv j) = (k \in fset0). move : HH. move/fsetP=>HH. rewrite HH. done. 
rewrite !inE. move/orP/orP. rewrite negb_or. split_and. by apply/negbTE. 

apply/eqP/fsetP=>k. rewrite !inE.
have :  (k \in efv a0 `|` \bigcup_(j <- gs) efv j) = (k \in fset0). move : HH. move/fsetP=>HH. rewrite HH. done. 
rewrite !inE. move/orP/orP. rewrite negb_or. split_and. by apply/negbTE. 
Qed.


Instance  CStructural_boundeb d a gs g : {goal g \in gs} ->  CStructural bounde (EBranch d a gs) g. 
Proof. move=>[] H. constructor.  move/Build_CGoal. move/CGoal_all_boundeb=>[]. move/allP=>Hall. apply Hall. done. 
Qed.

Instance bounde_unf g n : {goal bounde (ERec n g)} -> {goal bounde (g[e ERec n g//n])}.
Proof. move => [].  constructor. move : b.  rewrite /bounde. intros.  rewrite Substitutions.efv_subst /=. by simpl in b. 
cc. Qed.


Instance goallpreds_cons (p : pred gType) g (l : seq (pred gType)): {goal p g} -> {goal (lpreds l g) } -> {goal lpreds (p::l) g}. move => [] H [] H0. constructor. unlock lpreds. simpl. unlock lpreds in H0.  split_and. Qed.

Instance goallpreds_nil (A : eqType) (g : A) : {goal lpreds nil g}. constructor. unlock lpreds. simpl. done. Qed. 

Instance goallpreds_allcons (p : pred gType) gs (l : seq (pred gType)): {goal all p gs} -> {goal all (lpreds l) gs } -> {goal all (lpreds (p::l)) gs}. move => [] H [] H0. constructor. unlock lpreds. simpl. unlock lpreds in H0. rewrite all_predI. split_and. Qed.

Lemma lpredsT : forall g, lpreds [::(predT : pred gType)] g = true.
Proof. ul. elim;rewrite /=; try done;intros. Qed.

Instance traverse_predTG g : {goal lpreds [::predT : pred gType] g}.
constructor. rewrite lpredsT. done. Defined. 

Instance traverse_predTallG (gs : seq gType) : {goal all predT gs}.
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

Instance hint_size_eq2 (gs gs' : seq gType) x0 : {hint size gs = size gs'} -> {goal x0 < size gs'} -> {goal x0 < size gs}.
Proof. case. move => H. case. move => H0. constructor. rewrite H. done. Qed.


Definition in_pred p g  := p \in fv_g g.
Notation ipred := in_pred.

Instance ipred_CGPred p : CGPred (ipred p). constructor. constructor. Qed.

