From mathcomp Require Import all_ssreflect zify finmap.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Dep Require Import Global_Syntax Inductive_Linearity Predicates Substitutions Structures.

Let inE :=  Structures.inE.

Inductive proj : gType -> ptcp -> endpoint -> Prop :=
| cp_msg_from g e a u : proj g (ptcp_from a) e -> proj (GMsg a u g) (ptcp_from a) (EMsg Sd (action_ch a) u e)
| cp_msg_to g e a u : proj g (ptcp_to a) e -> proj (GMsg a u g) (ptcp_to a) (EMsg Rd (action_ch a) u e)
| cp_msg_other g a e  u p : p \notin a -> proj g p e -> proj  (GMsg a u g) p e
| cp_branch_from gs es a : size gs = size es -> Forall (fun p => proj p.1 (ptcp_from a) p.2) (zip gs es) -> 
                                 proj (GBranch a gs) (ptcp_from a) (EBranch Sd (action_ch a) es)
| cp_branch_to gs es a : size gs = size es ->Forall (fun p => proj p.1 (ptcp_to a) p.2) (zip gs es) -> 
                               proj  (GBranch a gs) (ptcp_to a) (EBranch Rd (action_ch a) es)
| cp_branch_other gs p e a : p \notin a -> Forall (fun g => proj g p e) gs -> 
                               proj (GBranch a gs) p e
| cp_end p : proj GEnd p EEnd
| cp_rec0 g p n : proj g p (EVar n)  -> proj (GRec n g) p EEnd
| cp_rec1 g p e n : proj g p e  -> e <> EVar n -> n \in (efv e) -> proj (GRec n g) p (ERec n e)
| cp_rec2 g p e n : proj g p e  ->  n \notin (efv e) -> proj (GRec n g) p e
| cp_var n p : proj (GVar n) p (EVar n).
Hint Constructors proj.


Lemma projP : forall g p, lpreds rec_pred g -> proj g p (project g p).
Proof. 
elim;intros;rewrite /=;try done. rifliad. apply cp_rec0. rewrite -(eqP H1). apply H. cc. 
Admitted.
(*apply cp_rec1. apply H. cc. apply negbT in H1.  apply/eqP. done. done. apply cp_rec2. apply H. cc. rewrite H2. done. 
rifliad;eauto. 
norm_eqs. 
apply cp_msg_from;eauto. apply : H. cc.
norm_eqs.  apply cp_msg_to;eauto.  apply : H. cc.
norm_eqs.  apply cp_msg_other. by  rewrite !inE H2 H1. apply : H. cc.
rifliad. 
norm_eqs. apply cp_branch_from. rewrite size_map //=.
apply/forallzipP. by rewrite size_map.
intros. rewrite /=. 
erewrite nth_project. apply : H. eauto. cc.
norm_eqs. apply cp_branch_to. rewrite size_map //=.
apply/forallzipP. by rewrite size_map.
intros. rewrite /=. 
erewrite nth_project. apply : H. eauto.   cc. 
rewrite match_n  /=. apply cp_branch_other. rewrite !inE. norm_eqs. by  rewrite H2 H1. 

apply/forallP. intros. 
have : project (nth GEnd l 0) p = project (nth GEnd l x0) p.

simpl in H. apply : project_predP_aux. eauto.  by rewrite !inE H1 H2. done. 
move=>->. apply : H;cc. 
Qed.*)


(*Instance locked_pred_cons a a0 l : {hint locked_pred rec_pred (GBranch a (a0 :: l))} -> {goal locked_pred rec_pred (GBranch a l)}.
Proof. apply chint_imp. ul. rewrite /=. split_and. move : H0.  rewrite /rec_pred /=. split_and. 2 : { done. move : H0. rewrite rec_predrewrite /rec_pred /=. split_and.  rewrite !locked_split /=; ul;rewrite /=.  split_and. rewrite split_locked_pred. ul. rewrrewrite traverse_pred_split.*)


Lemma project_tw0 : forall g p0 p1, lpreds [::apred;spred;ppred;npred p0;npred p1] g -> project g p0 = project g p1.  
Proof.
elim; rewrite /=;intros;try done. erewrite H;eauto. cc. 
list_lpreds [::3;4] H0. rewrite /= !inE. split_and.
rewrite (negbTE H3) (negbTE H4) (negbTE H6) (negbTE H7). apply H. cc.
list_lpreds [::3;4] H0. rewrite /= !inE. split_and.
rewrite (negbTE H3) (negbTE H4) (negbTE H6) (negbTE H7) !match_n.  apply H. cc. cc. 
Qed.



Instance fv_project : forall g p, {goal lpreds [::bound] g} -> {goal bounde (project g p)}.
Proof. intros. destruct H. constructor. rewrite /bounde. apply/eqP. apply/fsetP=>k. destruct ( (k \in efv (project g p))) eqn :Heqn. move : Heqn. rewrite project_clean_rproject fv_clean. nth_lpreds 0 H.  rewrite /bound. move/eqP/fsetP=>Hall. intros. rewrite -Hall. erewrite (@fv_rproject_in _ p).  done. rewrite project_clean_rproject.  rewrite fv_clean. done. rewrite !inE. done. 
Qed.

Lemma to_bounde e : (efv e == fset0) = bounde e. done. Qed.

Lemma clean_rproject_subst : forall g g0 p i,  lpreds [::bound] g0 -> clean (rproject (g[g g0//i]) p) = (clean (rproject g p))[e (clean (rproject g0 p))//i].
Proof. intros. rewrite rproject_subst clean_subst. done. rewrite -fv_clean. rewrite -project_clean_rproject. apply/eqP. rewrite to_bounde.  cc. Qed.

Lemma project_subst : forall g g0 p i,  lpreds [::bound] g0  -> project g[g g0//i] p = (project g p)[e (project g0 p)//i].
Proof. intros. rewrite !project_clean_rproject. rewrite clean_rproject_subst //=. Qed.


Lemma project_predP_aux : forall a gs p i, lpreds rec_pred (GBranch a gs) ->
p \notin a -> i < size gs  -> (project (nth GEnd gs 0) p) =f= (project (nth GEnd gs i) p).
Proof. 
intros. have : project_pred (GBranch a gs) by cc. 
rewrite /=. split_and. move : H2. move/allP=>Hall. have : (nth GEnd gs i) \in gs by cc.
Admitted.
(* 
move/Hall/eqP/fmapP=>HH0. specialize HH0 with p. move :HH0.  rewrite !mapf_if. rifliad.  case. move=><-. done. move=> _. 
move : H2. move/negbT. rewrite inE negb_or. move/andP=>[].  rewrite inE big_map. intros. move : a0.  rewrite /fresh. destruct (atom_fresh_for_list (a `|` \bigcup_(j <- gs) j)) eqn:Heqn.  rewrite Heqn. 


have : (nth GEnd gs i) \in gs by eauto. move/Hall/eqP/fmapP=>HH0. specialize HH0 with x. move :HH0.  rewrite !mapf_if. rifliad.
case. intros.

have : p \notin ( \bigcup_(j <- gs) j). move : b H0. rewrite !inE. move/orP=>[]. 
move/orP=>[]. move/eqP=>->. rewrite eqxx. done. move/eqP=>->. rewrite eqxx. split_and.  by move/andP=>[] -> ->. 
move => HH0.

clear Heqn. move : n.  move/negP. rewrite !inE. split_and. 
erewrite project_tw0. erewrite (@project_tw0 (nth GEnd gs i)). 
apply : H4. cc.   rewrite /npred. apply/notin_big. done. cc. apply/notin_big. done. cc. cc. apply/notin_big. done. cc. 
apply/notin_big. cc. cc.
move : H2. by rewrite big_map !inE  /fresh Heqn eqxx/=. 
Qed.*)

(*Lemma traverse_nth : forall a gs i P, locked_pred P (GBranch a gs) -> i < size gs -> locked_pred P (nth GEnd gs i).
Proof. intros. simpl in H. eauto.  Qed.

Lemma traverse_nth0 : forall a gs P, subpred P size_pred  -> locked_pred P (GBranch a gs) -> locked_pred P (nth GEnd gs 0).
Proof.
intros. simpl in H0. destruct (andP H0). apply H in H1. simpl in H1. eauto. Qed.

Hint Resolve traverse_nth traverse_nth0.*)


(*Missing setoid rewrite*)
Lemma project_predP : forall a gs p i j, lpreds rec_pred (GBranch a gs) ->
 p \notin a -> i < size gs -> j < size gs -> (project (nth GEnd gs i) p) =f= (project (nth GEnd gs j) p).
Proof. intros. (*erewrite <- project_predP_aux;eauto.   apply : project_predP_aux;eauto. *) Admitted.



 
(*Lemma project_ptcps : forall a gs, project_pred (GBranch a gs) -> size_pred (GBranch a gs)  -> forall p i j, p \notin a -> i < size gs -> j < size gs -> ptcps_of_g (nth GEnd gs i) = ptcps_of_g (nth GEnd gs j).
Proof. intros. erewrite <- project_predP_aux. eauto.   apply : project_predP_aux;eauto. Qed.
*)


Lemma match_n2
     : forall (A B : Type) (gs : seq A) (a : A) (f : A -> B),
       match gs with
       | [::] => f a
       | g' :: _ => f g'
       end = f (nth a gs 0).
Proof. intros. destruct gs. done. done. Qed.




Lemma nth_project : forall gs p i, nth EEnd (map (fun g => project g p) gs) i = project (nth GEnd gs i) p.
Proof.
elim;rewrite /=;try done; intros. rewrite !nth_nil /=. done.
rewrite /=. destruct i;rewrite /=. done. done.
Qed.


