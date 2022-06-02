From mathcomp Require Import all_ssreflect zify.
From Equations Require Import Equations.
From mathcomp Require Import finmap.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Dep Require Import Global_Syntax Inductive_Linearity Substitutions.


Let inE := Substitutions.inE.


(*Lemma apply_allP : forall (A : eqType) (P : A -> bool) l x, all P l -> x \in l -> P x. intros. by apply (allP H). Qed.
Lemma apply_allP2 : forall (A : eqType) (P : A -> bool) l x (P0 : bool), P0 && all P l -> x \in l -> P x. 
intros. destruct (andP H). by apply (allP H2). Qed.

Hint Resolve apply_allP apply_allP2.

Lemma and_left : forall (b0 b1 : bool), b0 && b1 -> b0.
Proof. intros. apply (andP H). Qed. 

Lemma and_right : forall (b0 b1 : bool), b0 && b1 -> b1.
Proof. intros. apply (andP H). Qed. 


Lemma true_right : forall (b : bool), b -> b && true.
Proof. intros. rewrite H. done. Qed.

Hint Resolve and_left and_right mem_nth true_right. 
*)





Fixpoint action_pred g :=
match g with 
| GMsg a u g0 => (~~ (ptcp_from a == ptcp_to a)) && action_pred g0
| GBranch a gs => (~~ (ptcp_from a == ptcp_to a)) && all action_pred gs
| GRec _ g0 => action_pred g0
| _ => true 
end.


Fixpoint size_pred (g : gType) :=
match g with 
| GMsg a u g0 => size_pred g0
| GBranch a gs => (0 < size gs) && all size_pred gs
| GRec _ g0 => size_pred g0
| _ => true
end.






Fixpoint rproject g p := 
match g with 
| GEnd => EEnd
| GMsg a u g0 => if p == (ptcp_from a) then EMsg Sd (action_ch a) u (rproject g0 p) 
                               else if p == (ptcp_to a) then EMsg Rd (action_ch a) u (rproject g0 p) else rproject g0 p
| GBranch a gs => if p == (ptcp_from a) then EBranch Sd (action_ch a) (map (fun g => rproject g p) gs)
                                else if p == (ptcp_to a) then EBranch Rd (action_ch a) (map (fun g => rproject g p) gs) else if gs is g'::gs' then rproject g' p else EEnd
| GRec n g => (ERec n (rproject g p))
| GVar n => EVar n
end.



Fixpoint clean e := 
match e with 
| EMsg d c v e0 => EMsg d c v (clean e0)
| EBranch d c es => EBranch d c (map clean es)
| ERec n e0 => if clean e0 == EVar n then EEnd else if n \in fv e0 then ERec n (clean e0) else clean e0
| EVar j => EVar j
| EEnd => EEnd
end.


Lemma fv_clean e :  fv (clean e) = fv e. 
Proof. elim : e;try solve [rewrite /=;try done];intros. 
rewrite /=. rifliad. rewrite (eqP H0) in H. rs. rewrite -H /=. by rewrite fsetDv. rs. rewrite H. done.
rewrite /= H. rs.  rewrite mem_fsetD1 //=. lia. 
rs. rewrite /= !big_map. induction l. rewrite !big_nil. done. rewrite !big_cons. f_equal. rewrite H. done. rewrite !inE. done. apply IHl. intros. apply H. rewrite !inE H0.  lia.
Qed.


(*Lemma subst_nop : forall e e' x, x \notin (fv e) -> subst_e x e e' = e. Proof. 
elim;rewrite /=;try done;intros. move : H. rewrite !inE.  rewrite neg_sym. move/negbTE=>->. done. 
move : H0. rewrite !inE. move/orP=>[]. by rewrite eq_sym=>->.  
intros. rifliad. rewrite H //=. 
f_equal. auto. f_equal. rewrite big_map in H0.  induction l. done. simpl. f_equal.  apply H.  rewrite !inE.  lia. simpl in H0. move : H0. 
rewrite big_cons. rewrite !inE. split_and. apply IHl. intros. apply H. rewrite !inE H1. lia. done. move : H0.  rewrite big_cons !inE. split_and. 
Qed.*)




(*Lemma fv_subst : forall  e e' n x, fv e' = fset0 -> n <> x -> (n \in (fv (subst_e x e e'))) = (n \in (fv e)).
Proof. elim;rewrite /=;try done;intros. rewrite !inE. rifliad. rewrite H !inE. have : n0 == n = false by lia. by move=>->. 
rewrite /= !inE. done. 
rifliad. rewrite /=. Check mem_map. Search (_ \in (map _ _)). Search _ (_ \in _ = _ \in _).  Search _ ((is_true _ -> is_true _) -> _ = _). rewrite !inE.  destruct (n0 != n)eqn:Heqn;rewrite /= //=.   rewrite Heqn //=.
apply H. done. done. rewrite Heqn //=. 
rewrite !big_map.  elim : l H. rewrite !big_nil. done. intros. rewrite !big_cons. rewrite !inE. rewrite H2 //=. 
destruct ( (n \in fv a)) eqn:Heqn; rewrite !Heqn //=. apply H. intros. apply H2. rewrite !inE H3. lia. done. done. 
Qed.*)

Lemma fv_nil_evar : forall e n, fv e = fset0 -> e <> EVar n. 
Proof.
elim;rewrite /=;try  done. intros. have : n \in [fset n]. by  rewrite !inE. move : H. move/fsetP=>->. done. 
Qed.

Lemma fset_nil : forall (A : choiceType) (n : A), [fset n] = fset0 -> False.
Proof. intros. move : H. move/fsetP=>HH. suff : n \in [fset n] = (n \in fset0). rewrite !inE. done. by rewrite HH. 
Qed.

Lemma clean_subst : forall (e0 : endpoint)  e' x, fv e' = fset0 -> clean (e0[s e'//x]) = (clean e0)[s clean e'//x].
Proof.
elim;intros. 
- rs. rifliad.
- rs. done.
- rs. case_if.  
 * rs. rewrite (eqP H1) /=. rifliad. rs. by rewrite /= eqxx. rewrite subst_nop //=. rewrite fv_clean. lia. 
 * rs. rewrite /= H //=.  rewrite fv_subst //=. symmetry. case_if.
  ** rs. rewrite (eqP H2) /=. rs. rewrite H1 eqxx. done.
  ** case_if.
   *** rs. rewrite /= H1. rifliad. exfalso. move : H4.  destruct (clean e);rewrite /=;rs. rifliad. move/eqP. apply : fv_nil_evar. 
       rewrite fv_clean //=. by rewrite H2. done. done. done. rifliad. 

   *** rs. rifliad. exfalso. move : H5. rewrite !inE H3. have : n != x by lia. move=>->. done. rewrite !inE H3.
       have : n != x by lia. move=>-> /=. rifliad. 
       destruct (clean e);rewrite /=;rs.  rifliad. rewrite (eqP H5) in H4. rs_in H4. rewrite eqxx in H4. rewrite -fv_clean in H0.  rewrite (eqP H4) in H0. rs_in H0. by apply fset_nil in H0. rs_in H4. rewrite H5 in H4. lia. done.
      all : try  by move : (eqP H4).   rs_in H4. rifliad. rs. f_equal. auto.  rs. f_equal. 
- rewrite -!map_comp. apply/eq_in_map. move => ll Hin /=. rewrite H //=.
Qed.

Lemma rproject_subst : forall g g0 p i,  rproject (g[s g0//i]) p = (rproject g p)[s (rproject g0 p)//i].
Proof. elim;rewrite /=;try done;intros;rs. rifliad. rifliad. rewrite /=.  rewrite H. done.  
rifliad. simpl. rs. f_equal. done. simpl. rs. f_equal. done. 
rifliad. simpl. rs. f_equal. 
rewrite -!map_comp. apply/eq_in_map. move=>ll Hin. simpl. apply H.  done. 
simpl. rs.  f_equal.
rewrite -!map_comp. apply/eq_in_map. move=>ll Hin. simpl. apply H.  done. destruct l. done. simpl. apply H. rewrite !inE. done. 
Qed.





Fixpoint project g p := 
match g with 
| GEnd => EEnd
| GMsg a u g0 => if p == (ptcp_from a) then EMsg Sd (action_ch a) u (project g0 p) 
                               else if p == (ptcp_to a) then EMsg Rd (action_ch a) u (project g0 p) else project g0 p
| GBranch a gs => if p == (ptcp_from a) then EBranch Sd (action_ch a) (map (fun g => project g p) gs)
                                else if p == (ptcp_to a) then EBranch Rd (action_ch a) (map (fun g => project g p) gs) else if gs is g'::gs' then project g' p else EEnd
| GRec n g => if (project g p) == EVar n then EEnd else if n \in fv (project g p) then ERec n (project g p) else project g p
| GVar n => EVar n
end.

Lemma match_n : forall (gs : seq gType) k,  match gs with
  | [::] => EEnd
  | g'0 :: _ => project g'0 k end = project (nth GEnd gs 0) k.
Proof.
elim. done. intros. rewrite /=. done.
Qed.


Lemma project_clean_rproject : forall g p, project g p = clean (rproject g p).
Proof.
elim;rewrite /=;try done;intros.
- rifliad.
 * move : H1. by  rewrite -H (eqP H0) eqxx. 
 * move : H1. by  rewrite -H (eqP H0) eqxx. 
 * move : H0. rewrite H (eqP H2) eqxx. done. 
 * rewrite H. done. 
 * rewrite H in H1. rewrite fv_clean in H1. lia. 
 * move : H1.  rewrite H (eqP H2) /= inE eqxx. done. 
 * move : H1.  rewrite H fv_clean H3.  done. 
- rifliad;rewrite //=;try f_equal;eauto.
- rifliad;rewrite //=;try f_equal;eauto.
 * rewrite -map_comp. induction l. done. simpl.  f_equal.  apply H. rewrite !inE. lia. apply IHl. intros. apply H. rewrite !inE H1.
 lia. 
 * rewrite -map_comp. induction l. done. simpl.  f_equal.  apply H. rewrite !inE. lia. apply IHl. intros. apply H. rewrite !inE H2.
 lia. 
destruct l;try done.  apply H. rewrite !inE. done. 
Qed.

(*Lemma fv_rproject_in : forall g p n,  n  \in (fv (project g p)) -> n \in (fv_g g).
Proof. move => g p n. rewrite project_clean_rproject fv_clean. move : g p n.
elim;rewrite /=;intros;try done. move : H0. rewrite !inE. split_and. eauto.  
destruct (p == ptcp_from a) eqn:Heqn.  simpl in H0. eauto. 
destruct (p == ptcp_to a) eqn:Heqn2.  simpl in H0. eauto. 
eauto. move : H0.  rifliad.  simpl. rewrite !big_map. 
elim : l H n.  rewrite !big_nil. done. intros. move : H2.  rewrite !big_cons !inE.  move/orP=>[]. move/H1.  move=>-> //=. 
 intros. apply/orP. right. apply H.  intros. apply : H1. rewrite !inE H2. lia. eauto. done.

elim : l H n.  done. simpl. intros. move : H3.  rewrite !big_cons !inE. move/orP=>[]. move/H2.  move=>-> //=. intros. apply/orP. right. apply H.  intros. apply : H2. rewrite !inE H3. lia. eauto. done. rewrite big_map.
destruct l. done. intros. rewrite big_cons !inE. erewrite H. done. rewrite !inE //=. eauto. 
Qed.*)




Definition projmap  (S : fset_ptcp) (g : gType)  : env := [fmap p : S => project g (val p)].

(*From metatheory*)
Definition ptcp_le (p0 p1 : ptcp) := let: Ptcp n0 := p0 in let: Ptcp n1 := p1 in n0 <= n1.

  Lemma nat_list_max : forall (xs : list ptcp),
    { n : ptcp | forall x, x \in xs -> ptcp_le x  n }.
  Proof.
    induction xs as [ | x xs [y H] ].
    (* case: nil *)
    exists (Ptcp 0). inversion 1.
    (* case: cons x xs *) destruct x,y.
    exists (Ptcp (n + n0)%nat). intros z J. move : J. rewrite inE. move/orP=>[]. move/eqP=>->. rewrite /=. lia. move/H. rewrite /ptcp_le. destruct z.  lia. 
   Qed.

 Lemma atom_fresh_for_list :
    forall (xs : list ptcp), { n : ptcp | ~ n \in xs }.
  Proof.
    intros xs. destruct (nat_list_max xs) as [x H]. destruct x. exists (Ptcp (n.+1)).
    intros J. rewrite /ptcp_le in H. apply H in J. lia. 
  Qed. 
Definition fresh (S : fset_ptcp) :=
    match atom_fresh_for_list S with
      (exist x _ ) => x
    end.



From Paco Require Import paco.

(*Inductive UnravelE (r : endpoint -> endpoint -> Prop) : endpoint -> endpoint -> Prop :=
 | UEndE : UnravelE r EEnd EEnd
 | UMsgE d c u g0 sg0 : UnravelE r g0 sg0 -> UnravelE r (EMsg d c u g0) (EMsg d c u sg0)
 | UBranchE d c gs sgs : size gs = size sgs -> Forall (fun p => UnravelE r p.1 p.2) (zip gs sgs) ->  UnravelE r (EBranch d c gs) (EBranch d c sgs)
 | URecE g sg n : r g[e ERec n g//n] sg  -> UnravelE r (ERec n g) sg.
Hint Constructors UnravelE.
Notation unf := (paco2 UnravelE bot2).


Definition ueqe e0 e1 := exists e, unf e0 e /\ unf e1 e.*)

Inductive Unravele (r : endpoint -> endpoint -> Prop) : endpoint -> endpoint -> Prop :=
 | UEnde : Unravele r EEnd EEnd
 | UVar n : Unravele r (EVar n) (EVar n)
 | UMsge u g0 g0' d c : r g0 g0' -> Unravele r (EMsg d c u g0) (EMsg d c u g0')
 | UBranche gs gs' d c : size gs = size gs' -> Forall (fun p => r p.1 p.2) (zip gs gs') ->  Unravele r (EBranch d c gs) (EBranch d c gs')
 | URece g g' n : r g[s ERec n g//n] g'  -> Unravele r (ERec n g) g'
 | URece2 g g' n : r g g'[s ERec n g'//n]  -> Unravele r g (ERec n g')
 | Utrans g0 g1 g2 : Unravele r g0 g1 -> Unravele r g1 g2 -> Unravele r g0 g2. (*Should be omitted later, probably not needed*)
Hint Constructors Unravele.
Notation "e0 =( R )= e1" := (Unravele R e0 e1)(at level 60).

Notation "e =f= e1" := (paco2 Unravele bot2 e e1)(at level 60).


(*Notation eq_unf e0 e1 := (is_true (eunf e0 == eunf e1)).*)

Lemma ueqe_refl : forall e,  e =f= e.
Proof. pcofix CIH. case;auto;intros. 
pfold. constructor. done. apply/Forall_forall. intros. move : H. move/nthP=>Hnth. specialize Hnth with (EEnd,EEnd). destruct Hnth. rewrite -H0. rewrite nth_zip /=. right. apply CIH. done. pfold. constructor. left. pfold. constructor.  right. done. 
Qed.
Ltac ich H := inversion H;clear H;subst;try done.
Ltac pc := pfold;constructor.

Hint Resolve ueqe_refl. 

Lemma ueqe_sym  : forall e0 e1, e0 =f= e1 ->  e1 =f= e0. 
Proof. Admitted.

Lemma ueqe_trans : forall e0 e1 e2, e0 =f= e1 -> e1 =f= e2 -> e0 =f=  e2.
Proof. Admitted.

Add Parametric Relation : endpoint (fun e0 e1 => e0 =f= e1)
  reflexivity proved by ueqe_refl
  symmetry proved by ueqe_sym
  transitivity proved by ueqe_trans
  as endpoint_setoid.


(*Lemma bool_true (b : bool) : b -> b = true.
destruct b. done. done. 
Qed.*)







Lemma monotone_ueqe : monotone2 Unravele.
Proof. intro. intros.  induction IN;auto.
constructor. done. induction H0. done. auto. eauto.   
Qed.

Hint Resolve monotone_ueqe : paco.

Lemma Unravele_r : forall e0 e1 r, paco2 Unravele bot2 e0 e1 -> paco2 Unravele r e0 e1.
Proof. pcofix CIH.
intros. pfold. apply : monotone_ueqe. punfold H0. intros. ich PR. right. apply CIH. done. Qed.

Hint Resolve Unravele_r.




Definition ueqe_dec (e0 e1 : endpoint) := true.

Lemma ueqeP e0 e1 : reflect (e0 =f= e1) (ueqe_dec e0 e1).
Proof. Admitted.


Fixpoint project_pred  (g : gType):=  
match g with 
| GMsg a u g0 => project_pred g0 
| GBranch a gs => let S := ptcps g in 
                 all (fun g' => all (fun p => ueqe_dec (project (nth GEnd gs 0) p) (project g' p)) (fresh S |` (S  `\` a))) gs && (all project_pred gs)
| GRec _ g0 => project_pred g0
| _ => true 
end.
