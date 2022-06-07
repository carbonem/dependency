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
(**)
(*Reserved Notation "e0 =f= e1" (at level 60). *)


Fixpoint eguarded n g := 
match g with 
| EVar n0 => n0 != n
| ERec n0 g0 => (n == n0) || eguarded n g0
| _ => true
end.

Fixpoint econtractive g := 
match g with 
| ERec n g0 => (eguarded n g0) && (econtractive g0)
| EMsg _ a u g0 => econtractive g0
| EBranch _ a gs => all econtractive gs 
| _ => true 
end.



Fixpoint emu_height g :=
match g with
| ERec n g0 => (emu_height g0).+1
| _ => 0
end.

Definition eunf g := if g is ERec n g' then (g'[s ERec n g'//n]) else g.

Lemma emu_height_subst : forall g0 g1  i, eguarded i g0 -> econtractive g0 -> emu_height (g0[s g1//i]) = emu_height g0.
Proof. 
elim; try solve [by rewrite /=].
- rewrite /=. rs.  intros. split_and. rewrite (negbTE H). done. 
- intros. simpl. simpl in H0. rs. split_and. destruct (i == n) eqn:Heqn.  rewrite eq_sym Heqn. done.  
  simpl in H1. rifliad. rs. split_and. 
Qed.


Lemma fsubset_in : forall (A : choiceType) (b c : {fset A}), b `<=` c -> (forall j, j \in b -> j \in c).
Proof.
intros. Search _ fsub1set. move : H0. rewrite -!fsub1set.  intros. apply : fsubset_trans. apply : H0. apply H. 
Qed.

(*Lemma efv_subst : forall (g : endpoint) g0 n, fv g0 `<=` fv g  -> fv (g[s g0 // n]) = fv g `\ n. 
Proof. 
elim;rewrite /=;rs;intros;apply/fsetP=>k;rewrite !inE.
- rifliad. rewrite (eqP H0). move : H.  move/fsubset_in =>HH. rewrite -(eqP H0). specialize HH with k. rewrite !inE in HH. 
destruct (k \in fv g0). destruct (eqVneq k n). simpl. specialize HH with k. rewrite -HH. move/fsubset_ rewrite /bound. move/eqP=>->. rewrite !inE. by destruct (eqVneq k n0).
- rewrite /= !inE. destruct (eqVneq k n). subst. lia. lia. 
- lia.
- rifliad. rewrite /= (eqP H1) !inE. destruct (k != n0);rewrite /=. done. done.
- rewrite /= H //= !inE. destruct (k != n);rewrite /=;try lia.  rewrite H //= !inE. done.
- rewrite !big_map. induction l. rewrite !big_nil !inE. lia. 
  rewrite !big_cons !inE H //= !inE. destruct (k != n);rewrite /=. destruct (k \in fv a) eqn:Heqn;rewrite Heqn //=.
  rewrite /= in IHl. apply IHl. intros. apply H. eauto. done. rewrite /= in IHl. apply IHl. intros. apply H. eauto. done.
Qed.*)

(*Lemma fv_subst : forall g g0 n, ebound g0 -> fv (g[e g0 // n]) = fv g `\ n. 
Proof. 
elim;rewrite /=;intros;apply/fsetP=>k;rewrite !inE.
- rifliad. rewrite (eqP H0). move : H.  rewrite /bound. move/eqP=>->. rewrite !inE. by destruct (eqVneq k n0).
- rewrite /= !inE. destruct (eqVneq k n). subst. lia. lia. 
- lia.
- rifliad. rewrite /= (eqP H1) !inE. destruct (k != n0);rewrite /=. done. done.
- rewrite /= H //= !inE. destruct (k != n);rewrite /=;try lia.  rewrite H //= !inE. done.
- rewrite !big_map. induction l. rewrite !big_nil !inE. lia. 
  rewrite !big_cons !inE H //= !inE. destruct (k != n);rewrite /=. destruct (k \in fv a) eqn:Heqn;rewrite Heqn //=.
  rewrite /= in IHl. apply IHl. intros. apply H. eauto. done. rewrite /= in IHl. apply IHl. intros. apply H. eauto. done.
Qed.*)


Lemma bound_subst : forall (g : endpoint) g' i, fv g = [fset i] -> bound g' -> bound (g[s g'//i]).
Proof. intros. move : H0. rewrite /bound. move/eqP=>HH. rewrite -HH. apply/eqP.  rewrite fv_subst. rewrite H HH. apply/fsetP=>k. rewrite !inE. destruct (eqVneq k i);done.  rewrite /bound. done. 
Qed.

Lemma notin_eguarded : forall g n, n \notin fv g  -> eguarded n g.
Proof. elim;rewrite /bound //=;intros. move : H. rewrite !inE. lia. move : H0. rewrite !inE. move/orP=>[]. lia. intros.  
rewrite H //=. lia. 
Qed.

Implicit Type (g : endpoint).

Lemma bound_notin : forall g n, bound g -> n \notin fv g.
Proof. intros. rewrite /bound in H. rewrite (eqP H) !inE. done. Qed.
Lemma bound_eguarded : forall g n, bound g  -> eguarded n g.
Proof. intros. apply notin_eguarded. apply bound_notin. done. Qed.

Lemma eguarded_subst : forall g g' n i, eguarded n g -> bound g' -> eguarded n (g)[s g' // i].
Proof. elim;rewrite /=;intros. rs. rifliad. apply bound_eguarded. done. done. rs. rifliad. rs. 


destruct (orP H0). by rewrite H3.  rewrite H //=. lia. done. done.
Qed.



Lemma econtractive_subst : forall g g' i, (*i \in fv g ->*) econtractive g -> econtractive g' -> bound g' -> econtractive (substitute i g g').
Proof.
elim;  (try solve [rewrite /= ;auto]).
- rewrite/=;rs. move => v g' i j. case : (eqVneq v i).  done. simpl. done.
- intros. rewrite /=. rs. rifliad. simpl. split_and. simpl in H1. split_and. apply eguarded_subst. simpl in H0. split_and. done.  apply H. simpl in H0. move : H0. split_and. done. done. 
- rewrite /=. rs. intros. move : H0. intros. rewrite all_map. apply/allP=> l' Hin. simpl. apply H;auto.  
  apply (allP H0). done. 
Qed.

Lemma bound_econtractive_subst : forall g0 g1 i, fv g0 = [fset i] -> bound g1 ->   econtractive g0 -> econtractive g1 ->  bound (g0[s g1//i]) && econtractive (g0[s g1//i]).
Proof.
intros.  split_and. apply bound_subst;auto. apply econtractive_subst;auto.  
Qed.


Notation e_pred g := (bound g && econtractive g). 


(*Lemma substitute_nop : forall g g' x, x \notin (fv g) -> substitute x g g' = g. 
Proof. 
elim;rewrite /=;try done;intros. move : H. rewrite !inE.  rewrite neg_sym. move/negbTE=>->. done. 
move : H0. rewrite !inE.  move/orP=>[]. intros. by  rewrite eq_sym a. rifliad. intros. f_equal. auto. f_equal. 
auto.
f_equal. rewrite big_map in H0.  induction l. done. simpl. f_equal.  apply H.  rewrite !inE.  lia. move : H0. 
rewrite big_cons. rewrite !inE. split_and. apply IHl. intros. apply H. rewrite !inE H1. lia. done. move : H0.  rewrite big_cons !inE. split_and. 
Qed.*)

Lemma eunf_pred : forall g , e_pred  g -> e_pred (eunf g).
Proof.
intros. rewrite /eunf. destruct g. move : (andP H)=>[];intros.  apply/andP. split. simpl. simpl in a. lia. simpl in *. lia. 
- done.
- simpl in *. split_and. done. destruct (n \notin (fv g)) eqn:Heqn.  rewrite subst_nop //=.  move : H.  rewrite /bound /=. rewrite /=. rs.
  rewrite mem_fsetD1 //=.  rs. split_and. 

 split_and. apply bound_subst. move : H0. rewrite /bound. rs. intros. apply/fsetP=>k. rewrite !inE. 
  destruct  (eqVneq k n). subst. have : n \in fv g. lia. done. have : false = (k \in fset0).  done. move=>->. move : H0. move/eqP/fsetP=>H0. rewrite -H0. rewrite !inE i /=. done. 
  done. apply econtractive_subst.  simpl in H1. split_and. done. done. 
Qed.


Lemma eiter_pred : forall k e,  e_pred e -> e_pred (iter k (fun g => eunf g) e).
Proof. elim;rewrite /=;intros. apply/andP.  destruct (andP H). split;auto. 
apply eunf_pred. apply H. done. 
Qed.


Lemma emu_height_eunf : forall g , e_pred g -> (emu_height g).-1 = emu_height (eunf g).
Proof.
move => g. rewrite /=. elim : g; try solve [intros;rewrite /=;done].
- intros. rewrite /eunf. rs.  rewrite /=. rs. split_and. simpl in H1,H2. split_and. rewrite emu_height_subst. done. done. done. 
Qed.


Lemma emu_height_iter_eunf : forall k g , e_pred g -> (emu_height g) - k = (emu_height (iter k (fun g => eunf g) g)). 
Proof.
elim;intros. rewrite /=. lia.
rewrite /=. have : emu_height g - n.+1 = (emu_height g - n).-1 by lia. move=>->. 
erewrite H. 2 : {  eauto. } erewrite emu_height_eunf. done. apply eiter_pred. done. 
Qed.


Lemma eiter_eunf_not_rec : forall sg k i, e_pred sg -> emu_height sg <= k -> forall g, iter k (fun g => eunf g) sg <> ERec i g.
Proof.
intros. simpl in *. apply (emu_height_iter_eunf k) in H. move : H. 
have : emu_height sg - k  = 0 by lia. move=>->. intros. destruct ((iter k (fun g => eunf g) sg));try done.
Qed.

Notation full_eunf g := (iter (emu_height g) (fun g' => eunf g') g). 


Definition next g :=
match full_eunf g with 
| EMsg _ _ _ g0 => [::g0]
| EBranch _ _ gs => gs
| _ => [::]
end.

Definition act_of g :=
match full_eunf g with 
| EMsg _ a _ _ => Some a
| EBranch _ a _ => Some a
| _ => None
end.

Inductive bisimilar_f (r : endpoint -> endpoint -> Prop) : endpoint -> endpoint -> Prop :=
 BF e0 e1 : act_of e0 = act_of e1 -> size (next e0) = size (next e1) -> Forall (fun p => r p.1 p.2) (zip (next e0) (next e1)) ->  bisimilar_f r e0 e1.


Lemma mono_bisim : monotone2 bisimilar_f.
Proof.
move => x. intros. induction IN. constructor. done. done.
apply/forallzipP. done. intros. move : H1. move/forallzipP=>Hzip. 
simpl in Hzip.  simpl. apply LE. apply : Hzip. done. done. 
Grab Existential Variables. all : repeat constructor.
Qed. 

Hint Resolve mono_bisim : paco.

Definition bisimilar e0 e1  : Prop := paco2 bisimilar_f bot2 e0 e1.

Fixpoint bisim_dec_aux n S e0 e1 :=
if n is n'.+1 then ((e0,e1) \in S) || (act_of e0 == act_of e1) && (size (next e0) == size (next e1)) && 
all (fun p => bisim_dec_aux n' ((e0,e1)::S) p.1 p.2) (zip (next e0) (next e1))
else (e0,e1) \in S.
Open Scope nat_scope.

Fixpoint esize e := 
match e with 
| EMsg _ _ _ e0 => (esize e0).+1
| EBranch _ _ es => foldr (fun e0 acc => (esize e0) + acc ) 0 es
| ERec N e0 => (esize e0).+1
| _ => 1
end.

Fixpoint bisim_dec e0 e1 := bisim_dec_aux ((esize e0) * (esize e1)) nil e0 e1.

Lemma bisimP : forall e0 e1, reflect (bisimilar e0 e1) (bisim_dec e0 e1). 
Proof. Admitted.
Lemma bisimP2 : forall e0 e1 R S, (forall e0 e1, R e0 e1 <-> (e0,e1) \in S ) -> exists n,  (bisimilar_f R e0 e1) <-> (bisim_dec_aux n S e0 e1). 
Proof. Admitted.

Fixpoint project_pred  (g : gType):=  
match g with 
| GMsg a u g0 => project_pred g0 
| GBranch a gs => let S := ptcps g in 
                 all (fun (g' : gType)  => 
                         all (fun p => bisim_dec (project (nth GEnd gs 0) p) (project g' p)) 
                         (fresh S |` (S `\` a )))
                      gs
                 && (all project_pred gs)
| GRec _ g0 => project_pred g0
| _ => true 
end.






(*Lemma in_foldr : forall l n,  n \in foldr (fun g' : gType => cat (fv_g g')) nil l ->  exists g, g \in l /\ n \in (fv_g g).
Proof. elim;try done;move => l n H n'.
rewrite /= mem_cat. move/orP=>[]. intros. exists l. rewrite !inE /= a. auto.
move/H. move=>[] x [].  intros. exists x. rewrite !inE a b. lia. Qed.*)

(*Lemma in_foldr2 : forall l n p g, g \in l -> n \in (fv (project  g p)) ->  n \in foldr (fun g' : gType => cat (fv (project g' p))) nil l.
Proof. elim;try done;intros. move : H0.
rewrite !inE. move/orP=>[]. move/eqP. intros. subst. simpl. rewrite mem_cat H1. done. intros.  simpl. rewrite mem_cat. apply/orP. right. apply : H. eauto. done. 
Qed.*)


(*
Lemma fv_project_in : forall g p n, lpreds rec_pred g ->  (n \in (fv_g g)) -> (n  \in (fv (project g p))).
Proof.
elim;rewrite //=;intros. move : H1. rewrite !inE.  split_and. apply (H p) in H3;last cc.
- rifliad. rewrite (eqP H1) in H3. simpl in H3. rewrite !inE in H3. lia. 
  simpl. Admitted. 
(*rewrite !inE.  split_and. 
- apply (H p) in H1;last cc. rifliad.
- rifliad. simpl. rewrite !big_map. 
  apply : big_cup_in.  intros. apply : H. done. cc. cc. apply/big_cup_in.  intros. apply : H4.  apply/big_cup_in. intros. apply : H4. rewrite big_map in H1. done. 
  rewrite /= !big_map.  apply : big_cup_in.  intros. apply : H. done. cc. eauto. rewrite big_map in H1. done. 
- rewrite match_n. apply H. cc. cc. move : H1. rewrite big_map foldr_exists. move/hasP=>[] x. intros. 
  intros.  move : p0. move/nthP=>Hnth. specialize Hnth with GEnd. destruct Hnth.

  apply : fv_rproject_in. 
  erewrite project_predP. apply : H. apply/mem_nth. apply : H1. cc. rewrite H4.  done. eauto.  cc.   all:cc. instantiate (1 := fresh a). rewrite /fresh. destruct (atom_fresh_for_list a). apply/negP.  move => HH. apply n0. destruct a. move : HH. rewrite !inE.  done. 
Qed.*)

Lemma fv_project_eq : forall g p n, lpreds rec_pred g ->  (n \in fv_g g) = (n \in fv (project g p)).
Proof. intros. destruct ( (n \in fv_g g)) eqn:Heqn. rewrite fv_project_in //=.
destruct ((n \in fv (project g p))) eqn:Heqn2. erewrite fv_rproject_in in Heqn. done. eauto. done. 
Qed.*)



(*Lemma fv_g_unf : forall g g0 n, bound g0 -> fv_g (g[g g0 // n]) = fv_g g `\ n. 
Proof. 
elim;rewrite /=;intros;apply/fsetP=>k;rewrite !inE.
- rifliad. rewrite (eqP H0). move : H.  rewrite /bound. move/eqP=>->. rewrite !inE. by destruct (eqVneq k n0).
- rewrite /= !inE. destruct (eqVneq k n). subst. lia. lia. 
- lia.
- rifliad. rewrite /= (eqP H1) !inE. destruct (k != n0);rewrite /=. done. done.
- rewrite /= H //= !inE. destruct (k != n);rewrite /=;try lia.  rewrite H //= !inE. done.
- rewrite !big_map. induction l. rewrite !big_nil !inE. lia. 
  rewrite !big_cons !inE H //= !inE. destruct (k != n);rewrite /=. destruct (k \in fv_g a0) eqn:Heqn;rewrite Heqn //=.
  rewrite /= in IHl. apply IHl. intros. apply H. eauto.  done. rewrite /= in IHl. apply IHl. intros. apply H. eauto. done.
Qed.

*)


(*
Inductive unf_eq : endpoint -> endpoint -> Prop :=

(*Use Pierces algorithm*)
Inductive unf_eq : endpoint -> endpoint -> Prop :=
 | UEE : EEnd =f= EEnd
 | UEV n :  (EVar n) =f= (EVar n)
 | UEM u g0 g0' d c : g0 =f= g0' -> (EMsg d c u g0) =f= (EMsg d c u g0')
 | UEB gs gs' d c : esize gs = esize gs' -> Forall (fun p => p.1 =f= p.2) (zip gs gs') ->   (EBranch d c gs) =f= (EBranch d c gs')
 | UER2 g g' n : g' =f= g'  -> (ERec n g) =f=  (ERec n g')
 | UERL g g' n : g[s ERec n g//n] =f= g'  -> (ERec n g) =f=  g'
 | UERR g g' n : g =f= g'[s ERec n g'//n]  -> g =f= (ERec n g')
 where "e0 =f= e1" := (unf_eq e0 e1).
Set Elimination Schemes.
Hint Constructors unf_eq.


Lemma unf_eq_ind
     : forall P : endpoint -> endpoint -> Prop,
       P EEnd EEnd ->
       (forall n : nat, P (EVar n) (EVar n)) ->
       (forall (u : value) (g0 g0' : endpoint) (d : dir) (c : ch), g0 =f= g0' -> P g0 g0' -> P (EMsg d c u g0) (EMsg d c u g0')) ->
       (forall (gs gs' : seq endpoint) (d : dir) (c : ch),
        esize gs = esize gs' -> 
Forall (fun p : endpoint * endpoint => p.1 =f= p.2) (zip gs gs') -> 
Forall (fun p : endpoint * endpoint => P p.1  p.2) (zip gs gs') ->
P (EBranch d c gs) (EBranch d c gs')) ->

       (forall (g g' : endpoint) (n : nat), g' =f= g' -> P g' g' -> P (ERec n g) (ERec n g')) ->
       (forall (g : endpoint_substType) (g' : endpoint) (n : nat), (g)[s ERec n g // n] =f= g' -> P (g)[s ERec n g // n] g' -> P (ERec n g) g') ->
       (forall (g : endpoint) (g' : endpoint_substType) (n : nat), g =f= (g')[s ERec n g' // n] -> P g (g')[s ERec n g' // n] -> P g (ERec n g')) ->
       forall e e0 : endpoint, e =f= e0 -> P e e0.
Proof. 
intros. move : e e0 H6. fix IH 3. intros. destruct H6.
apply H. apply H0. apply H1. auto. auto. apply H2. done. 
done. induction H7. done. constructor. auto. done. apply H3. done. 
auto. apply : H4. done. auto. apply : H5. done. auto. 
Qed.


Fixpoint unf_dec e0 e1 :=
match e0,e1 with 
| EEnd,EEnd => true
| EVar n,EVar n' => n == n'
| EMsg d c u e0', EMsg d' c' u' e1' =>  (d == d') && (c == c') && (u == u') && (unf_dec e0' e1')
| ERec n e0', ERec n' e1' =>  if n == n' then unf_dec e0' e1'
                             else unf_dec (ERec n e0') (e1'[s ERec n' e1'])
 ( == d') && (c == c') && (u == u') && (unf_dec e0' e1')


(*Inductive Unravele (r : endpoint -> endpoint -> Prop) : endpoint -> endpoint -> Prop :=
 | UEnde : Unravele r EEnd EEnd
 | UVar n : Unravele r (EVar n) (EVar n)
 | UMsge u g0 g0' d c :  r g0 g0' -> Unravele r (EMsg d c u g0) (EMsg d c u g0')
 | UBranche gs gs' d c : esize gs = esize gs' -> Forall (fun p => r p.1 p.2) (zip gs gs') ->  Unravele r (EBranch d c gs) (EBranch d c gs')
 | URece g g' n : r g[s ERec n g//n] g'  -> Unravele r (ERec n g) g'
 | URece2 g g' n : r g g'[s ERec n g'//n]  -> Unravele r g (ERec n g')
 | Utrans g0 g1 g2 : Unravele r g0 g1 -> Unravele r g1 g2 -> Unravele r g0 g2. (*Should be omitted later, probably not needed*)
Hint Constructors Unravele.
Notation "e0 =( R )= e1" := (Unravele R e0 e1)(at level 60).*)

(*Notation "e =f= e1" := (paco2 Unravele bot2 e e1)(at level 60).*)


(*Notation eq_unf e0 e1 := (is_true (eunf e0 == eunf e1)).*)
(*Lemma ueqe_refl_unf : forall e e' i, bound e' -> e' =f= e' -> e =f= e /\ e[s e'//i] =f= e[s e'//i].
Proof. elim;rewrite/=;rs;intros. rifliad. auto. auto. auto.
rifliad. split. 
pfold. constructor. left. pfold. constructor. left. apply H in H0 as H'.
have : e =f= e /\ (e)[s e' // i] =f= (e)[s e' // i]. apply : H. done. done.
move=>[]. intros.
 apply/Forall_forall. intros. move : H. move/nthP=>Hnth. specialize Hnth with (EEnd,EEnd). destruct Hnth. rewrite -H0. rewrite nth_zip /=. right. apply CIH. done. pfold. constructor. left. pfold. constructor.  right. done. 
Qed.*)

Fixpoint eguarded n g := 
match g with 
| EVar n0 => n0 != n
| ERec n0 g0 => (n == n0) || eguarded n g0
| _ => true
end.

Fixpoint econtractive g := 
match g with 
| ERec n g0 => (eguarded n g0) && (econtractive g0)
| EMsg _ a u g0 => econtractive g0
| EBranch _ a gs => all econtractive gs 
| _ => true 
end.

Lemma ueqe_refl : forall e,  e =f= e.
Proof. 
elim;rewrite /=;intros;try done. by  constructor. by constructor. constructor. done. apply/forallzipP. done. simpl. intros. have : (nth EEnd l x0) \in l. apply/mem_nth. done. move/H. eauto. 
Qed.

Hint Resolve ueqe_refl. 

Lemma ueqe_sym  : forall e0 e1, e0 =f= e1 ->  e1 =f= e0. 
Proof. intros. induction H;auto.  
constructor. done. Admitted.

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
*)

