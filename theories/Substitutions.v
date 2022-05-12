From mathcomp Require Import all_ssreflect zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From Dep Require Import Global_Syntax Inductive_Linearity.


Lemma contractive_lt : forall (g : gType) i j, j < i -> contractive_i i g -> contractive_i j g.
Proof.
elim;auto.
- rewrite /=. move => n i j. move/ltP=> + /leP;intros.  apply/leP. lia. 
- move => g H.  rewrite /=. intros. have : j.+1 < i.+1. apply/ltP. move : H0. move/ltP. lia. eauto. 
Qed.

Lemma contractive_le : forall (g : gType) i j, j <= i -> contractive_i i g -> contractive_i j g.
Proof.
intros. destruct (eqVneq j i). subst. done. 
have : j < i by lia. intros. eauto using contractive_lt.
Qed.



Lemma mu_height_subst : forall g0 g1  i, contractive_i (S i) g0 -> mu_height (substitution i g0 g1) = mu_height g0.
Proof. 
elim; try solve [by rewrite /=].
- rewrite /=. intros. case : (eqVneq n i) H. move=>->. by rewrite ltnn. by rewrite /=. 
- intros. rewrite /=. f_equal. apply H. done. 
Qed.




Lemma bound_lt : forall (g : gType) i j, i < j -> bound_i i g -> bound_i j g.
Proof. 
elim.
- rewrite /=;auto. move=>n i j.  move=> /leP H /ltP H1. apply/ltP.  lia. 
- rewrite /=;auto. intros. apply : (@H i.+1 j.+1); done. 
- rewrite /=;auto. 
- intros. move : H1. rewrite /=.  move/allP=>H2. apply/allP. move=> l' Hin. move : (H2 l' Hin). 
  apply H;auto. 
Qed.

Lemma bound_le : forall (g : gType) i j, i <= j -> bound_i i g -> bound_i j g.
Proof. intros. destruct (eqVneq i j). by subst. have : i < j by lia. 
eauto using bound_lt.
Qed.

Lemma bound_0 : forall (g : gType) j, bound g -> bound_i j g.
Proof.
intros. case : j. done. intros. apply  : (@bound_lt _ 0). done. done.
Qed.
Check max.

Lemma subst_none : forall (g g': gType) i j, i <= j -> (bound_i i g) -> (substitution j g g') = g.   
Proof.
elim; intros;rewrite /=;try done.
-  rifliad.  simpl in H0.  lia.
- f_equal. apply : H. have : i.+1 <= j.+1 by lia. intros. apply : x. done.
- rewrite (H g' i j) //=.
- f_equal. elim : l H H1. done.
  intros. rewrite /=. f_equal. apply  : H1. by rewrite inE eqxx. apply : H0. simpl in H2. apply (andP H2). apply H.
  intros.  apply : H1. by rewrite inE H3 orbC. apply : H4. done. simpl in *. apply (andP H2). 
Qed.


Lemma bound_subst : forall (g g': gType) i j, bound_i i.+1 g -> bound_i j g' -> bound_i (i + j) (substitution i g g').
Proof.
elim.
-  rewrite /=. intros. rifliad. move : H0. rewrite -(eqP H1). intros. apply : bound_le. 2: { apply : H0. }  lia. 
  have : n < i by lia. intros. rewrite /bound_i. lia.
- rewrite /=. done. 
- rewrite /=. intros. have : (i + j).+1 = (i.+1 + j) by lia. move=>->. apply H. done. done.
- rewrite /=. intros. auto. 
- rewrite /=. intros. move : (allP H0)=> H2. apply/allP. move => l' /mapP. case. intros. 
  subst. apply H;auto.
Qed.

Lemma bound_subst2 : forall (g g': gType) i j, j <= i -> bound_i i.+1 g -> bound_i j g' -> bound_i i (substitution i g g').
Proof.
elim.
-  rewrite /=. intros. rifliad. apply : bound_le. 2 : { eauto. } lia. simpl. lia. 
- done. 
- intros. simpl. apply : H. 3: {  eauto. } lia. done. 
- rewrite /=. intros. auto. 
- rewrite /=. eauto. 
- intros. simpl in *. move : (allP H1)=> HH2. apply/allP. move => l' /mapP. case. intros. 
  subst. eauto. 
Qed.

Lemma bound_contractive_subst : forall (g g': gType) i i2 j, bound_i i.+1 g -> contractive_i j g -> bound_i i2 g' -> (forall j, contractive_i j g') -> 
contractive_i j (substitution i g g').
Proof.
elim.  (try solve [rewrite /= ;auto]).
- rewrite/=. move => v g' i j. case : (eqVneq v i).  done. simpl. done.
- rewrite /=. intros. done. 
- rewrite /=. intros. apply : H. done. done. apply : H2. apply : H3. 
- rewrite /=.  intros. apply : H;eauto. 
- rewrite /=. intros. apply/allP. move=> gsub /mapP. case. intros. subst. 
  apply : H;eauto. auto using (allP H0), (allP H1). auto using (allP H1). 
Qed.

Lemma bound_cont_eq : forall (g : gType) i, bound_i i g -> contractive_i i g -> (forall j, contractive_i j g).
Proof.
elim; rewrite/=;auto.
- rewrite /=. move => v i /ltP + /leP. lia. 
- rewrite /=. intros. eauto. 
Qed.

Lemma subst_mixin : forall g0 g1 n, gt_pred n.+1 n.+1  g0 -> gt_pred n n g1 -> gt_pred n n (substitution n g0 g1).
Proof.
intros.  move : (andP H)=>[]. move : (andP H0)=>[]. intros. apply/andP. split.
apply : bound_subst2. 3 : { eauto. } lia. eauto. 
apply : bound_contractive_subst;eauto. 
apply : contractive_lt. 2 : { eauto. } lia. apply : bound_cont_eq. 
eauto. eauto. 
Defined.


Lemma unf_mixin : forall (g : gType) (n : nat), gt_pred n n g -> gt_pred n n (unf g n).
Proof.
intros. rewrite /unf. destruct g. move : (andP H)=>[];intros.  apply/andP. split. simpl. simpl in a. lia. simpl in *. lia. 
- done.
- simpl in *. apply subst_mixin.  done. done. 
  move : (andP H)=>[];intros. apply/andP. split. apply : bound_le. 2 : { eauto. } lia. done. 
- simpl in *. move : (andP H)=>[];intros. apply/andP. split. 
  apply/allP. move=> l' Hin. apply : bound_le. 2 : {  apply (allP a0).  done. } lia. done.
Qed.

Lemma iter_mixin : forall k (g : gType) (n : nat), gt_pred n n g -> gt_pred n n (iter k (fun g => unf g n) g).
Proof. elim;rewrite /=;intros. apply/andP.  destruct (andP H). split;auto. 
apply unf_mixin. apply H. done. 
Qed.


Lemma mu_height_unf : forall n g k, k <= n -> gt_pred n n g -> (mu_height g).-1 = mu_height (unf g k).
Proof.
move => n  g. rewrite /=. elim : g n; try solve [intros;rewrite /=;done].
- intros. rewrite /=. have : k <= n.+1 by lia.  intros. apply H in x;auto. rewrite mu_height_subst. done.
  apply : contractive_le. 2 : { apply (andP H1). } lia. 
Qed.


Lemma mu_height_iter_unf : forall k n g , gt_pred n n g -> (mu_height g) - k = (mu_height (iter k (fun g => unf g n) g)). 
Proof.
elim;intros. rewrite /=. lia.
rewrite /=. have : mu_height g - n.+1 = (mu_height g - n).-1 by lia. move=>->. 
erewrite H. 2 : {  eauto. } erewrite mu_height_unf. done. 2 : { apply iter_mixin. done. } lia.
Qed.


Lemma iter_unf_not_rec : forall n sg k, gt_pred n n sg -> mu_height sg <= k -> forall g, iter k (fun g => unf g n) sg <> GRec g.
Proof.
intros. simpl in *. apply (mu_height_iter_unf k) in H. move : H. 
have : mu_height sg - k  = 0 by lia. move=>->. intros. destruct ((iter k (fun g => unf g n) sg));try done.
Qed.

Notation full_unf n g := (iter (mu_height g) (fun g' => unf g' n) g).


(*Section SubgType.
Variable n : nat.

Inductive subgType : Type := SubgType g of bound_i n g && contractive_i n g.

Coercion gType_of_subgType sg := let: @SubgType g _  := sg in g.

Canonical subgType_subType := [subType for gType_of_subgType].
Definition subgType_eqMixin := Eval hnf in [eqMixin of subgType by <:].
Canonical subgType_eqType := Eval hnf in EqType subgType subgType_eqMixin.

Check subgType_ind.

Lemma SGEnd_mixin : gt_pred n n GEnd.
Proof. done. Qed.

Definition SGEnd := SubgType SGEnd_mixin.



Lemma SGMsg_mixin : forall a u g, gt_pred n n g -> gt_pred n n (GMsg a u g).
Proof. intros. rewrite /=.  move : (andP H)=>[]-> /=. eauto using contractive_le.
Defined.

Definition SGMsg a u (g : subgType) := SubgType (SGMsg_mixin a u (valP g)).


Lemma SGBranch_mixin : forall a gs, all (gt_pred n n) gs -> gt_pred n n (GBranch a gs).
Proof.
move => a gs. intros. have : all (bound_i n) gs && (all (contractive_i n) gs). 
move : H. elim : gs. done. intros. rewrite /=.  simpl in H0. move : H0. move/andP=>[] /andP. move=>[]. intros. rewrite a1 b /=. auto.
move/andP=>[].  intros. rewrite /= a0 /=.  apply/allP. move=> x Hin.  apply : contractive_le. 2: { apply (allP b). done. } lia. 
Defined.

Lemma seq_sub : forall (gs : seq subgType), all (gt_pred n n) (map val gs).
Proof. elim.  done. intros. simpl. destruct a. rewrite /= i /=. done.
Qed.

Definition SGBranch  a (gs : seq subgType) := SubgType (SGBranch_mixin a (seq_sub gs)). 


Lemma SGRec_mixin : forall g, gt_pred n.+1 n.+1 g ->  gt_pred n n (GRec g).
Proof.
intros. rewrite /=. done.
Defined.
End SubgType.

Definition SGRec n (g : subgType n.+1) := SubgType (@SGRec_mixin n g (valP g)).

Lemma full_unf_sub : forall n (g : subgType n) g', (full_unf n g) <> GRec g'.
Proof.
intros. apply iter_unf_not_rec. destruct g. simpl in *. done. lia.
Qed.*)
