From mathcomp Require Import all_ssreflect zify finmap.
Require Import Paco.paco.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From Dep Require Import NewSyntax  Utils.


Lemma injective_shift : injective S.
Proof. intro. intros. inversion H.  done. Qed.

Hint Resolve injective_shift.




Lemma inject2 : forall sigma, injective sigma ->  injective (0 .: sigma >> succn).
Proof. 
intros. intro. intros. destruct x1;destruct x2;try done. inversion H0. f_equal. apply/H. done. 
Qed.

Lemma inject_comp : forall (A B C : Type) (sigma : A -> B) (sigma' : B -> C) , injective sigma -> injective sigma' -> injective (sigma >> sigma').  
Proof. 
intros. rewrite /funcomp. intro. intros. apply H. apply H0. done.
Qed.


Hint Resolve inject2.

Lemma guarded_ren : forall g sigma i , (forall n, sigma n != i) -> guarded i g -> guarded i g ⟨g sigma⟩.
Proof.
elim;rewrite /=;simpl;intros;try done.
asimpl. apply : H. intros. destruct n.  done. simpl. specialize H0 with n. rewrite /funcomp. lia.
done. 
Qed.

Lemma guarded_shift1 : forall g i sigma, injective sigma ->  guarded i g -> guarded (sigma i) g ⟨g sigma⟩.
Proof.
elim;rewrite /=;simpl;intros;try done.
apply/eqP. move=> HH. apply H in HH. lia. 
asimpl. 
have : (sigma i).+1 = ((0 .: sigma >> succn) i.+1).
destruct i.  simpl. rewrite /funcomp. done. simpl. rewrite /funcomp. done.
move=>->. apply H. intro. intros. destruct x1;destruct x2;try done. inversion H2. f_equal.  apply/H0. done. 
done. 
Qed.



Lemma guarded_shift2 : forall g i sigma, injective sigma ->  guarded (sigma i) g ⟨g sigma⟩ ->  guarded i g.
Proof.
elim;rewrite /=;simpl;intros;try done.
apply/eqP. move=> HH. apply (negP H0). apply/eqP. f_equal. done. 
apply :H.  2 : { apply : H1.  } 
asimpl. auto. 
Qed.


Lemma guarded_shift : forall g sigma i , injective sigma  -> guarded i g <-> guarded (sigma i) g ⟨g sigma⟩.

intros. split;intros; eauto using guarded_shift1, guarded_shift2.
Qed.


Lemma contractive2_ren : forall g sigma, injective sigma -> (forall n, n <= sigma n) ->  contractive2  g -> contractive2 g ⟨g sigma ⟩.
Proof.
elim;intros;simpl;try done. 
asimpl. split_and. have : 0 = ( 0 .: sigma >> succn) 0. done. intros. rewrite {1}x.

rewrite -guarded_shift. simpl in H2. split_and. auto.
apply H. auto.  case. done. done.  simpl in H2. split_and. apply H.  done. done. done.
rewrite all_map. apply/allP. intro. intros. simpl. apply H. done.  done. done.  simpl in H2. apply (allP H2). done.
Qed.



Lemma guarded_sig2_ren : forall g sigma sigma' i, guarded i g ⟨g sigma⟩ -> (forall n, (sigma n) != i ->  (sigma' n) != i) -> guarded i g ⟨g sigma'⟩.
Proof.
elim;rewrite /=;intros;try done.
apply H0. done.
asimpl. apply : H. eauto. move => n.  asimpl. simpl. intros. destruct n. done. simpl in *. 
move : H. rewrite /funcomp. intros. suff :  sigma' n != i.  lia. apply : H1. lia. 
Qed.

Lemma guarded_sig2 : forall g sigma sigma' i, guarded i g [g sigma] -> (forall n, guarded i (sigma n) -> guarded i (sigma' n)) -> guarded i g [g sigma'].
Proof.
elim;rewrite /=;intros;try done.
apply H0. done.
asimpl. apply : H. eauto. move => n.  asimpl. simpl. intros. destruct n. done. simpl in *.
move : H. rewrite /funcomp. specialize H1 with n. move : H0. asimpl.
intros. rewrite -guarded_shift. move : H. rewrite -guarded_shift.  move/H1. done. 
done. done. 
Qed.


Lemma guarded_fv : forall g v, v \notin gType_fv g -> guarded v g.
Proof.
elim;rewrite /=;try done;intros.
rewrite !inE in H. lia.
apply H. move : H0. move/imfsetP=>HH. apply/negP=>HH'. apply HH. simpl. exists v.+1;try done.  
rewrite !inE. split_and.
Qed.

Lemma inotin : forall g i sigma, (forall n, i !=  sigma n) -> i \notin gType_fv g ⟨g sigma ⟩.
Proof.
elim;rewrite /=;try done;intros. rewrite !inE. specialize H with n. lia.
apply/imfsetP=>/=H'. destruct H'. rewrite !inE in H1.  destruct (andP H1). move : H3. asimpl. intros. apply/negP. apply : H. 2 : { apply : H3. } case. simpl. done. simpl. intros. asimpl. destruct x.  done. suff : x != sigma n. lia. 
specialize H0 with n.  simpl in H2. subst. done. 
rewrite !big_map big_exists. apply/negP. move/hasP=>HH. destruct HH. apply/negP. apply : H. eauto.
2 : {  apply : H2. } auto.
Qed.

Lemma contractive2_subst : forall g sigma,contractive2 g -> (forall n, contractive2 (sigma n)) -> contractive2 g [g sigma].
Proof. 
elim;rewrite /=;intros;try done. 
asimpl. split_and. 
apply/guarded_sig2.
instantiate (1 := (var 0 .: var >>  ⟨g ↑ ⟩)).  asimpl. done.
case. done. simpl. intros. apply/guarded_fv. asimpl. apply/inotin. done.
apply H. done.  intros. destruct n.  done. simpl. asimpl.  apply/contractive2_ren. done. done. done.
apply H. done.  intros. done. 
rewrite all_map. apply/allP. intro. intros. simpl. apply H. done. apply (allP H0). done. done.
Qed.



Lemma mu_height_ren : forall g sigma, mu_height g ⟨g sigma ⟩  = mu_height g.
Proof.
elim;rewrite /=;try done;intros.
f_equal. apply : H. 
Qed.



Lemma mu_height_subst : forall g0 sigma i,  guarded  i g0 -> (forall n, n != i -> mu_height (sigma n) = 0) -> contractive2 g0 -> mu_height (g0[g sigma]) = mu_height g0.
Proof. 
elim; try solve [by rewrite /=];intros.
- asimpl. simpl in H. rewrite H0. done. apply : H. 
simpl. f_equal. asimpl. apply H with (i:=i.+1). 2 : { intros. destruct n. simpl. done. simpl. asimpl.
rewrite mu_height_ren. apply H1. lia.  } intros. apply : H0. eauto. simpl in H2. split_and.
Qed. 



