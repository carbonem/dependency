From mathcomp Require Import all_ssreflect zify finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From Dep Require Import NewSyntax  Utils.
Open Scope fset_scope.
Open Scope fmap_scope.

Coercion ptcps_of_act (a : action) := ptcp_from a |` [fset ptcp_to a].

Definition label := (action * (value + nat))%type.

Coercion to_action (l : label) : action := l.1.


Canonical action_predType := PredType (fun a p => p \in ptcps_of_act a). 

Lemma ptcps_of_act_eq : forall a, ptcps_of_act a = [fset ptcp_from a; ptcp_to a].
Proof. done. Qed.

Lemma in_action_eq : forall p a, p \in ptcps_of_act a = (p == ptcp_from a) ||  (p == ptcp_to a).
Proof. intros. destruct a. by rewrite /= /ptcps_of_act !inE /=.  Qed.

Let inE := (inE,ptcps_of_act_eq,Bool.negb_involutive,eqxx,negb_or,negb_and).
Definition env := {fmap ptcp -> endpoint}.  
Definition fset_ptcp := {fset ptcp}.


(*Module Substitution.

Definition axiom_nop (T : eqType) (substitute : nat -> T -> T ->T) (fv : T -> {fset nat})  :=  forall t t0 i, i \notin fv t -> substitute i t t0 = t.

Definition axiom_fv_subst (T : eqType) (substitute : nat -> T -> T ->T) (fv : T -> {fset nat}) :=  
forall t t0 i, fv (substitute i t t0) = if i \in fv t then fv t `\ i `|` fv t0 else fv t `\i. 

Record mixin_of (T : eqType) := Mixin {substitute : nat -> T -> T -> T; fv : T -> {fset nat};
                                                        _ : axiom_nop substitute fv;
                                                        _ : axiom_fv_subst substitute fv;}.
Notation class_of := mixin_of.

Record type : Type := Pack {sort : eqType; class : class_of sort; }.
End Substitution. 
Coercion Substitution.sort : Substitution.type >-> Equality.type.

Notation substType := Substitution.type.
Definition substitute T := Substitution.substitute (Substitution.class T).
Definition fv T := Substitution.fv (Substitution.class T).
Definition bound (A : substType) (g  : A)  :=  fv g == fset0.
Arguments bound {_}.
Print Substitution.sort.
Arguments substitute {_} _ _ _ : simpl never.
Arguments fv {_} _ : simpl never.

Notation "G [s G0 // X ]" :=  (substitute X G G0)(at level 0, format "G [s  G0  //  X ]").

Lemma subst_nop ( A: substType) : Substitution.axiom_nop (@substitute A) (@fv A). 
Proof.  destruct A. destruct class. done. Qed.

Lemma fv_subst ( A: substType) : Substitution.axiom_fv_subst (@substitute A) (@fv A). 
Proof.  destruct A. destruct class. done. Qed.*)


(*
Module Contractive.

Definition axiom_nop (T : eqType) ( : nat -> T -> T ->T) (fv : T -> {fset nat})  :=  forall t t0 i, i \notin fv t -> substitute i t t0 = t.

Definition axiom_fv_subst (T : eqType) (substitute : nat -> T -> T ->T) (fv : T -> {fset nat}) :=  
forall t t0 i, fv t0 = fset0 -> fv (substitute i t t0) = fv t `\ i . 

Record mixin_of (T : eqType) := Mixin {substitute : nat -> T -> T -> T; fv : T -> {fset nat};
                                                        _ : axiom_nop substitute fv;
                                                        _ : axiom_fv_subst substitute fv;}.
Notation class_of := mixin_of.

Record type : Type := Pack {sort : eqType; class : class_of sort; }.
End Substitution. 
Coercion Substitution.sort : Substitution.type >-> Equality.type.

Notation substType := Substitution.type.
Definition substitute T := Substitution.substitute (Substitution.class T).
Definition fv T := Substitution.fv (Substitution.class T).
Definition bound (A : substType) (g  : A)  :=  fv g == fset0.
Arguments bound {_}.
Print Substitution.sort.
Arguments substitute {_} _ _ _ : simpl never.
Arguments fv {_} _ : simpl never.

Notation "G [s G0 // X ]" :=  (substitute X G G0)(at level 0, format "G [s  G0  //  X ]").
*)

(*Fixpoint eguarded n g := 
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

*)


(*(*From metatheory*)
  Lemma nat_list_max : forall (xs : list nat),
    { n : nat | forall x, x \in xs -> x <=  n }.
  Proof.
    induction xs as [ | x xs [y H] ].
    (* case: nil *)
    exists (0). inversion 1.
    (* case: cons x xs *) 
    exists ((x + y)%nat). intros z J. move : J. rewrite inE. move/orP=>[]. move/eqP=>->. rewrite /=. lia. move/H. lia. 
   Qed.

 Lemma atom_fresh_for_list :
    forall (xs : list nat), { n : nat | ~ n \in xs }.
  Proof.
    intros xs. destruct (nat_list_max xs) as [x H]. exists ( (x.+1)).
    intros J. apply H in J. lia. 
  Qed. 
Definition fresh (S : seq nat) :=
    match atom_fresh_for_list S with
      (exist x _ ) => x
    end.
*)

(*Print predn.



Fixpoint shift (g : gType) := 
match g with
| GMsg a u g0' => GMsg a u (shift g0')
| GBranch a gs => GBranch a (map (fun g0' => shift g0') gs)
| GVar n => GVar (n.+1)
| GRec g0' => GRec (shift g0') 
| GEnd => GEnd
end.



Fixpoint gType_substitution (i : nat) g0 g1  :=
match g0 with
| GMsg a u g0' => GMsg a u (gType_substitution i g0' g1)
| GBranch a gs => GBranch a (map (fun g0' => gType_substitution i g0' g1) gs)
| GVar n => if n == i then g1 else g0
| GRec g0' => GRec (gType_substitution i.+1 g0' (shift g1))
| GEnd => GEnd
end.
*)

Fixpoint ptcps (g : gType) : {fset ptcp} := 
match g with 
| GMsg a _ g0 => a `|`(ptcps g0)
| GBranch a gs => a `|` \bigcup_( i <- map ptcps gs) i
| GRec g0 => ptcps g0
| _ => fset0
end.

Canonical gType_predType := PredType (fun g p => p \in ptcps g). 


Fixpoint gType_fv (g : gType) :=
match g with
| GVar j => [fset j]
| GEnd => fset0
| GMsg _ _ g0 => gType_fv g0
| GBranch _ gs => \bigcup_( i <- map gType_fv gs) i 
| GRec g0 => [fset n.-1 | n in (gType_fv g0) & n != 0]
end. 


Fixpoint endpoint_fv (e : endpoint) :=
match e with
| EVar j => [fset j]
| EEnd => fset0
| EMsg _ _ _ g0 => endpoint_fv g0
| EBranch _ _ gs => \bigcup_( i <- map endpoint_fv gs) i 
| ERec g0 => [fset n.-1 | n in (endpoint_fv g0) & n != 0 ] (*[fset E | x in p & P]*)
end.


(*Lemma gType_axiom_nop : Substitution.axiom_nop subst_gType gType_fv.
Proof. elim;rewrite /=;try done;intros. move : H. rewrite !inE.  rewrite neg_sym. move/negbTE=>->. done. 
f_equal. move : H0. Search _ (_ @` _). rewrite !inE.  move/orP=>[]. rewrite negb_involutive.  move/negbTE.  intros. by  rewrite eq_sym a. rifliad. intros. f_equal. auto. f_equal. 
auto.
f_equal. rewrite big_map in H0.  induction l. done. simpl. f_equal.  apply H.  rewrite !inE.  lia. move : H0. 
rewrite big_cons. rewrite !inE. split_and. apply IHl. intros. apply H. rewrite !inE H1. lia. done. move : H0.  rewrite big_cons !inE. split_and. 
Qed.*)

Lemma big_exists : forall (A : eqType) (B : choiceType) (l : seq A) (f0 : A -> {fset B}) p, p \in \bigcup_(j <- l) (f0 j) = has (fun x => p \in f0 x) l. 
Proof. 
move => A B. elim. move => f0 p. rewrite big_nil. done. intros. simpl. rewrite big_cons !inE. destruct ( (p \in f0 a) ) eqn:Heqn;rewrite /=. 
done.
apply H.
Qed.

Lemma big_f_eq : forall (A : eqType) (B : choiceType)  (l : seq A) (f : A -> {fset B}) f1, (forall g, g \in l -> f g = f1 g) ->  \bigcup_(j <- l) (f j) =  \bigcup_(j <- l) (f1 j).
Proof. move => A B. elim. intros. by rewrite !big_nil.
intros. rewrite !big_cons. f_equal. auto. apply H. auto. 
Qed.

Lemma big_if : forall (A : eqType) (B : choiceType) (l : seq A) (p : pred A) (f : A -> {fset B}) S, 
                  \bigcup_(j <- l) (if p j then f j `|` S else f j) = 
                   (\bigcup_(j <- l) (f j)) `|` (if has p l then S else fset0).
Proof. move => A B. elim. intros. rewrite !big_nil /=. apply/fsetP=>k. by rewrite !inE. 
intros. rewrite !big_cons /= H. rifliad. all : apply/fsetP=>k; rewrite !inE; lia. 
Qed.

Lemma big_cup_in : forall (A : eqType) (B: choiceType) n (l : seq A) (f0 f1 : A -> {fset B}), (forall x n, x \in l -> n \in (f0 x) -> n \in (f1 x)) -> n \in \bigcup_(j <- l) (f0 j) ->  n \in \bigcup_(j <- l) (f1 j).
Proof. move => A B n. elim. move => f0 f1.  rewrite big_nil. done. intros. move : H1. rewrite !big_cons !inE. move/orP=>[].  intros. rewrite H0 //=. intros. erewrite H. lia. intros. apply H0. eauto. eauto. apply b. 
Qed.



(*Lemma gType_axiom_fv_subst : Substitution.axiom_fv_subst gType_substitution gType_fv.
Proof. 
elim;rewrite /=;intros;apply/fsetP=>k;rewrite !inE.
- rifliad. rewrite (eqP H0). move : H.  move=>->. rewrite !inE. lia. 
- rewrite /= !inE. destruct (eqVneq k n). subst. lia. lia. 
- lia.
- rifliad. rewrite /= (eqP H1) !inE. destruct (k != i);rewrite /=. done. done.
- rewrite /= H //= !inE. destruct (k != n);rewrite /=;try lia.  rewrite H //= !inE. done.
- rewrite !big_map. induction l. rewrite !big_nil !inE. lia. 
  rewrite !big_cons !inE H //= !inE. destruct (k != i);rewrite /=. destruct (k \in gType_fv a0) eqn:Heqn; rewrite Heqn //=.
  rewrite /= in IHl. apply IHl. intros. apply H. eauto. done. rewrite /= in IHl. apply IHl. intros. apply H. eauto. done.
Qed.

Definition gType_substMixin := Substitution.Mixin  gType_axiom_nop gType_axiom_fv_subst.
Canonical gType_substType := @Substitution.Pack _ gType_substMixin.*)





Ltac fsetPtac := let k := fresh "k" in apply/fsetP=>k;rewrite ?inE;try lia.

(*Definition axiom_ptcps_subst T (substitute : nat -> T -> T ->T) (fv : T -> {fset nat}) (ptcps : T -> fset_ptcp)  :=  
*)




(*Fixpoint endpoint_substitution (i : nat) g0 g1  :=
match g0 with
| EMsg d a u g0' => EMsg d a u (endpoint_substitution i g0' g1)
| EBranch d a gs => EBranch d a (map (fun g0' => endpoint_substitution i g0' g1) gs)
| EVar n => if n == i then g1 else g0
| ERec n g0' => if n == i then g0 else ERec n (endpoint_substitution i g0' g1)
| EEnd => EEnd
end.

Fixpoint endpoint_fv (g : endpoint) :=
match g with
| EVar j => [fset j]
| EEnd => fset0
| EMsg _ _ _ g0 => endpoint_fv g0
| EBranch _ _ gs => \bigcup_( i <- map endpoint_fv gs) i 
| ERec n g0 => (endpoint_fv g0) `\ n
end.

Lemma endpoint_axiom_nop : Substitution.axiom_nop endpoint_substitution endpoint_fv.
Proof. elim;rewrite /=;try done;intros. move : H. rewrite !inE.  rewrite neg_sym. move/negbTE=>->. done. 
move : H0. rewrite !inE. move/orP=>[]. intros. by  rewrite eq_sym a. rifliad. intros. f_equal. auto. f_equal. 
auto.
f_equal. rewrite big_map in H0.  induction l. done. simpl. f_equal.  apply H.  rewrite !inE.  lia. move : H0. 
rewrite big_cons. rewrite !inE. split_and. apply IHl. intros. apply H. rewrite !inE H1. lia. done. move : H0.  rewrite big_cons !inE. split_and. 
Qed.


Lemma endpoint_axiom_fv_subst : Substitution.axiom_fv_subst endpoint_substitution endpoint_fv.
Proof. 
elim;rewrite /=;intros;apply/fsetP=>k;rewrite !inE.
- rifliad. rewrite (eqP H0). move : H.  move=>->. rewrite !inE. lia. 
- rewrite /= !inE. destruct (eqVneq k n). subst. lia. lia. 
- lia.
- rifliad. rewrite /= (eqP H1) !inE. destruct (k != i);rewrite /=. done. done.
- rewrite /= H //= !inE. destruct (k != n);rewrite /=;try lia.  rewrite H //= !inE. done.
- rewrite !big_map. induction l. rewrite !big_nil !inE. lia. 
  rewrite !big_cons !inE H //= !inE. destruct (k != i);rewrite /=. destruct (k \in endpoint_fv a) eqn:Heqn; rewrite Heqn //=.
  rewrite /= in IHl. apply IHl. intros. apply H. eauto. done. rewrite /= in IHl. apply IHl. intros. apply H. eauto. done.
Qed.

Definition endpoint_substMixin := Substitution.Mixin  endpoint_axiom_nop endpoint_axiom_fv_subst.
Canonical endpoint_substType := @Substitution.Pack _ endpoint_substMixin.



Lemma gType_substitute_substitute : gType_substitution = substitute.  
Proof. done. Qed.

Lemma gType_fv_fv :  gType_fv = fv. done. Qed.

Lemma substitute_gType_substitute : substitute = gType_substitution.
Proof. done. Qed.

Lemma fv_gType_fv :  fv = gType_fv.
Proof. done. Qed.

Lemma endpoint_substitute_substitute : endpoint_substitution = substitute.  
Proof. done. Qed.

Lemma endpoint_fv_fv :  endpoint_fv = fv. done. Qed.

Lemma substitute_endpoint_substitute : substitute = endpoint_substitution.
Proof. done. Qed.

Lemma fv_endpoint_fv :  fv = endpoint_fv.
Proof. done. Qed.

Let unf := (substitute_gType_substitute,fv_gType_fv, substitute_endpoint_substitute,fv_endpoint_fv).
Let fold := (gType_substitute_substitute,gType_fv_fv,endpoint_substitute_substitute,endpoint_fv_fv).
Ltac rs :=  rewrite ?unf /= ?fold.
Ltac rs_in H :=  rewrite ?unf /= ?fold in H.


Lemma ptcps_subst : forall t t0 i, ptcps (t[s t0//i]) = if i \in fv t then ptcps t `|` ptcps t0  else ptcps t. 
Proof. elim;rewrite /=;intros; rewrite /=.
- rifliad. apply/fsetP=>k;rewrite !inE. rewrite /=. rewrite unf in H.  rs. rs_in H. rewrite !inE in H. by rewrite eq_sym H. rs. 
  rs_in H. rewrite !inE in H.  rewrite eq_sym H. by simpl. done. rs. rewrite /=. fsetPtac. rifliad. split_and. lia. 
  split_and. rs.  rewrite !inE H H3 !inE. done. rs. rewrite H. move : H1.  move/andP/andP. rewrite !inE. move/orP=>[].  lia. 
  move/negbTE=>->. done. 
- rs. rewrite H.   rifliad. fsetPtac. 
- rs. rewrite !big_map.
  have :  forall g, g \in l -> ptcps (gType_substitution i g t0) = (if i \in gType_fv g then ptcps g `|` ptcps t0 else ptcps g). auto. move=>HH.

  rewrite (big_f_eq HH) big_if !inE -big_exists. 

  rifliad. rewrite fsetUA. done. rewrite fsetUA. fsetPtac. 
Qed.*)










(*Class SubstType  (A : eqType) := { substitute : nat -> A -> A -> A }.

Instance substtype_gType : SubstType gType_EqType := Build_SubstType substitution.   

Instance substtype_endpoint : SubstType endpoint_EqType := Build_SubstType subst_e.   


Notation "G [g G0 // X ]" :=  (substitution X G G0)(at level 0, format "G [g  G0  //  X ]").

Notation "G [e G0 // X ]" :=  (subst_e X G G0)(at level 0, format "G [e  G0  //  X ]").*)





(*Fixpoint endpoint_substitution (i : nat) e0 e1  :=
match e0 with
| EMsg d a u e0' => EMsg d a u (endpoint_substitution i e0' e1)
| EBranch d a es => EBranch d a (map (fun e0' => endpoint_substitution i e0' e1) es)
| EVar n => if n == i then e1 else e0
| ERec n e0' => if n == i then e0 else ERec n (endpoint_substitution i e0' e1) (*Key insight, consume mu during traversal to make it commute with congruence rules*)
| EEnd => EEnd
end.*)


(*Fixpoint guarded n g := 
match g with 
| GVar n0 => n0 != n
| GRec n0 g0 => (n == n0) || guarded n g0
| _ => true
end.

Fixpoint contractive g := 
match g with 
| GRec n g0 => (guarded n g0) && (contractive g0)
| GMsg a u g0 => contractive g0
| GBranch a gs => all contractive gs 
| _ => true 
end.*)


Fixpoint mu_height g :=
match g with
| GRec g0 => (mu_height g0).+1
| _ => 0
end.

Definition unf g := if g is GRec g' then g' [g g.:var]  else g.

Open Scope fset_scope.
Open Scope fmap_scope.




 

(*Lemma in_ptcp_of_act_f : forall a, (ptcp_from a \in a).
Proof. case. intros. rewrite //=. by  rewrite /ptcps_of_act //= !inE eqxx. Qed.

Lemma in_ptcp_of_act_t : forall a, (ptcp_to a \in ptcps_of_act a).
Proof. case. intros. rewrite //=.  rewrite /ptcps_of_act //= !inE eqxx. lia. Qed.
*)











Notation negb_invol :=  Bool.negb_involutive.






Lemma n_fset0 (n : nat) : [fset n] == fset0 = false.
Proof. destruct (  ([fset n] == fset0)) eqn:Heqn.  move : Heqn. move/eqP/fsetP=>H. have : n \in [fset n] = false. by rewrite H !inE. 
rewrite !inE.  done. done.
Qed.


Fixpoint contractive_i (d : nat) g :=
match g with 
| GEnd => true
| GMsg _ _ g0 => contractive_i 0 g0
| GBranch _ gs => all (contractive_i 0) gs
| GRec g0 => contractive_i (S d) g0
| GVar n => d <= n
end. 

Fixpoint bound_i (i : nat) g  := 
match g with 
| GEnd => true
| GMsg _ _ g0 => bound_i i g0
| GBranch _ gs => all (bound_i i) gs
| GRec g0 => bound_i (S i) g0
| GVar n => n < i
end.

Lemma mu_height_subst : forall g0 i sigma, bound_i i.+1 g0 -> contractive_i i.+1 g0 -> mu_height (g0[g sigma]) = mu_height g0.
Proof. 
elim; try solve [by rewrite /=].
- rewrite /=. intros. lia. 
- intros. simpl. f_equal. apply : H. eauto. eauto. 
Qed.



Lemma bound_lt : forall (g : gType) i j, i < j -> bound_i i g -> bound_i j g.
Proof. 
elim.
- rewrite /=;auto. move=>n i j.  move=> /leP H /ltP H1. apply/ltP.  lia. 
- rewrite /=;auto. intros. apply : (@H i.+1 j.+1); done. 
- rewrite /=;auto. 
- intros. move : (allP H1) => H2. apply/allP.  move=> Hin H4. apply H2 in H4 as H5. apply : (H _ _ _ _ H0).
  done.
- intros. apply (allP H1). done. 
Qed.

Lemma bound_le : forall (g : gType) i j, i <= j -> bound_i i g -> bound_i j g.
Proof. 
intros. destruct (j == i) eqn:Heqn. rewrite (eqP Heqn). done. apply/bound_lt. 2 : {  eauto. } lia.
Qed.

Lemma bound_fv1 : forall g i, bound_i i g -> (forall v, v \in gType_fv g -> v < i).
Proof. 
elim;rewrite /=;intros.
rewrite !inE in H0. rewrite (eqP H0). done.
rewrite !inE in H0. done.
move : H1. move/imfsetP=>[]. simpl. move => x. rewrite !inE. split_and. subst. 
suff : x < i.+1. lia. apply H. done. done.
apply H. done. done.  move : H1. rewrite big_map big_exists. move/hasP=>[]. intros.  apply : H. eauto. 
apply (allP H0).  done. done.
Qed.

Lemma bound_fv2 : forall g i, (forall v, v \in gType_fv g -> v < i) ->  bound_i i g.
Proof.
elim;rewrite /=;intros. apply H. rewrite !inE //=. done.
apply H.  intros. 
destruct (eqVneq v 0).  subst.  done.
suff : v.-1 < i. lia. apply H0. 
apply/imfsetP. exists v. simpl. rewrite !inE /=. split_and. all: try done. 
apply H. auto. apply/allP. intro. intros. apply H.  done.  intros.  apply H0. rewrite big_map big_exists.
apply/hasP. exists x. done.  done. 
Qed.

Lemma bound_fv : forall g i, bound_i i g <-> (forall v, v \in gType_fv g -> v < i).
Proof. 
intros. split;intros.  apply : bound_fv1; eauto. 
apply : bound_fv2; eauto. 
Qed.

(*Lemma fv_ren : forall g sigma v,  v \in gType_fv g ->  sigma v \in gType_fv g ⟨g sigma ⟩. 
Proof.
elim;rewrite /=;intros;try done. 
move : H. rewrite !inE. move/eqP. move=>->. done.
move : H0.  move/imfsetP=>[] x. simpl. rewrite !inE. split_and. subst. 
apply/imfsetP. exists x. simpl. rewrite !inE. split_and.  asimpl. 
destruct x.  done. simpl. *)




(*Lemma bound_i_shift : forall g i,  bound_i i g -> bound_i i.+1 g  ⟨g shift⟩.
Proof.
move => g i.  rewrite !bound_fv. intros.
destruct v.  done. 
suff : v  < i. lia. apply : H. apply : fv_shift. 2 : {  apply : H0. }
intro.  intros. inversion H.  done. 
Qed.
*)
Fixpoint guarded i g := 
match g with
| GVar j => j != i
| GEnd => true
| GMsg _ _ g0 => true
| GBranch _ gs => true
| GRec g0 => guarded i.+1 g0
end. 

Fixpoint contractive2 g := 
match g with
| GVar j => true
| GEnd => true
| GMsg _ _ g0 => contractive2 g0
| GBranch _ gs => all contractive2 gs
| GRec g0 => (guarded 0 g0) && (contractive2 g0)
end. 

(*Print gType_fv.
Open Scope nat_scope.
Fixpoint cont_fv (g : gType) :=
match g with
| GVar j => [fset (j,0)]
| GEnd => fset0
| GMsg _ _ g0 => [fset (n.1,0) | n in (cont_fv g0)]
| GBranch _ gs => [fset (n.1,0)| n in (\bigcup_( i <- map cont_fv gs) i)]
| GRec g0 => [fset ((n.1),(n.2)+1) | n in (cont_fv g0)]
end. *)



Lemma contractive_lt : forall (g : gType) i j, j < i -> contractive_i i g -> contractive_i j g.
Proof.
elim.
- rewrite /=. intros. lia. 
- rewrite /=. done. 
- rewrite /=.  intros. apply : (H i.+1 j.+1). done. done.
- rewrite /=.  intros. done. 
- rewrite /=. intros. done. 
Qed.

Lemma contractive_le : forall (g : gType) i j, j <= i -> contractive_i i g -> contractive_i j g.
Proof.
intros. destruct (j == i) eqn:Heqn. rewrite (eqP Heqn). done. apply/contractive_lt. 2 : {  eauto. } lia.

Qed.




(*Lemma cont_fv_lem1 : forall g i, contractive_i i g -> (forall v, v \in cont_fv g -> v.2 + i <= v.1).
Proof.
elim;simpl;try done;intros;asimpl.
rewrite !inE in H0. move : (eqP H0). destruct v. case. intros.  subst.  simpl . lia.
move : H1.  move/imfsetP=>[] /=x. intros.  destruct v. inversion q. subst. clear q.
simpl. eapply H in H0. 2 : { eauto. } lia. 
move : H1.  move/imfsetP=>[] /=x. intros.  
apply 
destruct v. inversion q. subst. clear H1.
simpl. eapply H in H0. 2 : { eauto. }  lia.
apply H.  apply/contractive_le. 2 :  eauto.  lia. move : H1. 
clear q. 
move => g i.  rewrite !bound_fv. intros.
destruct v.  done. 
suff : v  < i. lia. apply : H. apply : fv_shift. 2 : {  apply : H0. }
intro.  intros. inversion H.  done. 
Qed.*)





(*Lemma bound_subst : forall (g : gType) i sigma, bound_i i.+1 g -> (forall n, n < i.+1 -> bound_i i (sigma n)) ->  bound_i i (g[g sigma]).
Proof. 
elim;rewrite /=;simpl;intros;try done.
apply H0. done. asimpl. apply : H. done. 
intros. destruct n. simpl. done. simpl. apply/bound_i_shift. apply : H1. lia. 
apply H.  done.  done. 
rewrite all_map. apply/allP. intro. intros.  simpl. apply : H. done.  apply (allP H0).  done.
done. 
Qed.

Lemma contractive_ren : forall g j sigma, (forall n, n <= sigma n) ->  contractive_i j g -> contractive_i j g ⟨g sigma ⟩.
Proof.
elim;intros;simpl.
simpl in H0. specialize H with n. lia. done.  asimpl. apply H.  intros. 
destruct n. done. simpl. asimpl. specialize H0 with n. lia.
done. simpl in H1. apply H.  auto. done.
rewrite all_map. apply/allP. intro. intros. simpl. apply H. done. auto. simpl in H1.  apply (allP H1).  done.
Qed.
*)
(*Lemma bound_contractive_subst : forall (g g': gType U) i j, bound_i (S i) g -> contractive_i j g -> bound g' -> (forall j, contractive_i j g') -> 
contractive_i j (substitution i g g').
Proof.
elim. 
- rewrite /=. done.
- rewrite/=. move => v g' i j. case : (eqVneq v i).  done. simpl. done.
- rewrite /=. intros. apply H. done. done. done. done. 
- rewrite /=. intros. apply/allP. move=> gsub Hin. move : (mapP Hin). case. 
intros. subst. apply H. by apply/InP. move : (allP H0). 
move => H4. apply H4 in p. done. move : (allP H1). move => H4. apply H4 in p. done. done. 
  intros. done.
- rewrite /=. intros. 
apply H. done. done. done. done. 
- rewrite /=. intros.  apply/andP. move : (andP H1) (andP H2)=> [] + +[]. intros. split; auto. 
Qed.
*)



(*Lemma contractive2_subst : forall (g : gType) sigma, contractive2 g -> 
(forall n, contractive2 (sigma n) ) -> contractive2 (g[g sigma]).
Proof. 
elim;rewrite /=;simpl;intros;try done.
split_and. asimpl. apply/guarded_subst. done. 
intros.
apply/guarded_shift2.
  destruct n.  done. simpl.  rewrite /funcomp. apply/guarded_shift2.
intros. destruct n0. done. done.


 eapply guarded_shift in H2. move : (@guarded_shift _ _ _ _ H2).  apply/guarded_shift.

apply H2. done. 
asimpl. apply :H.  eauto. eauto. intros. destruct n. done.
rewrite /funcomp. 
apply/bound_i_shift. apply : H2. lia. 
intros.  destruct n.  simpl. done.
simpl. rewrite /funcomp. apply/contractive_ren. auto.  apply H3. 

 edestruct H2.  eauto. 
simpl. 

apply/contractive_ren. auto. 

destruct (j0 == n.+1)eqn:Heqn. 
move : (eqP Heqn)=>HH. subst.c
  admit. lia.
apply : H. eauto.  done.  auto.  auto. 
rewrite all_map. apply/allP. intro. intros. simpl. apply : H.  done.  apply (allP H0). done.
apply (allP H1). done. a*)

(*Lemma contractive_subst : forall (g : gType) i j sigma, bound_i i.+1 g -> contractive_i j g -> 
(forall n, n < i.+1 -> bound_i i (sigma n) ) -> (forall  n j, j <= n -> contractive_i j (sigma n)) ->   contractive_i j (g[g sigma]).
Proof. 
elim;rewrite /=;simpl;intros;try done.
apply H2. done. 
asimpl. apply :H.  eauto. eauto. intros. destruct n. done.
rewrite /funcomp. 
apply/bound_i_shift. apply : H2. lia. 
intros.  destruct n.  simpl. done.
simpl. rewrite /funcomp. apply/contractive_ren. auto.  apply H3. 

 edestruct H2.  eauto. 
simpl. 

apply/contractive_ren. auto. 

destruct (j0 == n.+1)eqn:Heqn. 
move : (eqP Heqn)=>HH. subst.c
  admit. lia.
apply : H. eauto.  done.  auto.  auto. 
rewrite all_map. apply/allP. intro. intros. simpl. apply : H.  done.  apply (allP H0). done.
apply (allP H1). done. auto.  auto. 
Qed.
*)

Notation gt_pred g := (bound_i 0 g && contractive_i 0 g). 




(*Lemma unf_pred : forall (g : gType), gt_pred  g -> gt_pred (unf g).
Proof.
intros. rewrite /unf. destruct g. move : (andP H)=>[];intros.  apply/andP. split. simpl. simpl in a. lia. simpl in *. lia. 
- done.
- simpl in *. split_and. apply/bound_subst. done. intros. destruct n. done. done. destruct (n \notin (fv_g g)) eqn:Heqn.  rewrite subst_nop //=.  move : H0.  rewrite /bound /=. rewrite /=.
  rewrite mem_fsetD1 //=.  apply bound_subst. move : H0. rewrite /bound. simpl. intros. apply/fsetP=>k. rewrite !inE. 
  destruct  (eqVneq k n). subst. have : n \in fv_g g. lia. done. have : false = (k \in fset0).  done. move=>->. move : H0. move/eqP/fsetP=>H0. rewrite -H0. rewrite !inE i /=. done. 
  done. apply contractive_subst.  done. simpl. split_and. done. split_and. split_and. 
Qed.

Lemma iter_pred : forall k (g : gType), gt_pred g -> gt_pred (iter k (fun g => unf g) g).
Proof. elim;rewrite /=;intros. apply/andP.  destruct (andP H). split;auto. 
apply unf_pred. apply H. done. 
Qed.


Lemma mu_height_unf : forall g , gt_pred g -> (mu_height g).-1 = mu_height (unf g).
Proof.
move => g. rewrite /=. elim : g; try solve [intros;rewrite /=;done].
- intros. rewrite /=. split_and. simpl in H1,H2. split_and. rewrite mu_height_subst. done. done. done. 
Qed.


Lemma mu_height_iter_unf : forall k g , gt_pred g -> (mu_height g) - k = (mu_height (iter k (fun g => unf g) g)). 
Proof.
elim;intros. rewrite /=. lia.
rewrite /=. have : mu_height g - n.+1 = (mu_height g - n).-1 by lia. move=>->. 
erewrite H. 2 : {  eauto. } erewrite mu_height_unf. done. apply iter_pred. done. 
Qed.


Lemma iter_unf_not_rec : forall sg k i, gt_pred sg -> mu_height sg <= k -> forall g, iter k (fun g => unf g) sg <> GRec i g.
Proof.
intros. simpl in *. apply (mu_height_iter_unf k) in H. move : H. 
have : mu_height sg - k  = 0 by lia. move=>->. intros. destruct ((iter k (fun g => unf g) sg));try done.
Qed.
*)
Definition full_unf g := (iter (mu_height g) (fun g' => unf g') g).



(*Lemma contractive_subst : forall g sigma j, (forall n, sigma n = var n \/  contractive_i j (sigma n)) ->  contractive_i j g -> contractive_i j g[g sigma].
Proof.
elim;rewrite /=;intros;try done.
edestruct H.  rewrite H1. simpl. lia. eauto. eauto. 
asimpl. apply : H. eauto. intros. destruct n. simpl.  auto. simpl. 
edestruct H0. 
rewrite /funcomp H. asimpl. auto. 
right. 
intros. simpl.  asimpl. apply contractive_ren. auto. auto.  eauto. 
apply : H.   eauto. auto. auto.   
rewrite all_map. apply/allP. intro. intros. simpl. apply/H. done. auto. apply (allP H1).  done.
Qed.*)



(*Lemma bound_notin : forall g n, bound g -> n \notin fv_g g.
Proof. intros. rewrite /bound in H. rewrite (eqP H) !inE. done. Qed.
Lemma bound_guarded : forall g n, bound g  -> guarded n g.
Proof. intros. apply notin_guarded. apply bound_notin. done. Qed.

Lemma guarded_subst : forall g g' n i, guarded n g -> bound g' -> guarded n (g)[g g' // i].
Proof. elim;rewrite /=;intros. rifliad. apply bound_guarded. done. all:auto. 
rifliad. simpl. destruct (orP H0). by rewrite H3.  rewrite H //=. lia.
Qed.*)






(*Lemma contractive_subst : forall (g g': gType) i, (*i \in fv_g g ->*) contractive g -> contractive g' -> bound g' -> contractive (substitution i g g').
Proof.
elim;  (try solve [rewrite /= ;auto]).
- rewrite/=. move => v g' i j. case : (eqVneq v i).  done. simpl. done.
- intros. rewrite /=. rifliad. simpl. split_and. simpl in H1. split_and. apply guarded_subst. simpl in H0. split_and. done.  apply H. simpl in H0. move : H0. split_and. done. done. 
- rewrite /=. intros. move : H0. intros. rewrite all_map. apply/allP=> l' Hin. simpl. apply H;auto.  
  apply (allP H0). done. 
Qed.

Lemma bound_contractive_subst : forall g0 g1 i, fv_g g0 = [fset i] -> bound g1 ->   contractive g0 -> contractive g1 ->  bound (g0[g g1//i]) && contractive (g0[g g1//i]).
Proof.
intros.  split_and. apply bound_subst;auto. apply contractive_subst;auto.  
Qed.*)






(*Endpoint type*)


(*Fixpoint eguarded n g := 
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
end.*)



(*Definition ebound g := efv g == fset0.


Fixpoint emu_height g :=
match g with
| ERec n g0 => (emu_height g0).+1
| _ => 0
end.

Definition eunf g := if g is ERec n g' then (subst_e n g' g) else g.


Lemma emu_height_subst : forall g0 g1  i, eguarded i g0 -> econtractive g0 -> emu_height (g0[e g1//i]) = emu_height g0.
Proof. 
elim; try solve [by rewrite /=].
- rewrite /=. intros. split_and. rewrite (negbTE H). done. 
- intros. simpl. simpl in H0. split_and. destruct (i == n) eqn:Heqn.  rewrite eq_sym Heqn. done.  
  simpl in H1. rifliad. split_and. simpl. f_equal. apply H.  done. done. 
Qed.


Lemma fsubset_in : forall (A : choiceType) (b c : {fset A}), b `<=` c -> (forall j, j \in b -> j \in c).
Proof.
intros. Search _ fsub1set. move : H0. rewrite -!fsub1set.  intros. apply : fsubset_trans. apply : H0. apply H. 
Qed.*)

(*Lemma efv_subst : forall g g0 n, efv g0 `<=` efv g  -> efv (g[e g0 // n]) = efv g `\ n. 
Proof. 
elim;rewrite /=;intros;apply/fsetP=>k;rewrite !inE.
- rifliad. rewrite (eqP H0). move : H.  move/fsubset_in =>HH. rewrite -(eqP H0). specialize HH with k. rewrite !inE in HH. 
destruct (k \in efv g0). destruct (eqVneq k n). specialize HH with k. rewrite -HH. move/fsubset_ rewrite /bound. move/eqP=>->. rewrite !inE. by destruct (eqVneq k n0).
- rewrite /= !inE. destruct (eqVneq k n). subst. lia. lia. 
- lia.
- rifliad. rewrite /= (eqP H1) !inE. destruct (k != n0);rewrite /=. done. done.
- rewrite /= H //= !inE. destruct (k != n);rewrite /=;try lia.  rewrite H //= !inE. done.
- rewrite !big_map. induction l. rewrite !big_nil !inE. lia. 
  rewrite !big_cons !inE H //= !inE. destruct (k != n);rewrite /=. destruct (k \in efv a) eqn:Heqn;rewrite Heqn //=.
  rewrite /= in IHl. apply IHl. intros. apply H. eauto. done. rewrite /= in IHl. apply IHl. intros. apply H. eauto. done.
Qed.*)

(*Lemma efv_subst : forall g g0 n, ebound g0 -> efv (g[e g0 // n]) = efv g `\ n. 
Proof. 
elim;rewrite /=;intros;apply/fsetP=>k;rewrite !inE.
- rifliad. rewrite (eqP H0). move : H.  rewrite /bound. move/eqP=>->. rewrite !inE. by destruct (eqVneq k n0).
- rewrite /= !inE. destruct (eqVneq k n). subst. lia. lia. 
- lia.
- rifliad. rewrite /= (eqP H1) !inE. destruct (k != n0);rewrite /=. done. done.
- rewrite /= H //= !inE. destruct (k != n);rewrite /=;try lia.  rewrite H //= !inE. done.
- rewrite !big_map. induction l. rewrite !big_nil !inE. lia. 
  rewrite !big_cons !inE H //= !inE. destruct (k != n);rewrite /=. destruct (k \in efv a) eqn:Heqn;rewrite Heqn //=.
  rewrite /= in IHl. apply IHl. intros. apply H. eauto. done. rewrite /= in IHl. apply IHl. intros. apply H. eauto. done.
Qed.


Lemma ebound_subst : forall g g' i, efv g = [fset i] -> ebound g' -> ebound (subst_e i g g').
Proof. intros. move : H0. rewrite /ebound. move/eqP=>HH. rewrite -HH. apply/eqP.  rewrite efv_subst. rewrite H HH. apply/fsetP=>k. rewrite !inE. destruct (eqVneq k i);done.  rewrite /ebound. by apply/eqP.
Qed.

Lemma notin_eguarded : forall g n, n \notin efv g  -> eguarded n g.
Proof. elim;rewrite /ebound //=;intros. move : H. rewrite !inE. lia. move : H0. rewrite !inE. move/orP=>[]. lia. intros.  
rewrite H //=. lia. 
Qed.

Lemma ebound_notin : forall g n, ebound g -> n \notin efv g.
Proof. intros. rewrite /ebound in H. rewrite (eqP H) !inE. done. Qed.
Lemma ebound_eguarded : forall g n, ebound g  -> eguarded n g.
Proof. intros. apply notin_eguarded. apply ebound_notin. done. Qed.

Lemma eguarded_subst : forall g g' n i, eguarded n g -> ebound g' -> eguarded n (g)[e g' // i].
Proof. elim;rewrite /=;intros. rifliad. apply ebound_eguarded. done. all:auto. 

rifliad. simpl. destruct (orP H0). by rewrite H3.  rewrite H //=. lia.
Qed.



Lemma econtractive_subst : forall g g' i, (*i \in efv g ->*) econtractive g -> econtractive g' -> ebound g' -> econtractive (subst_e i g g').
Proof.
elim;  (try solve [rewrite /= ;auto]).
- rewrite/=. move => v g' i j. case : (eqVneq v i).  done. simpl. done.
- intros. rewrite /=. rifliad. simpl. split_and. simpl in H1. split_and. apply eguarded_subst. simpl in H0. split_and. done.  apply H. simpl in H0. move : H0. split_and. done. done. 
- rewrite /=. intros. move : H0. intros. rewrite all_map. apply/allP=> l' Hin. simpl. apply H;auto.  
  apply (allP H0). done. 
Qed.

Lemma ebound_econtractive_subst : forall g0 g1 i, efv g0 = [fset i] -> ebound g1 ->   econtractive g0 -> econtractive g1 ->  ebound (g0[e g1//i]) && econtractive (g0[e g1//i]).
Proof.
intros.  split_and. apply ebound_subst;auto. apply econtractive_subst;auto.  
Qed.


Notation e_pred g := (ebound g && econtractive g). 


Lemma subst_e_nop : forall g g' x, x \notin (efv g) -> subst_e x g g' = g. 
Proof. 
elim;rewrite /=;try done;intros. move : H. rewrite !inE.  rewrite neg_sym. move/negbTE=>->. done. 
move : H0. rewrite !inE.  move/orP=>[]. intros. by  rewrite eq_sym a. rifliad. intros. f_equal. auto. f_equal. 
auto.
f_equal. rewrite big_map in H0.  induction l. done. simpl. f_equal.  apply H.  rewrite !inE.  lia. move : H0. 
rewrite big_cons. rewrite !inE. split_and. apply IHl. intros. apply H. rewrite !inE H1. lia. done. move : H0.  rewrite big_cons !inE. split_and. 
Qed.

Lemma eunf_pred : forall g , e_pred  g -> e_pred (eunf g).
Proof.
intros. rewrite /eunf. destruct g. move : (andP H)=>[];intros.  apply/andP. split. simpl. simpl in a. lia. simpl in *. lia. 
- done.
- simpl in *. split_and. done. destruct (n \notin (efv g)) eqn:Heqn.  rewrite subst_e_nop //=.  move : H.  rewrite /ebound /=. rewrite /=.
  rewrite mem_fsetD1 //=.  split_and. Check ebound_subst. split_and. apply ebound_subst. move : H0. rewrite /ebound. simpl. intros. apply/fsetP=>k. rewrite !inE. 
  destruct  (eqVneq k n). subst. have : n \in efv g. lia. done. have : false = (k \in fset0).  done. move=>->. move : H0. move/eqP/fsetP=>H0. rewrite -H0. rewrite !inE i /=. done. 
  done. apply econtractive_subst.  simpl in H1. split_and. done. done. 
Qed.
Check iter.
Lemma eiter_pred : forall k e,  e_pred e -> e_pred (iter k (fun g => eunf g) e).
Proof. elim;rewrite /=;intros. apply/andP.  destruct (andP H). split;auto. 
apply eunf_pred. apply H. done. 
Qed.


Lemma emu_height_eunf : forall g , e_pred g -> (emu_height g).-1 = emu_height (eunf g).
Proof.
move => g. rewrite /=. elim : g; try solve [intros;rewrite /=;done].
- intros. rewrite /=. split_and. simpl in H1,H2. split_and. rewrite emu_height_subst. done. done. done. 
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









Lemma in_foldr : forall l n,  n \in foldr (fun g' : gType => cat (fv_g g')) nil l ->  exists g, g \in l /\ n \in (fv_g g).
Proof. elim;try done;move => l n H n'.
rewrite /= mem_cat. move/orP=>[]. intros. exists l. rewrite !inE /= a. auto.
move/H. move=>[] x [].  intros. exists x. rewrite !inE a b. lia. Qed.

(*Lemma in_foldr2 : forall l n p g, g \in l -> n \in (efv (project  g p)) ->  n \in foldr (fun g' : gType => cat (efv (project g' p))) nil l.
Proof. elim;try done;intros. move : H0.
rewrite !inE. move/orP=>[]. move/eqP. intros. subst. simpl. rewrite mem_cat H1. done. intros.  simpl. rewrite mem_cat. apply/orP. right. apply : H. eauto. done. 
Qed.*)


(*
Lemma fv_project_in : forall g p n, lpreds rec_pred g ->  (n \in (fv_g g)) -> (n  \in (efv (project g p))).
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

Lemma fv_project_eq : forall g p n, lpreds rec_pred g ->  (n \in fv_g g) = (n \in efv (project g p)).
Proof. intros. destruct ( (n \in fv_g g)) eqn:Heqn. rewrite fv_project_in //=.
destruct ((n \in efv (project g p))) eqn:Heqn2. erewrite fv_rproject_in in Heqn. done. eauto. done. 
Qed.*)



Lemma fv_g_unf : forall g g0 n, bound g0 -> fv_g (g[g g0 // n]) = fv_g g `\ n. 
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


Fixpoint act_of g :=
match g  with 
| EMsg _ a _ _ => Some a
| EBranch _ a _ => Some a
| ERec g0 => act_of g0 
| _ => None
end.

Fixpoint next_aux sigma e :=
match e with 
| EMsg _ _ _ e0 => [::e0[e sigma]]
| EBranch _ _ es => map (fun e => e[e sigma]) es
| ERec e0 => next_aux (e.:sigma) e0
| EVar n => [::sigma n ]
| EEnd => nil
end.

Definition next e := next_aux ids e.
(*Parameter (c : ch).
Definition g' := (ERec (EBranch Sd c ([::EVar 0;EVar 1]))).
Definition g := (ERec g'). 

Lemma test : (next_aux ids g) = [::g';g]. done. Qed.
*)


Inductive bisimilar_f (r : endpoint -> endpoint -> Prop) : endpoint -> endpoint -> Prop :=
 BF e0 e1 : act_of e0 = act_of e1 -> size (next e0) = size (next e1) -> Forall (fun p => r p.1 p.2) (zip (next e0) (next e1)) ->  bisimilar_f r e0 e1.

Require Import Paco.paco.
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
| ERec  e0 => (esize e0).+1
| _ => 1
end.

Fixpoint bisim_dec e0 e1 := bisim_dec_aux ((esize e0) * (esize e1)) nil e0 e1.

Lemma bisimP : forall e0 e1, reflect (bisimilar e0 e1) (bisim_dec e0 e1). 
Proof. Admitted.
Lemma bisimP2 : forall e0 e1 R S, (forall e0 e1, R e0 e1 <-> (e0,e1) \in S ) -> exists n,  (bisimilar_f R e0 e1) <-> (bisim_dec_aux n S e0 e1). 
Proof. Admitted. 


Fixpoint l_to_sig l := if l is x::l' then x.:(l_to_sig l') else ids.

Fixpoint gunf l g := 
match g with 
| GRec g0 => gunf (g::l) g0
| _ => g[g l_to_sig l]
end.



Definition act_ofg_aux g :=
match g  with 
| GMsg a u _ => Some (inl (a,Some u))
| GBranch a _ => Some (inl (a,None))
| GVar n => Some (inr n)
| _ => None
end.

Definition act_ofg g := act_ofg_aux (full_unf g).


Definition nextg_aux g :=
match g with 
| GMsg _ _ g0 => [::g0]
| GBranch  _ es => es
| _ => nil
end.

Definition nextg g := nextg_aux (full_unf g).



(*Parameter (c : ch).
Definition g' := (ERec (EBranch Sd c ([::EVar 0;EVar 1]))).
Definition g := (ERec g'). 

Lemma test : (next_aux ids g) = [::g';g]. done. Qed.
*)


Inductive bisimilar_fg (r : gType-> gType -> Prop) : gType -> gType -> Prop :=
 BFr e0 e1 : act_ofg e0 = act_ofg e1 -> size (nextg e0) = size (nextg e1) -> Forall (fun p => r p.1 p.2) (zip (nextg e0) (nextg e1)) ->  bisimilar_fg r e0 e1.


Lemma mono_bisimg : monotone2 bisimilar_fg.
Proof.
move => x. intros. induction IN. constructor. done. done.
apply/forallzipP. done. intros. move : H1. move/forallzipP=>Hzip. 
simpl in Hzip.  simpl. apply LE. apply : Hzip. done. done. 
Grab Existential Variables. all : repeat constructor.
Qed. 

Hint Resolve mono_bisimg : paco.

Definition bisimilarg e0 e1  : Prop := paco2 bisimilar_fg bot2 e0 e1.

Fixpoint bisim_decg_aux n S e0 e1 :=
if n is n'.+1 then ((e0,e1) \in S) || (act_ofg e0 == act_ofg e1) && (size (nextg e0) == size (nextg e1)) && 
all (fun p => bisim_decg_aux n' ((e0,e1)::S) p.1 p.2) (zip (nextg e0) (nextg e1))
else (e0,e1) \in S.
Open Scope nat_scope.

Fixpoint gsize e := 
match e with 
| GMsg  _ _ e0 => (gsize e0).+1
| GBranch _ es => foldr (fun e0 acc => (gsize e0) + acc ) 0 es
| GRec  e0 => (gsize e0).+1
| _ => 1
end.

Fixpoint bisim_decg e0 e1 := bisim_decg_aux ((gsize e0) * (gsize e1)) nil e0 e1.

Lemma bisimPg : forall e0 e1, reflect (bisimilarg e0 e1) (bisim_decg e0 e1). 
Proof. Admitted.
Lemma bisimP2g : forall e0 e1 R S, (forall e0 e1, R e0 e1 <-> (e0,e1) \in S ) -> exists n,  (bisimilar_fg R e0 e1) <-> (bisim_decg_aux n S e0 e1). 
Proof. Admitted. 

