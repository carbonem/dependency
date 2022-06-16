From mathcomp Require Import all_ssreflect finmap zify.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Locate Forall.

Notation In := List.In.
Notation Forall := List.Forall.


Lemma In_in : forall (A : eqType) (a : A) l, In a l <-> a \in l.
Proof.
move => A a. elim. split;done.
intros. rewrite /= inE. split. case. move=>->. rewrite eqxx. done. move/H. move=>->. by rewrite orbC. 
move/orP. case. move/eqP. move=>->. auto. move/H. auto. 
Qed.

Lemma Forall_forall
     : forall (A : eqType) (P : A -> Prop) (l : seq A), Forall P l <-> (forall x : A, x \in l -> P x).
Proof. intros. rewrite List.Forall_forall. split;intros;auto;by apply/H/In_in. Qed.

Lemma nat_fact : forall n, n - (n - n) = n. lia. Qed.

Lemma forallzipP1 : forall (A B : eqType) (P : A * B -> Prop) a b l l',  size l = size l' -> (forall x0, x0 < size l -> P (nth a l x0,nth b l' x0)) -> 
Forall P (zip l l').
Proof.
intros. apply/Forall_forall. intros. move : H1. move/nthP=>HH. specialize HH with (a,b). 
destruct HH. rewrite -H2. rewrite nth_zip //=. apply H0. move : H1. by rewrite size_zip minnE H nat_fact. 
Qed.


Lemma forallzipP2 : forall (A B : eqType) (P : A * B -> Prop) a b l l', Forall P (zip l l') -> size l = size l' -> (forall x0, x0 < size l -> P (nth a l x0,nth b l' x0)).
Proof.
move => A B P a b. elim. case. done. done. move => a0 l IH. case. done. move => a1 l0 H Hsize. intros. simpl in H0. destruct x0. simpl. simpl in H. inversion H. done. simpl. apply IH. simpl in H. inversion H. done. simpl in Hsize. lia. lia. 
Qed.

Lemma forallzipP : forall (A B : eqType) (P : A * B -> Prop) a b l l',  size l = size l' -> (forall x0, x0 < size l -> P (nth a l x0,nth b l' x0)) <-> 
Forall P (zip l l').
Proof.
intros.  split. apply forallzipP1. done. move/forallzipP2=>HH. apply HH. done. 
Qed.

Lemma forallzipto1 : forall (A B : Type) (P : A -> Prop) (l : seq A) (l' : seq B), size l = size l' -> 
Forall (fun p => P p.1) (zip l l') -> Forall P l.
Proof.
move => A B P. elim. case. done. done. intros. destruct l'. simpl in H0. done. simpl in *. inversion H1. subst. simpl in *. constructor. done. apply :H. inversion H0. eauto. done. 
Qed.

Lemma forallzipto2 : forall (A B : Type) (P : B -> Prop) (l' : seq B) (l : seq A), size l = size l' -> 
Forall (fun p => P p.2) (zip l l') -> Forall P l'.
Proof.
move => A B P. elim. case. done. done. intros. destruct l0. simpl in H0. done. simpl in *. inversion H1. subst. simpl in *. constructor. done. apply :H. inversion H0. eauto. done. 
Qed.


Lemma forallP : forall (A : eqType) (P : A -> Prop) a l,(forall x0, x0 < size l -> P (nth a l x0)) -> 
Forall P l.
Proof. intros.
apply/Forall_forall. intros. move : H0 => /nthP H3.  specialize H3 with a. destruct H3. rewrite -H1. auto.
Qed.

Lemma my_in_cons : forall (A :eqType) (a : A) l, a \in (a::l).
Proof. intros. rewrite !inE eqxx. done. Qed.

Lemma my_in_cons2 : forall (A :eqType) (a a0 : A) l, a \in l -> a \in (a0::l).
Proof. intros. rewrite !inE H. lia. Qed.

Hint Resolve my_in_cons my_in_cons2.

Ltac case_if := match goal with 
                | [ |- context[if ?X then _ else _ ]] => have : X by subst
                | [ |- context[if ?X then _ else _ ]] => have : X = false by subst 

                | [ |- context[if ?X then _ else _ ]] => let H := fresh in destruct X eqn:H

                end; try (move=>->).

(*Ltac iflia := case_if;*)

Ltac rifliad := (repeat case_if); try done.

Lemma neg_sym : forall (A : eqType) (a b : A), (a != b) = (b != a).
Proof.
intros. destruct (eqVneq a b).  done. done. 
Qed.

Ltac split_and := intros;repeat (match goal with 
                   | [ H : is_true (_ && _) |- _ ] => destruct (andP H);clear H
                   | [ H : (_ && _) = true  |- _ ] => destruct (andP H);clear H

                   | [ |- is_true (_ && _) ] => apply/andP;split 

                  end);auto.

Lemma negb_involutive : forall b, ~~ ~~ b = b. case;done. Qed.


Open Scope fset_scope.
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


Ltac norm_eqs := repeat (match goal with 
                   | [ H : (_ == _) |- _ ] => move : H => /eqP=>H
                   | [ H : (_ == _) = true |- _ ] => move : H => /eqP=>H
                   | [ H : (_ == _) = false |- _ ] => move : H => /negbT=>H

                  end);subst;repeat (match goal with 
                   | [ H : is_true (?a != ?a_) |- _ ] => rewrite eqxx in H;done 

                  end).

