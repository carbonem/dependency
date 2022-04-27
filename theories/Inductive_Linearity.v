From mathcomp Require Import all_ssreflect zify.



Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From deriving Require Import deriving.
Require Import Dep.Global_Syntax.


Ltac iflia := match goal with 
                | [ |- context[if ?X then _ else _ ]] => have : X by subst; lia
                | [ |- context[if ?X then _ else _ ]] => have : X = false by subst ; lia

                | [ |- context[if ?X then _ else _ ]] => let H := fresh in destruct X eqn:H

                end; try (move=>->).



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
-  iflia.  simpl in H0.  lia.
- done.
- f_equal. apply : H. have : i.+1 <= j.+1 by lia. intros. apply : x. done.
- rewrite (H g' i j) //=.
- f_equal. elim : l H H1. done.
  intros. rewrite /=. f_equal. apply  : H1. by rewrite inE eqxx. apply : H0. simpl in H2. apply (andP H2). apply H.
  intros.  apply : H1. by rewrite inE H3 orbC. apply : H4. done. simpl in *. apply (andP H2). 
Qed.

(*Lemma bound_subst2 : forall (g g': gType) i, (bound_i i g') -> (bound_i i.+1 g) = bound_i i (substitution i g g').   
Proof.
elim;intros; rewrite /=;try done.
- iflia. have : n < i.+1 by lia. move=>-> /=.  rewrite H. done. rewrite /=. destruct (n < i) eqn:Heqn. have : n < i.+1 by lia. move=>->. done. lia.
- apply : H
-> bound_i j g' -> bound_i (i + j) (substitution i g g').*)

Lemma bound_subst : forall (g g': gType) i j, bound_i i.+1 g -> bound_i j g' -> bound_i (i + j) (substitution i g g').
Proof.
elim.
-  rewrite /=. intros. iflia. move : H0. rewrite -(eqP H1). intros. apply : bound_le. 2: { apply : H0. }  lia. 
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
-  rewrite /=. intros. iflia. apply : bound_le. 2 : { eauto. } lia. simpl. lia. 
- done. 
- intros. simpl. apply : H. 3: {  eauto. } lia. done. 
- rewrite /=. intros. auto. 
- rewrite /=. eauto. 
- intros. simpl in *. move : (allP H1)=> HH2. apply/allP. move => l' /mapP. case. intros. 
  subst. eauto. 
Qed.

(*Lemma contractive_subst2 : forall (g g': gType) i j k, j <= i -> k <= i -> contractive_i i.+1 g -> contractive_i j g' -> contractive_i k (substitution i g g').
Proof.
elim.
-  rewrite /=. intros. iflia. simpl. lia. 
- done. 
- intros. simpl. apply : H. 3: {  eauto. } 3 : {  eauto. } lia. lia. 
- rewrite /=. intros. apply : contractive_le. 2 : { apply : H. 4 : { eauto. } lia. apply : H1. eauto. lia. 3 : { eauto. } lia. apply : H. eauto. 
- intros. simpl in *. move : (allP H1)=> HH2. apply/allP. move => l' /mapP. case. intros. 
  subst. eauto. *)
(*Lemma contractive_0 : forall (g : gType) i,  contractive_i i g -> contractive g.
Proof.
move=> g. case. done. intros.  apply : contractive_lt; last eauto. done.
Qed.*)



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


Section SubgType.
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
Qed.


(*Lemma subst_mixin : forall g0 g1 n, gt_pred n.+1 n.+1  g0 -> gt_pred n n g1 -> gt_pred (n+n) n (substitution n g0 g1).
Proof.
intros.  move : (andP H)=>[]. move : (andP H0)=>[]. intros. apply/andP. split.
apply : bound_subst. done. done.
apply : bound_contractive_subst.
done. apply : contractive_lt. 2 : { eauto. } lia. eauto. apply : bound_cont_eq. 
eauto. eauto. 
Defined.*)

(*Definition sub_subst (g0 : subgType 1) (g1 : subgType 0) := SubgType (@subst_mixin g0 g1 (valP g0) (valP g1)).*)


Inductive Forall2 (A B : Type) (R : A -> B -> Type) : seq A -> seq B -> Prop :=
    Forall2_nil : Forall2 R nil nil | Forall2_cons : forall (x : A) (y : B) (l : seq A) (l' : seq B), R x y -> Forall2 R l l' -> Forall2 R (x :: l) (y :: l').
Hint Constructors Forall2. 

Inductive Forall3 (A B C : Type) (R : A -> B -> C -> Type) : seq A -> seq B -> seq C -> Prop :=
    Forall3_nil : Forall3 R nil nil nil | Forall3_cons : forall (x : A) (y : B) (z : C) (l : seq A) (l' : seq B) (l'' : seq C), R x y z -> Forall3 R l l' l'' -> Forall3 R (x :: l) (y :: l') (z ::l'').
Hint Constructors Forall3.

Lemma index_Forall : forall (A: Type) (l0 : seq A) d0 n (P : A  -> Prop), n < size l0 -> Forall P l0 -> P (nth d0 l0 n).
Proof.
intros. move : H0 d0 n H. elim.
intros.  done. intros. destruct n. simpl. done. simpl. auto. 
Qed.


Lemma size_Forall2 : forall (A B : Type) (l0 : seq A) (l1 : seq B) P, Forall2 P l0 l1 -> size l0 = size l1. 
Proof. intros. induction H;simpl;auto. Qed.

Lemma index_Forall2 : forall (A B : Type) (l0 : seq A) (l1 : seq B) d0 d1 n (P : A -> B -> Prop), n < size l0 -> Forall2 P l0 l1 -> P (nth d0 l0 n) (nth d1 l1 n).
Proof.
intros. move : H0 d0 d1 n H. elim.
intros.  done. intros. destruct n. simpl. done. simpl. auto. 
Qed.

Lemma Forall2_Forall : forall (A B : Type) (l0 : seq A) (l1 : seq B) (P : A -> Prop), Forall2 (fun a b => P a) l0 l1 -> Forall P l0.
Proof.
intros. elim : H;auto.
Qed.


Definition label := (action * (value + nat))%type.


Definition same_ch (a0 a1 : action) := action_ch a0 == action_ch a1.

Definition II (a0 a1 : action) := (ptcp_to a0 == ptcp_to a1).
Definition IO (a0 a1 : action) := (ptcp_to a0 == ptcp_from a1).
Definition OO (a0 a1 : action) := (ptcp_from a0 == ptcp_from a1) && same_ch a0 a1.
Definition IO_OO a0 a1 := IO a0 a1 || OO a0 a1.

Inductive InDep : seq action -> Prop :=
 | ID_End a0 a1 : II a0 a1 -> InDep ([::a0; a1])
 | ID_cons a0 a1 aa: IO a0 a1 -> InDep (a1::aa) -> InDep (a0::a1::aa).
Hint Constructors InDep.



Definition indep ss := 
match ss with 
| a::a'::ss' => let: one_less := belast a' ss' in path IO a one_less && II (last a one_less) (last a' ss')
| _ => false 
end.

Lemma InDep_iff : forall ss, InDep ss <-> indep ss.
Proof.
case. split;intros;inversion H.
move => a l. case : l. split;intros;inversion H.
move => a0 l. 
elim : l a0 a. rewrite /=. move => a0 a. split;intros; inversion H;subst. done. inversion H4. auto.
move => a0 l H a1. rewrite /=. split;intros.
- inversion H0;subst. rewrite H3 /=. simpl in H. by  apply/H.
- move : H0 => /andP => [] [] /andP => [] []. intros. constructor. done. apply/H. by rewrite /= b b0.
Qed.

Inductive OutDep : seq action -> Prop :=
 | OD_end a0 a1 : IO_OO a0 a1 -> OutDep ([::a0; a1])
 | OD_cons a0 a1 aa: IO_OO a0 a1  -> OutDep (a1::aa) -> OutDep (a0::a1::aa).
Hint Constructors OutDep.

Fixpoint dep (R : action -> action -> bool) ss := 
match ss with 
| nil => false 
| a::s' => match s' with 
          | a'::nil => R a a' 
          | a'::ss' => (R a a') && dep R s'
          | _ => false
        end
        
end.

Definition outdep ss :=
match ss with 
| a::a'::ss => path IO_OO a (a'::ss)
| _ => false 
end. 

Lemma OutDep_iff : forall ss, OutDep ss <-> outdep ss.
Proof.
rewrite /outdep.
case; first (split;intros; inversion H).
move => a []; first (split;intros;inversion H).
move => a0 l. move : l a a0. elim.
- move => a a0. split; rewrite /=;intros. rewrite andbC /=. inversion H; done.
  constructor. by move : H => /andP => [] [].
- move => a l IH a0 a1. split;intros. 
 * inversion H. subst. rewrite /=. simpl in IH. rewrite H2 /=. inversion H4;subst. by rewrite H1. 
   by apply/IH. 
 * simpl in IH,H. move : H=> /andP=> [] []H0 H1. constructor;first done. by apply/IH.  
Qed.

Ltac contra_list := match goal with 
                      | H : (nil = _ ++ _) |-  _ => apply List.app_cons_not_nil in H
                      end;contradiction.

Definition in_action p a := let: Action p0 p1 k :=a in  (p==p0) || (p==p1).

Definition pred_of_action (a : action) : {pred ptcp} := fun p => in_action p a.

Canonical action_predType := PredType pred_of_action. 

Coercion to_action (l : label) : action := l.1.

Definition pred_of_label (l : label) : {pred ptcp} := fun p => in_action p l.

Canonical label_predType := PredType pred_of_label.  


Inductive Tr : seq action -> gType  -> Prop :=
| TR_nil G : Tr nil G 
| TRMsg a u aa g0 : Tr aa g0 -> Tr (a::aa) (GMsg a u g0)
| TRBranch d a n gs aa  : n < size gs -> Tr aa (nth d gs n) ->  Tr (a::aa) (GBranch a gs)
| TRUnf aa g : Tr aa g[GRec g] -> Tr aa (GRec g).
Hint Constructors Tr.

Definition exists_depP  (Pm : seq bool -> Prop) (P : seq action -> Prop) a0 aa a1 := exists m, size m = size aa /\ P (a0::((mask m aa))++[::a1]) /\ Pm m.
Notation exists_dep := (exists_depP (fun _ => True)).

Definition Linear (sg : gType) := 
forall aa_p a0 aa a1, 
Tr (aa_p ++ (a0::(aa++[::a1]))) sg -> 
same_ch a0 a1 -> 
exists_dep InDep a0 aa a1 /\ exists_dep OutDep a0 aa a1.

Definition slice (A : Type) (l : seq A) n0 n1 := take n1 (drop n0 l).

Lemma nth_slice : forall (A : Type) (n n0 : nat) (d : A) (s : seq A) x , n <= n0 -> n0 < size s ->  (nth d (take n s ++ x :: drop n s) n0.+1) = nth d s n0.
Proof.
intros. rewrite nth_cat size_take. have : n < size s by lia. move => Hn.  rewrite Hn. 
  have : n0.+1 < n = false by lia. move =>->. have : n0.+1 - n = (n0 - n).+1 by lia. move=>->.  rewrite /=. 
  rewrite nth_drop. f_equal. lia. 
Qed.

Definition all_indep (sg : gType) := forall s n0 n1 d,
Tr s sg -> 
same_ch (nth d s n0) (nth d s n1) -> n0 < size s -> n1 < size s ->
exists_dep InDep (nth d s n0) (slice s n0 n1) (nth d s n1).


Definition Linear1 (sg : gType) := forall aa_p a0 aa a1, 
Tr (aa_p ++ (a0::(aa++[::a1]))) sg -> 
same_ch a0 a1 -> 
exists_dep InDep a0 aa a1.

Definition Linear2 (sg : gType) := forall aa_p a0 aa a1, 
Tr (aa_p ++ (a0::(aa++[::a1]))) sg -> 
same_ch a0 a1 -> 
exists_dep OutDep a0 aa a1.

Lemma Linear_1 : forall g, Linear g -> Linear1 g.
Proof.
intros. rewrite /Linear1. intros. apply H in H0. destruct H0. done. done. Qed.

Lemma Linear_2 : forall g, Linear g -> Linear2 g.
Proof.
intros. rewrite /Linear2. intros. apply H in H0. destruct H0. done. done. Qed.



Definition insert (A : Type) (l : seq A) n x := ((take n l) ++ (x::(drop n l))).

Lemma insert0 : forall (A: Type) (l : seq A) x, insert l 0 x = x::l.
Proof. intros. by rewrite /insert take0 drop0 /=. Qed.

Lemma insert_nil : forall (A: Type) n (x : A), insert nil n x  = [::x]. 
Proof. intros. destruct n; done. Qed.


Lemma insert_cons : forall (A: Type) (l : seq A) n x a, insert (a::l) n x  = if n is n'.+1 then a::(insert l n' x) else x::a::l.
Proof. intros. destruct n.  rewrite insert0. done. rewrite /insert /=. done. Qed.

Lemma insert_cat : forall (A: Type) (l0 l1 : seq A) n x, insert (l0++l1) n x  = if n <= size l0 then (insert l0 n x)++l1 else l0++(insert l1 (n-(size l0)) x). 
Proof. move => A.  elim. rewrite /=. intros. destruct n. by rewrite insert0 /=. rewrite /=. done. 
intros. rewrite /=. rewrite insert_cons. destruct n. by rewrite /=. rewrite H /=. destruct (n < (size l).+1) eqn:Heqn. 
have : n <= size l by lia.  move=>->. f_equal. have : n <= size l = false by lia. move=>->. done. 
Qed.

Lemma size_insert : forall (A : Type) (l : seq A) n x, size (insert l n x) = (size l).+1. 
Proof. move=> A. elim;intros. by rewrite insert_nil. 
rewrite insert_cons /=. destruct n.  done. by rewrite /= H. 
Qed.


Definition delete (A : Type) (l : seq A) n := (take n l)++(drop n.+1 l).

Lemma delete_nil : forall (A: Type) (n : nat), delete (@nil A) n = nil.
Proof. intros. by rewrite /delete /=.  Qed.


Lemma delete_cons : forall (A: Type) l (a : A) n, delete (a::l) n = if n is n'.+1 then a::(delete l n') else l.
Proof. move => A. elim;intros; destruct n; rewrite /delete /=;try done. Qed.




Lemma size_delete : forall (A : Type) (l : seq A) n, size (delete l n) = if n < size l then (size l).-1 else size l.
Proof. move => A. elim;intros. rewrite delete_nil /=. destruct n;done. 
rewrite delete_cons /=. destruct n eqn:Heqn. by iflia. 
subst. rewrite /= H. iflia. iflia. lia. by iflia. 
Qed.

Lemma delete_insert : forall (A : Type) aa n (x : A), (delete (insert aa n x) n) = if n <= size aa then aa else insert aa n x.
Proof. move => A. elim. intros. rewrite /=. destruct n. by  rewrite insert_nil delete_cons /=. 
rewrite insert_nil delete_cons delete_nil. by iflia.  
intros. rewrite insert_cons. destruct n;rewrite /= delete_cons. done. rewrite H.
iflia. by iflia. by iflia. 
Qed.

Lemma mask_delete : forall (A: Type) d n (aa : seq A) m, nth d m n = false -> mask m aa = mask (delete m n) (delete aa n).
Proof. move => A d n aa m. move : aa m d n. elim. case; try done. intros. 
rewrite /= delete_nil /= delete_cons. destruct n. Search _ mask _ nil. by  rewrite mask0. rewrite mask0. done. 
intros. destruct m;try done. rewrite /=. destruct n. simpl in H0. subst. rewrite !delete_cons. done.
simpl in *. destruct b. f_equal. erewrite H. reflexivity.  lia. eauto. 
Qed.


Lemma insert_spec : forall (A : Type) (l : seq A) n a,  n <= size l -> exists l0 l1, l0 ++ l1 = l /\ insert l n a = l0 ++ a::l1 /\ size l0 = n.
Proof. move => A. elim. intros. exists nil,nil. rewrite insert_nil /=. destruct n;done.
intros. destruct n.  rewrite insert0. exists nil, (a::l). auto.  
rewrite insert_cons. destruct (H n a0). simpl in H0. lia. destruct H1,H1,H2. rewrite H2. rewrite -H1. exists (a::x),x0. split. by rewrite /= H1. 
rewrite /=. auto. 
Qed.


Lemma insert_delete : forall (A : Type) aa n (d : A), n < size aa -> aa = insert (delete aa n) n (nth d aa n).  
Proof.
move => A. elim. done.  
intros. rewrite delete_cons. destruct n. by  rewrite insert0 /=. rewrite insert_cons. f_equal. simpl in H0.  apply H. lia. 
Qed.
Lemma In_nth : forall (A : Type) (a : A) l d, In a l -> exists n, a = nth d l n /\ n < size l.
Proof.
move => A a. elim. done.
intros. simpl in H0. destruct H0. subst. exists 0. done. apply (H d) in H0. destruct H0. exists (x.+1). simpl. done.
Qed.
Check Tr.

Fixpoint In2 (A B: Type) (a : A) (b : B) (la : seq A) (lb : seq B) := 
match la,lb with
| nil,nil => False 
| a'::la',b'::lb' => a=a' /\ b = b' \/ In2 a b la' lb'
| _,_ => False 
end.

Lemma In2_swap  : forall (A B : Type) a b (la : seq A) (lb : seq B), In2 a b la lb -> In2 b a lb la.
Proof.
move => A B a b. elim. case. done. done.
move => a0 l IH []. done. intros. simpl. simpl in H.  destruct H. destruct H. subst. auto.
auto.
Qed.

(*Lemma In2_swap_aux  : forall (A B : Type) (P : A -> B -> Prop) a b (la : seq A) (lb : seq B), In2 a b la lb -> In2 b a lb la.*)

Lemma Forall2_forall : forall (A B : Type) (P : A -> B -> Prop) (la : seq A) (lb : seq B), Forall2 P la lb <-> (size la = size lb /\ forall a b, In2 a b la lb -> P a b).
Proof.
move => A B P la lb. split.
- elim.
 * done.  
 * intros. destruct H1. split. simpl. rewrite H1. done. intros. simpl in H3. destruct H3. destruct H3. subst. done. apply H2. done. 
elim : la lb. case. done. intros. destruct H. done.
move => a l H [] . simpl. case. done. 
intros. destruct H0. constructor. apply H1. simpl. auto.  apply H. simpl in H0.  inversion H0.  split;auto. intros. apply H1. simpl. auto. 
Qed.

Fixpoint In3 (A B C: Type) (a : A) (b : B) (c : C) (la : seq A) (lb : seq B) (lc : seq C) := 
match la,lb,lc with
| nil,nil,nil => False 
| a'::la',b'::lb',c'::lc' => a=a' /\ b = b' /\ c = c' \/ In3 a b c la' lb' lc'
| _,_,_=> False 
end.

Lemma Forall3_forall : forall (A B C : Type) (P : A -> B -> C -> Prop) (la : seq A) (lb : seq B)(lc : seq C), Forall3 P la lb lc <-> (size la = size lb /\ size lb = size lc) /\ forall a b c, In3 a b c la lb lc -> P a b c.
Proof.
move => A B C P la lb lc. split.
- elim.
 * done.  
 * intros. destruct H1. split. simpl. destruct H1. rewrite H1 H3. done. intros. simpl in H3. destruct H3. 
  ** destruct H3,H3, H4. subst. done. auto. 
elim : la lb lc. case. case. done. intros. destruct H,H. done. intros. destruct H,H. done.
move => a l H []. simpl. intros. destruct H0,H0. done. 
intros. destruct lc.  destruct H0,H0. done. destruct H0,H0. constructor. apply H1. simpl. auto.  apply H. simpl in H0.  inversion H0. simpl in H2.   inversion H2. rewrite -H4. split;auto. intros. apply : H1. simpl. auto. 
Qed.

Lemma In_nth2 : forall (A : Type) (l : seq A) (d : A) n, n < size l -> In (nth d l n) l.
Proof.
move => A. elim. done.
intros. destruct n. simpl.  auto. simpl in *. have : n < size l by lia.  move/H. auto. 
Qed.

Lemma In2_nth2 : forall (A  B: Type) (l : seq A) (lb : seq B) (d : A) (db : B) n, n < size l -> size l = size lb -> In2 (nth d l n) (nth db lb n) l lb.
Proof.
move => A B. elim. done.
intros. destruct n. simpl. destruct lb.   done. auto. 
destruct lb. done. simpl. right. simpl in *.  apply H. lia. lia. 
Qed.

Lemma In3_In2_r : forall (A B C : Type) (a : A) (b : B) (c : C) al bl cl, In3 a b c al bl cl -> In2 b c bl cl.
Proof. Admitted.

Lemma In3_In2_l : forall (A B C : Type) (a : A) (b : B) (c : C) al bl cl, In3 a b c al bl cl -> In2 a b al bl.
Proof. Admitted.

Lemma In2_In_l : forall (A B : Type) (a : A) (b : B) al bl, In2 a b al bl -> In a al.
Proof. Admitted.

Lemma In2_In_r : forall (A B : Type) (a : A) (b : B) al bl, In2 a b al bl -> In b bl.
Proof. Admitted.

Lemma In_in : forall (A : eqType) (a : A) l, In a l <-> a \in l.
Proof.
move => A a. elim. split;done.
intros. rewrite /= inE. split. case. move=>->. rewrite eqxx. done. move/H. move=>->. by rewrite orbC. 
move/orP. case. move/eqP. move=>->. auto. move/H. auto. 
Qed.

(*Lemma Tr_unf : forall g s,  Tr s g[GRec g] -> Tr s (GRec g).
Proof.
intros. constructor.*)





Unset Elimination Schemes. 
Inductive step : gType -> label  -> gType -> Prop :=
 | GR1 (a : action) u g : step (GMsg a u g) (a, inl u) g
 | GR2 a n d gs : n < size gs -> step (GBranch a gs) (a, inr n) (nth d gs n)
 | GR3 a u l g1 g2 : step g1 l g2 -> ptcp_to a \notin l -> step (GMsg a u g1) l (GMsg a u g2)
 | GR4 a l gs gs' : Forall2 (fun g g' => step g l g') gs gs' -> (ptcp_to a) \notin l  ->  step (GBranch a gs) l (GBranch a gs').
Set Elimination Schemes. 
Hint Constructors step. 

Lemma step_ind
     :  forall P : gType -> label -> gType -> Prop,
       (forall (a : action) (u : value) (g : gType), P (GMsg a u g) (a, inl u) g) ->
       (forall (a : action) (n : nat) (d : gType) (gs : seq gType),
        n < size gs -> P (GBranch a gs) (a, inr n) (nth d gs n)) ->
       (forall (a : action) (u : value) (l : label) (g1 g2 : gType),
        step g1 l g2 ->
        P g1 l g2 -> ptcp_to a \notin l -> P (GMsg a u g1) l (GMsg a u g2)) ->
       (forall (a : action) (l : label) (gs gs' : seq gType),
        Forall2 (fun g : gType => step g l) gs gs' ->  Forall2 (fun g0 g2 : gType => P g0 l g2) gs gs' -> 

        ptcp_to a \notin l -> P (GBranch a gs) l (GBranch a gs')) ->
       forall (s : gType) (l : label) (s0 : gType), step s l s0 -> P s l s0.
Proof.
move => P H0 H1 H2 H3. fix IH 4.
move => ss l s1 [].
intros. apply H0;auto. 
intros. apply H1;auto.
intros. apply H2;auto.
intros. apply H3;auto. elim : f;auto.  
Qed.


(*Really nice, define reduction with smart constructors, no exotic terms*)
(*Unset Elimination Schemes.
Inductive step : subgType 0 -> label  -> subgType 0 -> Prop :=
 | GR1 (a : action) u g : step (SGMsg a u g) (a, inl u) g
 | GR2 a n d gs : n < size gs -> step (SGBranch a gs) (a, inr n) (nth d gs n)
 | GR3 a u l g1 g2 : step g1 l g2 -> ptcp_to a \notin l -> step (SGMsg a u g1) l (SGMsg a u g2)
 | GR4 a l gs gs' : Forall2 (fun g g' => step g l g') gs gs' -> (ptcp_to a) \notin l  ->  step (SGBranch a gs) l (SGBranch a gs')
 | GR_rec g l g' : step (sub_subst g (SGRec g)) l g'  -> step (SGRec g) l g'.
Set Elimination Schemes. 
Hint Constructors step. 


Lemma step_ind :  forall P : subgType 0 -> label -> subgType 0 -> Prop,
       (forall (a : action) (u : value) (g : subgType 0), P (SGMsg a u g) (a, inl u) g) ->
       (forall (a : action) (n : nat) (d : subgType 0) (gs : seq (subgType 0)),
        n < size gs -> P (SGBranch a gs) (a, inr n) (nth d gs n)) ->
       (forall (a : action) (u : value) (l : label) (g1 g2 : subgType 0),
        step g1 l g2 -> P g1 l g2 -> ptcp_to a \notin l -> P (SGMsg a u g1) l (SGMsg a u g2)) ->
       (forall (a : action) (l : label) (gs gs' : seq (subgType 0)),
        Forall2 (fun g : subgType 0 => [eta step g l]) gs gs' -> Forall2 (fun g0 g1 => P g0 l g1) gs gs' -> ptcp_to a \notin l -> P (SGBranch a gs) l (SGBranch a gs')) ->
       (forall (g : subgType 1) (l : label) (g' : subgType 0),
        step (sub_subst g (SGRec g)) l g' -> P (sub_subst g (SGRec g)) l g' -> P (SGRec g) l g') ->
       forall (s : subgType 0) (l : label) (s0 : subgType 0), step s l s0 -> P s l s0.
Proof.
move => P H0 H1 H2 H3 H4. fix IH 4.
move => g l g0  [].
intros. apply H0;auto. 
intros. apply H1;auto.
intros. apply H2;auto.
intros. apply H3;auto. elim : f;auto.  
intros. apply H4;auto.
Qed.*)

(*Lemma test : forall(a b c : subgType 0),  a = b -> b = c -> a = c.
Proof.
intros. rewrite -H in H0. *)
Lemma step_tr_in : forall g vn g', step g vn g' -> forall s, Tr s g' -> Tr s g \/ exists n, Tr (insert s n vn.1) g /\ Forall (fun a => (ptcp_to a) \notin vn.1) (take n s).
Proof.
move => g vn g'. rewrite /insert. elim.
- intros. right. exists 0. simpl. rewrite take0 drop0 /=.  auto. 
- intros. right. exists 0. simpl. rewrite take0 drop0 /=. eauto.  
- intros. destruct s;auto. 
  inversion H2. subst. move : (H0 _ H4)=>[];auto.
  move=> [] n [].  intros. right. exists n.+1. simpl. auto. 
- intros. destruct s; auto.
  inversion H2. subst. rewrite -(size_Forall2 H0) in H6.  
  case :  (@index_Forall2 _ _ gs gs' d d n _ H6 H0 _ H8). 
 * intros. left. eauto.
 * move => [] n0 [] HH0 HH1. right. exists n0.+1. rewrite /=. eauto. 
Qed.


Lemma Tr_app : forall (G : gType) l0 l1, gt_pred 0 0 G -> Tr (l0++l1) G -> Tr l0 G.
Proof.
intros.  remember (l0 ++ l1). elim : H0 H l0 l1 Heql ;intros.  destruct l0;done. 

destruct l0. done. rewrite cat_cons in Heql. inversion Heql. subst. eauto.  
destruct l0. done. rewrite cat_cons in Heql. inversion Heql. subst.
apply : TRBranch;  eauto. apply : H1. simpl in H2. destruct (andP H2).   apply/andP.  split.
apply (allP H1).  apply mem_nth.  done. apply (allP H3). apply mem_nth. done.
eauto. constructor. simpl in H. apply : H0. apply : subst_mixin. done. done. eauto.
Qed.

Lemma take_cat2
     : forall (n0 : nat) (T : Type) (s1 s2 : seq T),
       take n0 (s1 ++ s2) = (if n0 <= size s1 then take n0 s1 else s1 ++ take (n0 - size s1) s2).
Proof.
intros. rewrite take_cat. iflia. iflia. done. iflia. have : n0 = size s1 by lia. move=>->. have : size s1 - size s1 = 0 by lia.  move=>->. rewrite take0 cats0. by  rewrite take_size. done.
Qed.

Lemma drop_cat2 
     : forall (n0 : nat) (T : Type) (s1 s2 : seq T),
       drop n0 (s1 ++ s2) = (if n0 <= size s1 then drop n0 s1 ++ s2 else drop (n0 - size s1) s2).
Proof. intros. rewrite drop_cat. iflia. iflia. done. iflia.  have : n0 = size s1 by lia. move=>->. have : size s1 - size s1 = 0 by lia. move=>->. rewrite drop0. rewrite drop_oversize //=. done. 
Qed.


Lemma split_mask : forall (A : Type) (l0 : seq A) x l1 m, size m = size (l0++x::l1) ->
mask m (l0 ++ (x :: l1)) =
  mask (take (size l0) m) l0 ++ (nseq (nth false m (size l0)) x) ++ mask (drop (size l0).+1 m) l1.
Proof.
move => A. elim. 
- rewrite /=. intros. rewrite take0 /=. case : m H. done. 
  intros. by  rewrite mask_cons /= drop0. 
- rewrite /=. intros. case : m H0.  done. rewrite /=. intros. 
  case : a0. rewrite cat_cons. f_equal. rewrite H //=. lia. 
  rewrite H //=. lia.
Qed.

Definition IO_II a0 a1 := IO a0 a1 || II a0 a1.

Lemma indep0 : forall l0 l1, indep (l0 ++ l1) -> if l0 is x::l0' then path IO_II x l0' else true.
Proof.
move => l0 l1. rewrite /indep.
case :l0 ;first done.
move => a l. rewrite /=. case : l;first done.
move => a0 l. rewrite /=. move/andP=> [] H H1. elim : l a a0 H H1.
- move => a a0. rewrite /=.  case : l1. simpl. rewrite /IO_II. move => _ -> . by rewrite orbC.  
  move => a1 l. rewrite/= /IO_II. by move/andP=> [] ->.
- move => a l IH a0 a1. rewrite /= /IO_II. move/andP=> [] ->. intros. rewrite /=. 
  unfold IO_II in IH. apply/IH. done. done.
Qed.

Lemma outdep0 : forall l0 l1, outdep (l0 ++ l1) -> if l0 is x::l0' then path IO_OO x l0' else true.
Proof.
rewrite /outdep. case;first done. 
move => a l l1. rewrite cat_cons. case : l;first done.  
move => a0 l. rewrite cat_cons. rewrite -cat_cons. rewrite cat_path. by move/andP=>[]. 
Qed.


Lemma in_action_from' : forall p0 p1 c, p0 \in Action p0 p1 c.
Proof. intros. by rewrite /in_mem /= eqxx. Qed.

Lemma in_action_to' : forall p0 p1 c, p1 \in Action p0 p1 c.
Proof. intros. by rewrite /in_mem /= orbC eqxx. Qed.

Lemma in_action_from : forall a, ptcp_from a \in a.
Proof. intros. destruct a. rewrite /=. rewrite in_action_from' //=. Qed.

Lemma in_action_to : forall a, ptcp_to a \in a.
Proof. intros. destruct a. rewrite /=. rewrite in_action_to' //=. Qed.

Hint Resolve in_action_from in_action_to in_action_from' in_action_to'.

Lemma IO_in_action : forall a0 (l : action), IO a0 l -> (ptcp_to a0) \in l.
Proof.
move => a0 a1. rewrite /IO.  rewrite /IO. move/eqP=>->. apply in_action_from.
Qed.

Lemma II_in_action : forall a0 (l : action), II a0 l -> (ptcp_to a0) \in l.
Proof.
move => a0 a1. rewrite /II.  move/eqP=>->. apply in_action_to.
Qed.


Lemma IO_II_in_action : forall a0 (l : action), IO_II a0 l -> (ptcp_to a0) \in l.
Proof.
move => a0 a1. rewrite /IO_II. move/orP=>[]; auto using IO_in_action, II_in_action. 
Qed.


Lemma InDep_insert : forall a0 aa a1 n x,  n <= size aa -> Forall (fun a : action => ptcp_to a \notin x) (take n aa) -> ptcp_to a0 \notin x -> exists_dep InDep a0 (insert aa n x) a1 -> exists_dep InDep a0 aa a1.
Proof. 
intros. destruct H2,H2,H3,H4. have : n < size x0.  rewrite size_insert in H2. rewrite H2. lia. 
move=> H4. destruct (nth false x0 n == false) eqn:Heqn. 
- move : (eqP Heqn)=>HH. move : H3. rewrite (@mask_delete _ false n (insert aa n x)) //=. rewrite !delete_insert.  iflia. 
 intros. exists (delete x0 n). rewrite size_delete.  iflia. rewrite H2 size_insert /=. auto. 
- have : nth false x0 n = true by lia. clear Heqn. move => Heqn. 
  destruct (@insert_spec _ aa n x H).  destruct H5,H5,H6. move : H3. rewrite H6 split_mask; last (rewrite size_cat /= H2 size_insert -H5 size_cat; lia).
  rewrite H7 Heqn /=. 
   have : (a0 :: (mask (take n x0) x1 ++ x :: mask (drop n.+1 x0) x2) ++ [:: a1]) = 
          ((a0 :: (mask (take n x0) x1 ++ [::x])) ++ ((mask (drop n.+1 x0) x2) ++ [:: a1])). 
   rewrite -!catA. rewrite !cat_cons /=. rewrite !catA. f_equal.  rewrite -!catA. f_equal. move=>->.
 move/InDep_iff. move/indep0.

   rewrite cat_path /=. move/andP=>[] _. rewrite andbC /=.  destruct (mask (take n x0) x1) eqn:Heqn4. 
 * rewrite /=. move/IO_II_in_action. move => HH.  rewrite HH in H1. done. 
 * rewrite /=. intros. have : In (last a l) (take n aa).  rewrite -H5 take_cat. iflia.  apply/In_in. rewrite mem_cat. 
   apply/orP. left. eapply mem_mask with (m:= (take n x0)).  rewrite Heqn4.  by rewrite mem_last.  

   move : H0. rewrite List.Forall_forall.  intros.  apply H0 in x3. apply IO_II_in_action in b. rewrite b in x3. done. 
Qed.

Lemma ind_aux : forall l a a0, path IO a (belast a0 l) -> II (last a (belast a0 l)) (last a0 l) -> IO_II a a0 && path IO_II a0 l.
Proof.
 elim.
- move => a a0.  rewrite /= /IO_II. move => _ ->.  by rewrite orbC.
- move => a l IH a0 a1. rewrite /=. move/andP=>[].  intros. rewrite /IO_II a2 /=.
  unfold IO_II in IH. apply/IH. done. done. 
Qed.

Lemma indep1 : forall l0 l1, indep (l0 ++ l1) -> if l1 is x::l1' then path IO_II x l1' else true.
Proof.
case. simpl. case. done. rewrite /=. move => a []. done.
move => a0 l. rewrite /=. intros. move : H. move/andP=>[]. intros. apply/ind_aux. done. done. 
- move => a l l1. rewrite /=. case : l. rewrite /=. case : l1. done.
  intros. move : H=> /andP=> [] []. intros. move : (ind_aux a1 b). by move/andP=>[].
- move => a0 l. rewrite /=. move/andP=> []. intros. case : l1 a1 b. done. 
intros. move : (ind_aux a2 b). move/andP=> []. rewrite cat_path. move => _ /andP => [] []. 
  rewrite /=. move => _ /andP => [] []. done. 
Qed.

Lemma last_eq : forall A (l0 l1 : seq A) x0 x1, l0 ++ ([::x0]) = l1 ++ ([::x1]) -> l0 = l1 /\ x0 = x1.
Proof.
move => A. elim.
case. rewrite /=. move => x0 x1. case. done.
move => a l x0 x1. rewrite /=. case. move =>-> H. apply List.app_cons_not_nil in H. done. 
rewrite /=. intros. case : l1 H0.  rewrite /=. case. move => _ /esym H1. apply List.app_cons_not_nil in H1. done. 
intros. move : H0.  rewrite cat_cons. case. intros. move : (H _ _ _ H1). case. intros. split. subst. done. done. 
Qed.



Lemma split_list : forall A (l : seq A), l = nil \/ exists l' a, l = l'++([::a]).
Proof.
move => A. elim.
auto.  move => a l [] . move =>->. right.  exists nil. exists a. done. 
move => [] l' [] a0 ->. right. exists (a::l'). exists a0. done.
Qed.


Lemma no_indep : forall a0 l a1, (ptcp_to a0) \notin a1 -> Forall (fun a : action => ptcp_to a \notin a1) l -> exists_dep InDep a0 l a1 -> False.
Proof.
intros. destruct H1,H1,H2,H3. move : H2. move/InDep_iff. rewrite /=.  destruct (mask x l ++ [:: a1]) eqn :Heqn. destruct (mask x l). done. done. rewrite Heqn. 
move/andP=>[]. intros. have : last a l0 = a1.  destruct (split_list l0).  subst. destruct (mask x l). simpl in Heqn. inversion Heqn. done. simpl in Heqn. inversion Heqn. destruct l0;done. destruct H2,H2. rewrite H2. rewrite last_cat. simpl. rewrite H2 in Heqn. rewrite -cat_cons in Heqn. apply last_eq in Heqn. destruct Heqn. done. 
intros.  rewrite x0 in b. (* have : (last a0 (belast a l0)) \in l. apply mem_mask with (m := x). *)
destruct (split_list (mask x l)). rewrite H2 in Heqn.    simpl in Heqn. destruct l0;try done. inversion Heqn. subst. simpl in *. 
apply II_in_action in b. rewrite b in H.  done. 
destruct H2,H2. rewrite H2 in Heqn. have : belast a l0 = x1 ++ [:: x2].  destruct (split_list l0). subst. simpl in *. rewrite -catA in Heqn.  destruct x1; try done. simpl in Heqn. inversion Heqn. destruct x1;done. destruct H3. destruct H3. rewrite H3 belast_cat /=. rewrite -cat_rcons. rewrite -lastI cats0. rewrite H3 in Heqn. rewrite -cat_cons in Heqn. 
apply last_eq in Heqn. destruct Heqn. done. intros. rewrite x3 in b. rewrite last_cat in b. simpl in b.  
have : x2 \in l. apply mem_mask with (m:= x). rewrite H2. by rewrite mem_cat inE eqxx orbC. 
move/In_in. move : H0. move/List.Forall_forall. move=> Hf.  move/Hf=>Hp. apply II_in_action in b. rewrite b in Hp. done. 
Qed.

Lemma  mask_take: forall (A : Type) (l : seq A) m, mask (take (size l) m) l = mask m l.
Proof.
move => A. elim. intros. by rewrite /= take0 !mask0.
intros. rewrite /=. destruct m.  simpl. done. rewrite /=. destruct b. f_equal. done. done.
Qed.

Lemma size_mask' : forall (A : eqType) (l : seq A) (m : bitseq)  x, x \in (mask m l) -> exists l0 l1, l = l0++(x::l1).  
Proof.
move => A. elim. intros. rewrite mask0 in H. done.
intros. move : H0. destruct m.  rewrite mask0s.  done. simpl. destruct b. 
rewrite /=. rewrite inE. move/orP=>[]. move/eqP=>->. exists nil,l. done. 
move/H=>[] x0 [] x1 ->. exists (a::x0),x1. done. 
move/H=> [] x0 [] x1 ->. exists (a::x0),x1. done. 
Qed.


Lemma get_neigbor : forall (P : action -> action -> bool) a p x_end m, path P a ((mask m p)++[::x_end]) -> exists x_in, x_in \in (a::p) /\ P x_in x_end. 
Proof. 
intros. 
case : (split_list (mask m p)) H. move =>->. rewrite /= andbC /=. intros. exists a. by rewrite inE eqxx /=.
move => [] l' [] a0 Heqa2.  move : (Heqa2) =>->. rewrite -catA. rewrite cat_path /=.
move/andP=> [] _ /andP => [] [] _. rewrite andbC /=. move => HH.
have : a0 \in a::p. rewrite inE.  apply/orP. right. apply (@mem_mask _ _  m). 
rewrite Heqa2. by rewrite mem_cat inE eqxx orbC. 
intros. exists a0. by rewrite x. 
Qed.

Lemma in_split : forall (A : eqType) l (x : A), x \in l -> exists l0 l1, l = l0 ++ x::l1.
Proof.
move => A. elim. done.
move => a l IH x. rewrite inE. move/orP=>[]. move/eqP=>->. exists nil. exists l. done. move/IH=> [] l0 [] l1 ->. exists (a::l0),l1. done. 
Qed. 



Lemma Linear_step  : forall (g : subgType 0) l g', step g l g' -> Linear g -> Linear g'.
Proof.
intros. rewrite /Linear. intros. move : (step_tr_in H H1)=>[]. intros. eauto.  
move => [] n [] Htr Hf. move : Htr. rewrite insert_cat.
destruct (n <= size aa_p) eqn:Heqn;eauto. 
rewrite insert_cons. destruct (n - size aa_p) eqn:Heqn2. 
have : (aa_p ++ [:: l.1, a0 & aa ++ [:: a1]]) = ((aa_p ++ [:: l.1])++ a0::aa ++ [:: a1]). by rewrite -catA /=.
move=>->. eauto. 
rewrite insert_cat. destruct (n0 > size aa) eqn:Heqn3.
have : n0 <= size aa = false by lia. move=>->. 
rewrite insert_cons. destruct (n0 - size aa) eqn:Heqn4. lia. rewrite insert_nil.
have : aa_p ++ a0 :: aa ++ [:: a1; l.1] = (aa_p ++ a0 :: aa ++ [:: a1]) ++ [::l.1]. rewrite -!catA !cat_cons. f_equal. Search _ (_ :: (_ ++ _)). f_equal. rewrite -catA. f_equal. move=>->. eauto. move/Tr_app. move : (valP g).  intros. eauto. 
have : n0 <= size aa by lia. move=>->. intros. (*setup finished*)
move : (H0 _ _ _ _ Htr H2)=>Hlin.
move : Hf. have : n = n0.+1 + (size aa_p) by lia. move=>->. rewrite take_cat.
have :  n0.+1 + size aa_p < size aa_p = false by lia. move=>->. rewrite /=.
have : (n0.+1 + size aa_p - size aa_p) = n0.+1  by lia. move=>->.
rewrite /=. rewrite take_cat2. have : n0 <= size aa by lia. move=>->. rewrite -cat1s catA.  
move/List.Forall_app=>[] /List.Forall_app=> [] [] HH0 HH1 HH2.  have : n0 <= size aa by lia.  intros. 
split. 
- apply : InDep_insert. apply : x. eauto. inversion HH1. done. apply Linear_1 in H0.  eauto. 
- destruct Hlin. destruct H4,H4,H5,H6. have : n0 < size x0.  rewrite size_insert in H4. rewrite H4. lia. 
  
  move=> HH4. destruct (nth false x0 n0 == false) eqn:Heqn4. 
- move : (eqP Heqn4)=>HH. move : H5. rewrite (@mask_delete _ false n0 (insert aa n0 l.1)) //=. rewrite delete_insert. iflia.  intros. exists (delete x0 n0). rewrite size_delete.  iflia. rewrite H4 size_insert /=. split;auto.  

- have : nth false x0 n0 = true by lia. clear Heqn. move => Heqn. 
  destruct (@insert_spec _ aa n0 l.1 x).  destruct H6,H6,H7.  move : H5. rewrite H7 split_mask; last  (rewrite size_cat /= H8 H4 size_insert -H6 size_cat;  lia).
  rewrite H8. rewrite Heqn /=. move/OutDep_iff. 
  have : (a0 :: (mask (take n0 x0) x1 ++ l.1 :: mask (drop n0.+1 x0) x2) ++ [:: a1]) = 
         (a0 :: mask (take n0 x0) x1 ++ [::l.1]) ++ ((mask (drop n0.+1 x0) x2) ++ [:: a1]).
  rewrite -!catA cat_cons /=. f_equal. rewrite -catA. f_equal. move=>->.
 move/outdep0.
  move/get_neigbor=>[] xin []. intros.
  
rewrite /IO_OO in b. case : (orP b).

 *  intros.  exfalso. move : a.  rewrite inE. move/orP=>[]. 
  ** move/eqP=>HHeq. inversion HH1. apply : negP. apply H10. apply/IO_in_action. rewrite -HHeq. done. 
  **  rewrite -H6 in HH2. move : HH2. rewrite take_cat. iflia.
      move/List.Forall_app=>[]. move/List.Forall_forall=> Hf _. intros.  apply/negP. apply : Hf. apply/In_in. apply : b0. apply/IO_in_action. done. 
 *  rewrite /OO. move/andP=> [] /eqP _ HHH0. 
     move : (in_split a)=> [] l1 [] l2 Heq0.
    move : Htr.  rewrite H7. rewrite -!cat_cons. rewrite Heq0.
    have :  (aa_p ++ ((l1 ++ xin :: l2) ++ l.1 :: x2) ++ [:: a1]) =
            ((aa_p ++ l1) ++ (xin::l2 ++ [:: l.1]))++(x2++[::a1]).
    rewrite -!catA; f_equal. f_equal. rewrite /=. f_equal.  rewrite -catA.  f_equal. move=>->.
    move/Tr_app. move : (valP g). move => H0H  H1H. apply H1H in H0H. move : H0H.
   move/H0. move => HH'. apply HH' in HHH0. destruct HHH0. 
   destruct H5,H5,H10,H11. apply InDep_iff in H10. move : H10.
     case : (split_list (mask x3 l2)). move=>->. rewrite /=.  move/II_in_action=>HII.   exfalso. move : a. rewrite inE.  move/orP=>[].
  **  move/eqP=> HHeq'. inversion HH1. apply : negP. apply H12. rewrite -HHeq'. done. 
  ** intros. rewrite -H6 in HH2. move : HH2. rewrite take_cat. iflia.
      move/List.Forall_app=>[]. move/List.Forall_forall=> Hf _. intros.  apply/negP. apply : Hf. apply/In_in. apply : b0. done. 
 * move=> [] l' [] a2 HHeq'. rewrite HHeq'.
     rewrite  -!catA -cat_cons. move/indep1. rewrite /= andbC /=. move/IO_II_in_action=> Hia.  exfalso. 
     move : HH2. rewrite -H6. rewrite take_cat. iflia. 
      move/List.Forall_app=>[]. move/List.Forall_forall=> Hf _. apply : negP. apply : Hf. apply/In_in. 2: { apply : Hia. } 
    
       destruct l1.  simpl in Heq0.  inversion Heq0.  eapply mem_mask with (m:= x3). rewrite HHeq'. by rewrite mem_cat inE eqxx orbC. simpl in Heq0. 
inversion Heq0. rewrite mem_cat.  apply/orP. right. rewrite inE. apply/orP. right. eapply mem_mask with (m:=x3). rewrite HHeq'. by  rewrite mem_cat inE eqxx orbC. 
Qed.



