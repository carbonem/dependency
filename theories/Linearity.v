From mathcomp Require Import all_ssreflect zify.
From Equations Require Import Equations.
From mathcomp Require Import fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From deriving Require Import deriving.
Require Import Dep.Global_Syntax.


Unset Elimination Schemes. Check seq.
CoInductive sgType  : Type :=
  | SGEnd : sgType  
  | SGMsg : action -> value -> sgType -> sgType  
  | SGBranch : action -> seq sgType -> sgType  .
Set Elimination Schemes.




Search _ Forall.

Inductive Forall2 (A B : Type) (R : A -> B -> Type) : seq A -> seq B -> Prop :=
    Forall2_nil : Forall2 R nil nil | Forall2_cons : forall (x : A) (y : B) (l : seq A) (l' : seq B), R x y -> Forall2 R l l' -> Forall2 R (x :: l) (y :: l').
Hint Constructors Forall2. Search List.Forall.

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


Inductive Unravel (r : gType -> sgType -> Prop) : gType -> sgType -> Prop :=
 | UEnd : Unravel r GEnd SGEnd
 | UMsg a u g0 sg0 : Unravel r g0 sg0 -> Unravel r (GMsg a u g0) (SGMsg a u sg0)
 | UBranch gs sgs a : Forall2 (Unravel r) gs sgs ->  Unravel r (GBranch a gs) (SGBranch a sgs)
 | URec g sg : r g[GRec g] sg  -> Unravel r (GRec g) sg.
Hint Constructors Unravel.


Require Import Paco.paco.
Check paco2.

Definition GUnroll g sg : Prop := paco2 Unravel bot2 g sg.

Example test : GUnroll (GRec (GVar 0)) SGEnd.
unfold GUnroll. pcofix CIH. pfold. constructor. right. simpl. done.
Qed.
Check Unravel_ind.
Lemma Unravel_ind2
     : forall r P : gType -> sgType -> Prop,
       P GEnd SGEnd ->
       (forall (a : action) (u : value) (g0 : gType) (sg0 : sgType),
        Unravel r g0 sg0 -> P g0 sg0 -> P (GMsg a u g0) (SGMsg a u sg0)) ->
       (forall (gs : seq gType) (sgs : seq sgType) (a : action),
        Forall2 (Unravel r) gs sgs -> Forall2 P gs sgs -> P (GBranch a gs) (SGBranch a sgs)) ->
       (forall (g : gType) (sg : sgType), r (g)[GRec g] sg -> P (GRec g) sg) ->
       forall (g : gType) (s : sgType), Unravel r g s -> P g s.
Proof.
intros. move : g s H3. fix IH 3. move => g s [].
- apply H.
- intros. apply H0. apply u0.  apply IH. apply u0. 
- intros. apply H1. apply f.
- induction f.  done. constructor. apply IH. apply H3. apply IHf. 
- intros. apply H2. apply r0.
Qed.

Lemma GUnroll_mono : monotone2 Unravel.
Proof.
elim;intros.
-  inversion IN. 
- inversion IN. auto. 
- inversion IN. subst. auto.  
- inversion IN. eauto.  
- inversion IN. subst. constructor. move : l sgs IN H3 H. elim. 
 + intros. inversion H3. auto.
 + intros. inversion H3. subst. constructor. eapply H0.  by  rewrite inE eqxx. eauto. eauto. eauto.
   apply H. constructor. auto. auto.  intros.  eapply H0. by rewrite inE H1 orbC. eauto. eauto. 
Qed.
Hint Resolve GUnroll_mono : paco.

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





Inductive Tr : seq action -> sgType -> Prop :=
| TR_nil G : Tr nil G 
| TRMsg a u aa g0 : Tr aa g0 -> Tr (a::aa) (SGMsg a u g0)
| TRBranch a gs n aa d : n < size gs -> Tr aa (nth d gs n) ->  Tr (a::aa) (SGBranch a gs).
Hint Constructors Tr.

Definition exists_depP  (Pm : seq bool -> Prop) (P : seq action -> Prop) a0 aa a1 := exists m, size m = size aa /\ P (a0::((mask m aa))++[::a1]) /\ Pm m.
Notation exists_dep := (exists_depP (fun _ => True)).

Definition Linear (sg : sgType) := 
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

Definition all_indep (sg : sgType) := forall s n0 n1 d,
Tr s sg -> 
same_ch (nth d s n0) (nth d s n1) -> n0 < size s -> n1 < size s ->
exists_dep InDep (nth d s n0) (slice s n0 n1) (nth d s n1).


Definition Linear1 (sg : sgType) := forall aa_p a0 aa a1, 
Tr (aa_p ++ (a0::(aa++[::a1]))) sg -> 
same_ch a0 a1 -> 
exists_dep InDep a0 aa a1.

Definition Linear2 (sg : sgType) := forall aa_p a0 aa a1, 
Tr (aa_p ++ (a0::(aa++[::a1]))) sg -> 
same_ch a0 a1 -> 
exists_dep OutDep a0 aa a1.

Lemma Linear_1 : forall g, Linear g -> Linear1 g.
Proof.
intros. rewrite /Linear1. intros. apply H in H0. destruct H0. done. done. Qed.

Lemma Linear_2 : forall g, Linear g -> Linear2 g.
Proof.
intros. rewrite /Linear2. intros. apply H in H0. destruct H0. done. done. Qed.


Unset Elimination Schemes. 
Inductive step : sgType -> label  -> sgType -> Prop :=
 | GR1 (a : action) u g : step (SGMsg a u g) (a, inl u) g
 | GR2 a n d gs : n < size gs -> step (SGBranch a gs) (a, inr n) (nth d gs n)
 | GR3 a u l g1 g2 : step g1 l g2 -> ptcp_to a \notin l -> step (SGMsg a u g1) l (SGMsg a u g2)
 | GR4 a l gs gs' : Forall2 (fun g g' => step g l g') gs gs' -> (ptcp_to a) \notin l  ->  step (SGBranch a gs) l (SGBranch a gs').
Set Elimination Schemes. 
Hint Constructors step. 

Lemma step_ind
     :  forall P : sgType -> label -> sgType -> Prop,
       (forall (a : action) (u : value) (g : sgType), P (SGMsg a u g) (a, inl u) g) ->
       (forall (a : action) (n : nat) (d : sgType) (gs : seq sgType),
        n < size gs -> P (SGBranch a gs) (a, inr n) (nth d gs n)) ->
       (forall (a : action) (u : value) (l : label) (g1 g2 : sgType),
        step g1 l g2 ->
        P g1 l g2 -> ptcp_to a \notin l -> P (SGMsg a u g1) l (SGMsg a u g2)) ->
       (forall (a : action) (l : label) (gs gs' : seq sgType),
        Forall2 (fun g : sgType => step g l) gs gs' ->  Forall2 (fun g0 g2 : sgType => P g0 l g2) gs gs' -> 

        ptcp_to a \notin l -> P (SGBranch a gs) l (SGBranch a gs')) ->
       forall (s : sgType) (l : label) (s0 : sgType), step s l s0 -> P s l s0.
Proof.
move => P H0 H1 H2 H3. fix IH 4.
move => ss l s1 [].
intros. apply H0;auto. 
intros. apply H1;auto.
intros. apply H2;auto.
intros. apply H3;auto. elim : f;auto.  
Qed.

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


Ltac iflia := match goal with 
                | [ |- context[if ?X then _ else _ ]] => have : X by subst; lia
                | [ |- context[if ?X then _ else _ ]] => have : X = false by subst ; lia

                | [ |- context[if ?X then _ else _ ]] => let H := fresh in destruct X eqn:H

                end; try (move=>->).




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

Lemma step_tr_in : forall g vn g', step g vn g' -> forall s, Tr s g' -> Tr s g \/ exists n, Tr (insert s n vn.1) g /\ Forall (fun a => (ptcp_to a) \notin vn.1) (take n s).
Proof.
move => g vn g'. rewrite /insert. elim.
- intros. right. exists 0. simpl. rewrite take0 drop0 /=.  auto. 
- intros. right. exists 0. simpl. rewrite take0 drop0 /=.  split;auto.  eauto. 
- intros. destruct s;auto. 
  inversion H2. subst. move : (H0 _ H4)=>[];auto.
  move=> [] n [].  intros. right. exists n.+1. simpl. auto. 
- intros. destruct s; auto.
  inversion H2. subst. rewrite -(size_Forall2 H0) in H6.  
  case :  (@index_Forall2 _ _ gs gs' d d n _ H6 H0 _ H8). 
 * intros. left. eauto.
 * move => [] n0 [] HH0 HH1. right. exists n0.+1. rewrite /=. eauto. 
Qed.


Lemma Tr_app : forall l0 l1 G, Tr (l0++l1) G -> Tr l0 G.
Proof.
elim. rewrite /=. done.
move => a l IH l1 G. rewrite cat_cons. move => H. inversion H. 
- subst. constructor. eauto.  
- subst. eauto. 
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

Lemma In_in : forall (A : eqType) (a : A) l, In a l <-> a \in l.
Proof.
move => A a. elim. split;done.
intros. rewrite /= inE. split. case. move=>->. rewrite eqxx. done. move/H. move=>->. by rewrite orbC. 
move/orP. case. move/eqP. move=>->. auto. move/H. auto. 
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


Lemma linear1_step : forall g l g', step g l g' -> Linear g -> Linear g'.
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
have : aa_p ++ a0 :: aa ++ [:: a1; l.1] = (aa_p ++ a0 :: aa ++ [:: a1]) ++ [::l.1]. rewrite -!catA !cat_cons. f_equal. Search _ (_ :: (_ ++ _)). f_equal. rewrite -catA. f_equal. move=>->. eauto. move/Tr_app. eauto. 
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
    move/Tr_app. 
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



