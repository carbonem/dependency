From mathcomp Require Import all_ssreflect zify.



Require Import Dep.Global_Syntax Dep.Syntax. 
Require Import Dep.unscoped. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Definition in_action p a := let: Action p0 p1 k := a in  (p==p0) || (p==p1).


Inductive Forall2 (A B : Type) (R : A -> B -> Type) : seq A -> seq B -> Prop :=
    Forall2_nil : Forall2 R nil nil | Forall2_cons : forall (x : A) (y : B) (l : seq A) (l' : seq B), R x y -> Forall2 R l l' -> Forall2 R (x :: l) (y :: l').
Hint Constructors Forall2. 

Inductive Forall3 (A B C : Type) (R : A -> B -> C -> Type) : seq A -> seq B -> seq C -> Prop :=
    Forall3_nil : Forall3 R nil nil nil | Forall3_cons : forall (x : A) (y : B) (z : C) (l : seq A) (l' : seq B) (l'' : seq C), R x y z -> Forall3 R l l' l'' -> Forall3 R (x :: l) (y :: l') (z ::l'').
Hint Constructors Forall3.

(*Inductive label := 
 | LU : action -> value -> label
 | LN : action -> nat -> label. 
*)
Notation nth_error := List.nth_error. 



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

(*Fixpoint dep (R : action -> action -> bool) ss := 
match ss with 
| nil => false 
| a::s' => match s' with 
          | a'::nil => R a a' 
          | a'::ss' => (R a a') && dep R s'
          | _ => false
        end
        
end.*)

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


(*Definition label_indDef := [indDef for label_rect].
Canonical label_indType := IndType label label_indDef.
Definition label_eqMixin := [derive eqMixin for label].
Canonical label_eqType := EqType label label_eqMixin.

Definition act_of_label l := 
match l with 
| LU a _ => a
| LN a _ => a
end.

Definition pred_of_label (l : label) : {pred ptcp} := fun p => in_action p (act_of_label l).

Canonical label_predType := PredType pred_of_label. *)


(*Maybe reflect into function*)
Check unf.
Inductive Tr : seq action -> gType -> Prop :=
| TR_nil G : Tr nil G 
| TR_msg a u aa g0 : Tr aa g0 -> Tr (a::aa) (GMsg a u g0)
| TR_branch n g a gs aa : n < size gs -> Tr aa (nth g gs n) ->  Tr (a::aa) (GBranch a gs)
| TR_rec aa g : Tr aa (unf g ) -> Tr aa (GRec g).
Hint Constructors Tr.


Inductive cgType : Set := CGType g of contractive g.

Coercion gType_of_cont i := let: CGType g _ := i in g.

Canonical cgType_subType := [subType for gType_of_cont].
Definition cgType_eqMixin := Eval hnf in [eqMixin of cgType by <:].
Canonical cgType_eqType := Eval hnf in EqType cgType cgType_eqMixin.

(*Lemma next_rec : forall g, contractive_i 1 g -> (unf (GRec g) (mu_height (GRec g))) = 
                      (unf g[GRec g] (mu_height g[GRec g])).
Proof. intros. rewrite /= mu_height_subst //=.
Qed.*)



(*Lemma tr_rec : forall g aa, contractive_i 1 g -> tr aa (GRec g) = tr aa g[GRec g].
Proof.
intros. case : aa.  done. rewrite /=. intros. rewrite mu_height_subst //=. 
Qed.


Lemma contractive_subst : forall g i, contractive_i i (GRec g)  -> contractive_i i g[GRec g].
Proof.
elim.
3 : { 
intros. rewrite /=. *)

(*Locate "list_map".

Print g_next.

Fixpoint g_act  g :=
 match g with
                 | GMsg a _ _ => Some a
                 | GBranch a gs => Some a
                 | GRec g' => g_act g'
                 | _ => None
                 end.
Fixpoint g_next2 sigma  g :=
 match g with
                 | GMsg _ _ g' => Some ([::g'])
                 | GBranch a gs => Some gs
                 | GRec g' => g_next2 ( g .: sigma) g'
                 | GVar n => Some ([::(sigma n)])
                 | GEnd => None
                 end.

Fixpoint tr (ls : seq action) (g : gType)  :=
if ls is a::ls' then if (g_act g,g_next2 GVar g) is (Some a',Some gs) then (a == a') && has (tr ls') gs
                                                else false 
               else true.


Lemma g_act_unf : forall g sigma, (forall x, sigma x = GVar x) -> g_act g = g_act (unf_aux sigma g).
Proof.
elim; try done. intros. rewrite /=. rewrite H. done. 
intros. simpl. rewrite (H GVar). rewrite /unf /=. rewrite H.

Lemma g_next_unf : forall g, map unf (g_next g) = g_next (unf g).
Proof.
elim.
3: { rewrite /=.
Lemma tr_unf : forall aa g, tr aa g = tr aa (unf g).
Proof.
rewrite /=. elim.  done. 
intros. simpl. case : aa. done. intros. rewrite /=.
rewrite /g_next /= /unf /=. 
Lemma TrP : forall ls (g : gType), reflect (Tr ls g) (tr ls g).
Proof. intros. apply Bool.iff_reflect. split.
-  elim. 
 * done.  
 * intros.  rewrite /= eqxx. asimpl. by rewrite /= H0. 
 * intros. rewrite /= eqxx /=. apply/hasP. exists (nth g0 gs n). asimpl. rewrite map_id. apply/mem_nth.  done. done. 
 * intros. simpl. rewrite /list_map. Search _ (list_map id).  Check mem_nth. by apply/(allP
rewrite /=.  intros.  by  rewrite eqxx H0. rewrite /=. intros. rewrite eqxx /=. apply/hasP. exists (nth g0 gs n). by apply/mem_nth. apply H1. by apply/(allP i)/mem_nth. intros. rewrite tr_rec //=. apply H0. done. rewrite /=. intros. clear H. move : aa H0. elim.
- done.  
-intros.  simpl. rewrite /=. intros. 
r
Search _ reflect.*)

Definition exists_depP  (Pm : seq bool -> Prop) (P : seq action -> Prop) a0 aa a1 := exists m, size m = size aa /\ P (a0::((mask m aa))++[::a1]) /\ Pm m.
Notation exists_dep := (exists_depP (fun _ => True)).


Definition Linear (sg : gType) := forall aa_p a0 aa a1, 
Tr (aa_p ++ (a0::aa++[::a1])) sg -> 
same_ch a0 a1 -> 
exists_dep InDep a0 aa a1 /\ exists_dep OutDep a0 aa a1.

Definition label := (action * (value + nat))%type.
Unset Elimination Schemes.
Inductive step : gType ->  label -> gType -> Prop :=
 | GR1 (a : action) u g : step (GMsg a u g) (a, inl u) g
 | GR2 a n d gs : n < size gs -> step (GBranch a gs) (a, inr n) (nth d gs n)
 | GR3 a u l g1 g2 : step g1 l g2 -> ~~in_action (ptcp_to a) l.1  -> step (GMsg a u g1) l (GMsg a u g2)
 | GR4 a l gs gs' : Forall2 (fun g g' => step g l g') gs gs' ->  ~~in_action (ptcp_to a) l.1  ->  step (GBranch a gs) l (GBranch a gs')
| GR5 g l g' : step (unf g) l g' -> step g l g'.


Set Elimination Schemes.
Hint Constructors step. 
Lemma step_ind
: forall P : gType -> label -> gType -> Prop,
       (forall (a : action) (u : value) (g : gType), P (GMsg a u g) (a, inl u) g) ->
       (forall (a : action) (n : nat) (d : gType) (gs : seq gType),
        n < size gs -> P (GBranch a gs) (a, inr n) (nth d gs n)) ->
       (forall (a : action) (u : value) (l : label) (g1 g2 : gType),
        step g1 l g2 -> P g1 l g2 -> ~~ in_action (ptcp_to a) l.1 -> P (GMsg a u g1) l (GMsg a u g2)) ->
       (forall (a : action) (l : label) (gs gs' : seq gType),
        Forall2 (fun g : gType => [eta step g l]) gs gs' -> Forall2 (fun g0  g2 => P g0 l g2) gs gs' ->
        ~~ in_action (ptcp_to a) l.1 -> P (GBranch a gs) l (GBranch a gs')) ->
       (forall (g : gType) (l : label) (g' : gType), step (unf g) l g' -> P (unf g) l g' ->  P g l g') ->
       forall (g : gType) (l : label) (g0 : gType), step g l g0 -> P g l g0.
Proof.
move => P H0 H1 H2 H3 H4. fix IH 4.
move => ss l s1 [].
intros. apply H0;auto. 
intros. apply H1;auto.
intros. apply H2;auto.
intros. apply H3;auto. elim : f;auto.  
intros. apply H4;auto. 
Qed.

(*Lemma Tr_branch_cons : forall s a x l, Tr s (GBranch a l) -> Tr s (GBranch a (x :: l)).
Proof. 
intros. inversion H;auto. eapply TR_branch. simpl. eauto. simpl. eauto. 
Qed.




Hint Resolve Tr_branch_cons Tr_branch_cons2.*)

Lemma index_Forall2_helper : forall A B (P : A -> B -> Prop) (l0 : seq A) (l1 : seq B) da db, Forall2 P l0 l1 -> (forall n, n < size l0 -> P (nth da l0 n) (nth db l1 n)) /\ size l0 = size l1.  
Proof.
intros. elim : H. rewrite /=. split;auto. intros.  done.
rewrite /=. intros. destruct H1. rewrite H2. split;auto. intros. destruct n. done. simpl. apply H1. lia. 
Qed.

Lemma Forall2_size : forall A B (P : A -> B -> Prop) (l0 : seq A) (l1 : seq B), Forall2 P l0 l1 -> size l0 = size l1.
Proof.
intros. elim : H. done. simpl. intros;subst. lia.
Qed.

Arguments Forall2_size {_} {_} {_} {_} {_}.


Lemma Forall2_index :  forall A B (P : A -> B -> Prop) (l0 : seq A) (l1 : seq B) da db n, n < size l0 -> Forall2 P l0 l1 -> P (nth da l0 n) (nth db l1 n).  
Proof.
intros. elim : H0  n H. done. intros. destruct n. simpl. done. simpl. apply H1. simpl in H2. lia. 
Qed.

(*Definition Forall2_index P l0 l1 := @Forall2_index_aux _ _ P l0 l1 GEnd GEnd.*)

Arguments Forall2_index {_} {_} {_} {_} {_} da db {_}.

Definition is_not_rec g := if g is GRec _ then false else true.

Lemma unf_mu_0 : forall g, mu_height g = 0 -> unf g = g.
Proof.
destruct g;auto;rewrite /=; try lia; intros;asimpl;done.
Qed.

(*Lemma unf_mu_0 : forall g, mu_height g = n.+1 -> unf g = g.
Proof.
destruct g;auto;rewrite /=; try lia; intros;asimpl;done.
Qed.*)
Print unf_aux.



Lemma Tr_unf : forall s g,Tr s (unf g) ->   Tr s g.
Proof. 
intros. remember (mu_height g). elim : n g Heqn H.  
- intros. move : H. rewrite unf_mu_0 //=.  
- intros. move : Heqn. destruct g;rewrite  /=;try done. simpl in H0. intros. constructor. apply H. lia.

Lemma trace_reduce : forall g l g',  step g l g' -> forall s, Tr s g' -> Tr s g \/ exists s0 s1, s = s0++s1 /\ Tr (s0++(l.1::s1)) g /\ Forall (fun a => ~~in_action (ptcp_to a) l.1) s0.  
Proof.
move => g l g'. elim.
- intros. right. exists nil. exists s. rewrite /=.  split; auto. 
- intros. right. exists nil. exists s. rewrite /=. split;eauto. 
- intros. inversion H2. 
 * subst.  auto. 
 * subst. move : (H0 aa H5). case. 
  ** intros. auto. 
  ** move => [] s0 [] s1 [] Heq [] HH0 HH1. subst. right. exists (a::s0),s1. rewrite /=. split;auto.  
- intros. inversion H2. 
 * subst. auto. 
 * move : H6. rewrite -(Forall2_size H0). move => H6. case : (Forall2_index g0 g0 H6 H0 aa H7);eauto.
  intros. right. destruct b,H8,H8,H9. subst. exists (a::x),x0. rewrite /=.  split;eauto. 
- intros. apply H0 in H1. destruct H1. left.  apply Tr_unf. done. destruct H1,H1,H1,H2. right. subst. exists x,x0. rewrite /=.  split;auto. split;auto. apply Tr_unf. done.
Qed.

split;auto. eauto. left. eauto. intros. in H6.  subst. Check (Forall2_index n H6 H0).  H6 H0). induction H. 
  ** done. 
  ** inversion H0. subst. destruct n. 
   *** simpl in *. apply H9 in H7. destruct H7;auto.   
       right. destruct H4, H4,H4 ,H5,H6. subst. exists (a::x0),x1. rewrite /=. split;auto.
 
   ***  apply IHForall2 in H11. 
    **** case : H11;auto. intros. right. destruct b,H4,H4,H5. subst. rewrite H4. exists x0,x1.  
         split;auto. 
    **** simpl in *. econstructor. have : n < size l' by lia. eauto. eauto. inversion H6.  done. eapply H7.  split. 
         intros. done. subst. constructor.   intros. case : H11. intros. left. elim : H0 n H6 H7;first done.  
   intros. 
  ** right.  have : aa = nil. exists (a::nil),nil. intros. elim : gs H H0.  
  ** intros. 
intros. subst. intros. case : s H2. intros. exists (a::nil),nil. nil,nil. rewrite /=. move : (H0 nil (TR_nil g2))=> [] s0 [] s1 [] HH0 [] HH1 HH2. split;auto.

Inductive stepG : gType -> gType -> label  -> gType -> Prop :=
| GGR1 a u g0 : stepG (GMsg a u g0) (GMsg a u SGEnd) (LU a u) g0
| GGR2 a d gs n : n < size gs -> stepG (GBranch a gs) (GBranch a nil) (LN a n) (nth d gs n)
| GGR3 a u  g G l g' : stepG g G l g'  -> ~~in_action (ptcp_to a) (act_of_label l) ->
                     stepG (GMsg a u g) (GMsg a u G) l (GMsg a u g')
| GGR4 a gs GS gs' l : Forall3 (fun g G g' => stepG g G l g') gs  GS gs' -> ~~in_action (ptcp_to a) (act_of_label l) -> stepG (GBranch a gs) (GBranch a GS) l (GBranch a gs').
Hint Constructors stepG.



Lemma Forall3_forall_n : forall A B C (P : A -> B -> C -> Prop) (l0 : seq A) (l1 : seq B) (l2 : seq C) da db dc, Forall3 P l0 l1 l2 -> (forall n, n < size l0 -> P (nth da l0 n) (nth db l1 n) (nth dc l2 n)) /\ size l0 = size l1 /\ size l1 = size l2.  
Proof.
intros. elim : H. rewrite /=. split;auto. intros.  done.
rewrite /=. intros. move : H1 => [] H2 [] H3 H4. split;auto. case. rewrite /=. done. move => n. rewrite /=.
intros. have : n < size l. done. intros. apply H2. done. 
Qed.

Lemma Forall3_forall_n_def : forall A B C (P : A -> B -> C -> Prop) (l0 : seq A) (l1 : seq B) (l2 : seq C) da db dc, P da db dc -> Forall3 P l0 l1 l2 -> (forall n, n <= size l0 -> P (nth da l0 n) (nth db l1 n) (nth dc l2 n)) /\ size l0 = size l1 /\ size l1 = size l2.  
Proof.
intros. elim : H0. rewrite /=. split;auto. intros.  rewrite !nth_nil. done.
rewrite /=. intros. move : H2 => [] H4 [] H5 H6. split;auto. case. rewrite /=. done. move => n. rewrite /=.
intros. have : n <= size l. done. auto.  
Qed.



Lemma step_G : forall g l g',  step g l g' -> exists G, stepG g G l g'.
Proof. 
fix IH 4. intros. case : H; try solve [intros;econstructor;eauto].
- intros. case  : (IH _ _ _ s). intros. exists (GMsg a u x). eauto. 
- intros. 
 have : exists GS, Forall3 (fun g G g' => stepG g G l0 g') gs GS gs'. 
 * elim : f.
  **  exists nil. done. 
  **  intros. case : (IH _ _ _ H).  intros. case : H1. intros. exists (x0::x1). eauto. 
 *  case. intros. exists (GBranch a x);eauto. 
Qed.

Lemma G_step : forall g G l g', stepG g G l g' -> step g l g'.
Proof.
fix IH 5. 
intros. case : H; try solve [intros;constructor;auto].
intros. constructor;eauto. Guarded. 
intros. constructor. elim : f. done. intros. constructor. eauto. 
done. done. 
Qed.

Lemma linear_sgmsg : forall a u g0, Linear (GMsg a u g0) -> Linear g0.
Proof. 
move => a u g0. rewrite /Linear /=.  intros. move : (H (a::aa_p) a0 aa a1). rewrite cat_cons /=. 
  destruct ( aa_p ++ a0 :: rcons aa a1) eqn:Heqn. case : aa_p H0 Heqn.  done. done.
  intros. have : Tr ((a::aa_p ++ (a0::aa) ++ [::a1])) (GMsg a u g0). auto.  move/H2 => H3.  move : (H3 H1). 
  move => [] mi [] mo. intros. auto. 
Qed.

Lemma nth_def : forall A (l : seq A) n d0 d1 , n < size l -> nth d0 l n = nth d1 l n.
Proof.
move => A. elim.
- case;done. 
intros. case : n H0. done. rewrite /=. intros. apply H. done. 
Qed.

Lemma linear_branch : forall a gs, Linear (GBranch a gs) -> forall n d, n < size gs -> Linear (nth d gs n).
Proof.
intros. rewrite /Linear. intros. unfold Linear in H. have : Tr (a::aa_p ++ a0::aa ++ ([::a1])) (GBranch a gs). eauto. 
intros. apply TRBranch with (n:=n). erewrite nth_def. eauto. done. intros. apply : H. move : x. rewrite -cat_cons. intros. apply : x. done. 
Qed.


(*Need to pack use of fix inside principle so that it doesn't compain about non-guarded recursion*)
Lemma stepG_ind2
     : forall P : gType -> gType -> label -> gType -> Prop,
       (forall (a : action) (u : value) (g0 : gType), P (GMsg a u g0) (GMsg a u SGEnd) (LU a u) g0) ->
       (forall (a : action) (d : gType) (gs : seq gType) (n : nat),
        n < size gs -> P (GBranch a gs) (GBranch a nil) (LN a n) (nth d gs n)) ->
       (forall (a : action) (u : value) (g G : gType) (l : label) (g' : gType),
        stepG g G l g' -> P g G l g' ->  ~~in_action (ptcp_to a) (act_of_label l) -> P (GMsg a u g) (GMsg a u G) l (GMsg a u g')) ->
       (forall (a : action) (gs GS gs' : seq gType) (l : label),
        Forall3 (fun g G : gType => [eta stepG g G l]) gs GS gs' -> Forall3 (fun g0 g1 g2 => P g0 g1 l g2) gs GS gs' ->
         ~~in_action (ptcp_to a) (act_of_label l) -> P (GBranch a gs) (GBranch a GS) l (GBranch a gs')) ->
       forall (s s0 : gType) (l : label) (s1 : gType), stepG s s0 l s1 -> P s s0 l s1.
Proof.
move => P H0 H1 H2 H3. fix IH 5.
move => ss s0 l s1 [].
intros. apply H0;auto. 
intros. apply H1;auto.
intros. apply H2;auto.
intros. apply H3;auto. elim : f. done. intros. constructor. apply IH. done. done.
Qed.

Lemma Tr_reduce : forall  G g l g', stepG g G l g' -> forall s, Tr s G -> Tr s g.
Proof.
intros. move :  H s H0.  elim/stepG_ind2. 
- intros. inversion H0. done. subst. inversion H2. subst. eauto.   
- intros.  inversion H0.  done. subst. move : H3. rewrite nth_nil.  intros. inversion H3. subst. apply TRBranch with (n:=0). 
  done. 
- intros. inversion H2.  done. subst. constructor. eauto.  
- intros. inversion H2. subst. done. subst.
  move : (@Forall3_forall_n _ _ _ _ gs GS gs' SGEnd SGEnd SGEnd H0) => [] H8 [] H9 H10.  

(*move : (@Forall3_forall_n _ _ _ (fun g0 g1 => fun _ => forall s, Tr s g1 -> Tr s g0) gs GS gs' d d d H0)=> [] H8 [] H9 H10.  *)
  case Heq : (n < size gs). 
 * move : (H8 n Heq). intros. apply TRBranch with (n:=n). apply H3. done. 
   have : size GS <= n. lia. intros. move : H5.  rewrite nth_default //=. intros. inversion H5. subst.
   apply TRBranch with (n:=n).  rewrite nth_default //=. rewrite H9. done. 
Qed.
Print stepG.

Lemma label_linear : forall g G l g',  stepG g G l g' -> Linear g -> Linear G.
Proof.
move => g G l g'. elim/stepG_ind2.
- move => a u g0 _.  rewrite /Linear. case. rewrite /=. intros. inversion H. subst. inversion H2. case : aa H H2 H3;done. 
  move => a0 l0 a1 aa a2. rewrite cat_cons. intros. inversion H. subst. inversion H2. apply List.app_cons_not_nil in H3.   done.
- move => a _ gs n Hlt HL. rewrite /Linear. intros. inversion H. apply List.app_cons_not_nil in H2. done. 
  subst. move : H3. rewrite nth_nil. intros. inversion H3. subst. exfalso. 
  clear H H0 H3.
  case : aa_p H1. rewrite /=. case. move => _ H3. apply List.app_cons_not_nil in H3. done.
  move => a2 l0.  rewrite cat_cons. case. move => _ H3. apply List.app_cons_not_nil in H3. done.
- move => a u g0 G0 l0 g'0. intros.  move : (linear_sgmsg H2). move/H0=> H3. 
  have : stepG (GMsg a u g0) (GMsg a u G0) l0 (GMsg a u g'0). eauto. 
  move/Tr_reduce=> H4. move : H2. rewrite /Linear. 
  intros. apply : H2; eauto. 
- intros. have : stepG (GBranch a gs) (GBranch a GS) l0 (GBranch a gs'). eauto. move/Tr_reduce=>H3.
  move : H2.  rewrite /Linear. intros. eauto.  
Qed.



Lemma Tr_or : forall s g, Tr s g \/ ~ (Tr s g).
Proof.
elim. intros. auto. 
intros. case : g. 
- right. move => H2. inversion H2. 
- intros. case : (H s).  case (eqVneq a a0). move =>->. auto. 
  right. move => H2. inversion H2. apply (negP i). by apply/eqP. 
- intros. right. move => H2. inversion H2. done. 
  intros. case : (eqVneq a a0). 
 * move => ->. elim : l0. case : l H.  intros. left. auto. apply TRBranch with (n:=0). rewrite nth_nil. done. 
   intros. right. move => H2. inversion H2.  rewrite nth_nil in H1. inversion H1. 
   intros. case : H0.  
  ** intros. left. inversion a2. subst. apply TRBranch with (n:=n.+1). rewrite /=. done. 
  ** intros. case : (H a1). intros. left. apply TRBranch with (n:=0).  done. 
     intros. right. move => H2. apply b. inversion H2. subst.  case : n H1. rewrite /=. done.
     intros. apply TRBranch with (n:=n). done. 
 * move/eqP=>H2. right. move => H3. apply H2. inversion H3. done. 
Qed.



Definition app_Forall3 {P : gType -> gType -> gType -> Prop}{gs GS gs' : seq gType} (H : Forall3 P gs GS gs') := @Forall3_forall_n _ _ _ _ gs GS gs' SGEnd SGEnd SGEnd H.


Definition app_Forall3_def {P : gType -> gType -> gType -> Prop}{gs GS gs' : seq gType}  (H : Forall3 P gs GS gs') (H0 : P SGEnd SGEnd SGEnd) := @Forall3_forall_n_def _ _ _ _ gs GS gs' SGEnd SGEnd SGEnd H0 H.



Lemma reduce_condition : forall g G l g', stepG g G l g' -> forall aa a' a, Tr (aa++([::a])) G ->  
a' \in aa -> ~~in_action (ptcp_to a') (act_of_label l).  
Proof.
move => g G l g'. elim/stepG_ind2.
- intros. case : aa H H0; first done.  move => a1 l0. rewrite /=. intros. inversion H. subst. 
  inversion H2. contra_list. 
- intros.  case : aa H H0 H1; first done.  move => a1 l0. rewrite /=. intros. inversion H0. subst. 
  rewrite nth_nil in H3. inversion H3. contra_list.
- intros. case : aa H2 H3. done. move => a1 l1. rewrite cat_cons. intros. inversion H2. subst.
  move : H3. rewrite inE. move/orP=>[ /eqP ->  |  ]. done.  eauto. 
- intros. case : aa H2 H3. done. move => a1 l1. rewrite cat_cons. intros. 
  move : H3. rewrite inE. move/orP=>[ /eqP ->  |  ]. inversion H2.  subst. eauto.
  move : (app_Forall3 H0)=> []. intros. inversion H2.  subst.
  case Heq : (n < size gs). apply : a2. eauto. eauto. done. 
  rewrite nth_default in H4. inversion H4. contra_list. lia.
Qed.
Check TRBranch.
Definition TRBranchn {gs aa} n a (H : Tr aa (nth SGEnd gs n)) := @TRBranch a gs n aa H.
Check TRBranchn.
Arguments TRBranchn {_} {_} n.
Check TRBranchn.


Lemma deletion : forall g G l g', stepG g G l g' -> forall s, Tr s g' -> ~ Tr s G -> exists s0 s1, s = s0++s1 /\ Tr (s0++(act_of_label l)::s1) g /\ Tr (s0++([::act_of_label l])) G.
Proof. 
move => g G l g'. elim/stepG_ind2.
- intros. exists nil. exists s. rewrite /=. auto.
- intros. exists nil. exists s. rewrite /=. split;auto. split. apply TRBranch with (n:=n). 
  move : H0. rewrite (nth_def _ SGEnd) //=. apply TRBranch with (n:=0).  done. 
- intros. inversion H2. 
 * subst. exfalso. apply H3. done. 
 * subst. have : ~Tr aa G0.  move => H7. apply H3. auto. move => H7. 
   move : (H0 aa H6 H7)=> [] s0 [] s1 [] -> H8. exists (a::s0). exists s1. rewrite cat_cons. split;auto.  rewrite cat_cons. auto. case : H8. intros. rewrite cat_cons. auto. 
- intros. inversion H2. subst. 
 *  exists nil. exists nil. rewrite /=. exfalso. eauto. 
 * subst. move :  (@Forall3_forall_n _ _ _ _ gs GS gs' SGEnd SGEnd SGEnd H0).   
   move => [] Hall Hsize.
   have : ~Tr aa (nth SGEnd GS n). move => HH. apply H3. eauto. move => HH.
   case Heq : (n < size gs).
   move : (Hall n Heq aa H6 HH)=> [] s0 [] s1 [] -> [] HH0 HH1. 
   exists (a::s0). exists s1. rewrite /=. eauto. 
   rewrite nth_default in H6. inversion H6.  subst. rewrite nth_default in HH. done. 
   lia. lia. 
Qed.


Lemma split_list : forall A (l : seq A), l = nil \/ exists l' a, l = l'++([::a]).
Proof.
move => A. elim.
auto.  move => a l [] . move =>->. right.  exists nil. exists a. done. 
move => [] l' [] a0 ->. right. exists (a::l'). exists a0. done.
Qed.

Lemma Tr_app : forall l0 l1 G, Tr (l0++l1) G -> Tr l0 G.
Proof.
elim. rewrite /=. done.
move => a l IH l1 G. rewrite cat_cons. move => H. inversion H. 
- subst. constructor. eauto.  
- subst. apply TRBranch with (n:=n). eauto.
Qed.

Lemma last_eq : forall A (l0 l1 : seq A) x0 x1, l0 ++ ([::x0]) = l1 ++ ([::x1]) -> l0 = l1 /\ x0 = x1.
Proof.
move => A. elim.
case. rewrite /=. move => x0 x1. case. done.
move => a l x0 x1. rewrite /=. case. move =>-> H. apply List.app_cons_not_nil in H. done. 
rewrite /=. intros. case : l1 H0.  rewrite /=. case. move => _ /esym H1. apply List.app_cons_not_nil in H1. done. 
intros. move : H0.  rewrite cat_cons. case. intros. move : (H _ _ _ H1). case. intros. split. subst. done. done. 
Qed.


  

Lemma split_mask : forall A (l0 : seq A) x l1 m, size m = size (l0++x::l1) ->
mask m (l0 ++ x :: l1) =
  mask (take (size l0) m) l0 ++ (nseq (nth false m (size l0)) x) ++ mask (drop (size l0).+1 m) l1.
Proof.
move => A. elim. 
- rewrite /=. intros. rewrite take0 /=. case : m H. done. 
  intros. by  rewrite mask_cons /= drop0. 
- rewrite /=. intros. case : m H0.  done. rewrite /=. intros. 
  case : a0. rewrite cat_cons. f_equal. rewrite H //=. lia. 
  rewrite H //=. lia.
Qed.

Lemma add_sub : forall n1 n0, n0 = n0 + n1 - n1. 
elim.
lia. 
intros. lia. 
Qed.

Lemma contra1 : forall a l0, II a (act_of_label l0) -> ~~ in_action (ptcp_to a) (act_of_label l0) -> False.
Proof.
case. move => p p0 c []; rewrite /II /=;intros; apply : (negP H0);case : a H H0;move => p1 p2 c0 /eqP ->;by rewrite /=eqxx orbC.  
Qed.

Lemma contra2 : forall a l0, IO a (act_of_label l0) -> ~~ in_action (ptcp_to a) (act_of_label l0) -> False.
Proof.
case. move => p p0 c []; rewrite /IO /=;intros; apply : (negP H0);case : a H H0;move => p1 p2 c0 /eqP ->; by rewrite /= eqxx. 
Qed.

Lemma split_indep : forall s a0 a1 s2, InDep (s++a0::a1::s2) -> InDep (a0::a1::s2).
Proof.
elim. auto. rewrite /=. intros. apply H. inversion H0. subst. case : l H3 H0 H.  rewrite /=. intros. done.
rewrite /=. intros. case : H3. intros. apply List.app_cons_not_nil in H3. done. done.
Qed.

Lemma in_action_to : forall a, in_action (ptcp_to a) a.
Proof.
case. intros. by rewrite/= eqxx orbC.
Qed. 

Lemma in_action_from : forall a, in_action (ptcp_from a) a.
Proof.
case. intros. by rewrite/= eqxx.
Qed. 

Lemma cons23 : forall A  s0 s1 aa (a0 : A) a1,  a0 :: aa ++ [:: a1] = s0 ++ s1 -> s0 = nil /\ a0::aa++([:: a1]) = s1 \/ s1 = nil /\  a0::aa++([:: a1]) = s0 \/ exists s0' s1', s0 = a0::s0' /\ s1 = s1'++([::a1]) /\ s0' ++ s1' =  aa.
Proof.
move => A. elim.
move => s1 aa a0 a1. rewrite /=. move => <-. auto. 
rewrite /=. intros. case : H0. move => <-. case : aa. rewrite /=. case : s1. rewrite cats0. move => <-. auto. 
move => a2 l0. right. right. exists l. case : l H H0. rewrite /=. intros. exists nil. done. 
rewrite /=. intros. case : H0.  intros. apply List.app_cons_not_nil in H1. done. 
move => a2 l0. rewrite cat_cons. move/H. case. 
- case. move => -> <-. right. right. exists nil. exists (a2::l0). done. 
case. 
 - case. move => -> <-. auto. 
 - case.  move => x [] x1 [] -> [] -> H1. right. right. exists (a2::x). exists x1. rewrite /= H1. done. 
Qed.

Lemma InDep_app : forall l0 l1, InDep (l0 ++ l1) -> 1 < size l1 -> InDep l1.
Proof.
elim. rewrite /=. done.
move => a l IH l1. rewrite cat_cons. move => H. inversion H. subst.
case : l H2 H IH.  rewrite /=. move => <-. done. 
move => a0 l. rewrite cat_cons. case. move => <-. case : l.  case : l1. done. done. done. 
intros. subst. rewrite H1 in H3. auto. 
Qed.

Definition IO_II a0 a1 := IO a0 a1 || II a0 a1.

Lemma ind_aux : forall l a a0, path IO a (belast a0 l) -> II (last a (belast a0 l)) (last a0 l) -> IO_II a a0 && path IO_II a0 l.
Proof.
 elim.
- move => a a0.  rewrite /= /IO_II. move => _ ->.  by rewrite orbC.
- move => a l IH a0 a1. rewrite /=. move/andP=>[].  intros. rewrite /IO_II a2 /=.
  unfold IO_II in IH. apply/IH. done. done. 
Qed.

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


Inductive IO_seq : seq action -> Prop :=
 | IO_seq0 a b : IO a b ->  IO_seq ([::a; b])
 | IO_seq1 a b l : IO a b -> IO_seq (b::l) -> IO_seq (a::b::l).


Lemma apply_InDep_app : forall l l0 l1 , InDep l -> l = l0++l1 -> 1 < size l1 -> InDep l1.
Proof.
intros.  apply : InDep_app;auto. rewrite H0 in H. eauto. 
Qed.

Lemma OutDep_app : forall l0 l1, OutDep (l0 ++ l1) -> 1 < size l1 -> OutDep l1.
Proof.
elim. rewrite /=. done.
move => a l IH l1. rewrite cat_cons. move => H. inversion H. subst.
case : l H2 H IH.  rewrite /=. move => <-. done. 
move => a0 l. rewrite cat_cons. case. move => <-. case : l.  case : l1. done. done. done. 
intros. subst. rewrite H1 in H3. auto. 
Qed.

Lemma outdep0 : forall l0 l1, outdep (l0 ++ l1) -> if l0 is x::l0' then path IO_OO x l0' else true.
Proof.
rewrite /outdep. case;first done. 
move => a l l1. rewrite cat_cons. case : l;first done.  
move => a0 l. rewrite cat_cons. rewrite -cat_cons. rewrite cat_path. by move/andP=>[]. 
Qed.

Lemma nil_ll : forall A (l0 l1 : seq A), nil = l0 ++ l1 -> l0 = nil /\ l1 = nil.
Proof.
move => A. elim.
- case. done. done. 
- rewrite /=. done. 
Qed.

Check list_ind.


Lemma apply_OutDep_app : forall l l0 l1 , OutDep l -> l = l0++l1 -> 1 < size l1-> OutDep l1.
Proof.
intros.  apply : OutDep_app;auto. rewrite H0 in H. eauto. 
Qed.

Lemma delete_middle : forall a0 l0 a l1 a1 P, exists_depP (fun m => nth false m (size l0) = false) P a0 (l0 ++ a::l1) a1 ->
                      exists_dep P a0 (l0++l1) a1.
Proof.
intros. move : H => [] m [] H0 [] H1 H2. exists ((take (size l0) m)++(drop (size l0).+1 m)).
rewrite size_cat size_take size_drop H0 !size_cat /=. have : size l0 < size l0 + (size l1).+1 by lia.
move => H3. rewrite H3. split. lia. split;auto. move : H1. rewrite !split_mask //=. rewrite H2 /= mask_cat //=. 
by rewrite size_take H0 size_cat /= H3. 
Qed.


Lemma apply_linear : forall g s_tr a_p a0 s a1, Linear g -> Tr s_tr g -> s_tr = a_p++(a0::s++[::a1]) -> same_ch a0 a1 -> exists_dep InDep a0 s a1 /\ exists_dep OutDep a0 s a1.
Proof.
intros. rewrite H1 in H0. eauto. 
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

Lemma IO_II_in_action : forall a0 a1, IO_II a0 a1 -> in_action (ptcp_to a0) a1.
Proof.
move => a0 a1. rewrite /IO_II. move/orP=>[]. rewrite /IO. move/eqP=>->. apply in_action_from.
rewrite /II. move/eqP=>->. apply in_action_to.
Qed.

Lemma in_split : forall (A : eqType) l (x : A), x \in l -> exists l0 l1, l = l0 ++ x::l1.
Proof.
move => A. elim. done.
move => a l IH x. rewrite inE. move/orP=>[]. move/eqP=>->. exists nil. exists l. done. move/IH=> [] l0 [] l1 ->. exists (a::l0),l1. done. 
Qed. 


Lemma stepG_aux : forall g G l g', stepG g G l g' -> Linear g -> 
forall a0 aa a1, Tr (a0 :: aa ++ [:: a1]) g' -> same_ch a0 a1 -> exists_dep InDep a0 aa a1 /\ exists_dep OutDep a0 aa a1.
Proof.
move => g G l g'  Hstep  Lg a aa a1 HG Hch.
move : (label_linear Hstep Lg) =>LG. case : (Tr_or (a:: aa ++ ([:: a1])) G); first auto using (LG nil).
   move => Hnot.  
   move : (deletion Hstep HG Hnot)=> [] s0 [] s1 [] Heq [] Hg0 HG0.
   case : (cons23 Heq). 
   move => [] Hs0 Hs1;subst; simpl in *. have : Tr (([::act_of_label l]) ++ (a::aa) ++  ([::a1])) g. by  simpl. move => Hg0'.  apply : Lg. apply : Hg0'. done. 
   case; first ( move => [] Hs0 Hs1; subst; apply : (LG nil); simpl; eauto using Tr_app). 
   move => [] s0' [] s1' [] Hs0 [] Hs1 Heqaa. subst. simpl in *. 
   move : (@apply_linear _ _ nil a (s0' ++ (act_of_label l)::s1') a1 Lg Hg0).  (*get that original g contains in/out chains*)
   rewrite /= -!catA cat_cons. move => Hinout. move : (Hinout Logic.eq_refl Hch)=> [] Hin Hout. 
   rewrite  -cat_cons -[_::_]cat0s in HG0. (*make it ready to by used with LG*)
   split.
   ** move : Hin => [] m [] Hsize [] Hin _. (*InDep*)
      case Heqb : (nth false m (size s0')); last (apply : delete_middle; exists m; split;eauto). 
      move : Hin. rewrite split_mask //= Heqb /=.


      move/InDep_iff.
      have : (a :: (mask (take (size s0') m) s0' ++ act_of_label l :: mask (drop (size s0').+1 m) s1') ++ [:: a1]) =
             (((a :: (mask (take (size s0') m) s0' ++ [::act_of_label l])) ++ (mask (drop (size s0').+1 m) s1') ++ [:: a1])).
      by rewrite /= -!catA. move =>->.

      move/indep0. move/get_neigbor=> [] x_in []. intros.

      exfalso. apply/negP. eapply reduce_condition with (a':=x_in). apply : Hstep.   apply : HG0. 
      by rewrite mem_cat a0 orbC. auto using IO_II_in_action. 

  ** move : Hout => [] m [] Hsize [] Hout _. (*OutDep*) 
     case Heqb : (nth false m (size s0')); last (apply : delete_middle; exists m; split;eauto).
     move : Hout. rewrite split_mask //= Heqb /=.

     move/OutDep_iff.
      have : (a :: (mask (take (size s0') m) s0' ++ act_of_label l :: mask (drop (size s0').+1 m) s1') ++ [:: a1]) =
             (((a :: (mask (take (size s0') m) s0' ++ [::act_of_label l])) ++ (mask (drop (size s0').+1 m) s1') ++ [:: a1])).
      by rewrite /= -!catA. move =>->.

      move/outdep0. move/get_neigbor=> [] x_in []. intros. 
      rewrite /IO_OO in b. case : (orP b). intros.  exfalso. apply : negP. eapply reduce_condition with (a':= x_in). apply : Hstep.
      apply : HG0. by rewrite mem_cat a0 orbC. move : a2. rewrite /IO. move/eqP=>->. by  rewrite in_action_from. 

      rewrite /OO. move/andP=> [] /eqP _ HH0. 
      move : (in_split a0)=> [] l1 [] l2 Heq0. have : x_in \in [::] ++ a :: s0' by rewrite mem_cat a0 orbC. move => xin. Check reduce_condition. move : (@reduce_condition _ _ _ _ Hstep _ _ _ HG0 xin )=> not_act. 
  simpl in HG0. rewrite -cat_cons Heq0 -catA in HG0. 
      
        move : (LG _ _ _ _ HG0 HH0) => [] HInm HOutm. move : HInm => [] mm [] Hsizem  [] HInm _.
        move : HInm. move/InDep_iff. 
     case : (split_list (mask mm l2)). move=>->. rewrite /= /II. move/eqP=> HHeq.  exfalso. apply :negP. apply : not_act. 
        rewrite HHeq. apply/in_action_to.  
     move => [] l' [] a2 Heq2. rewrite Heq2 -!catA -cat_cons. move/indep1. rewrite /= andbC /=. move => HIO_II.  exfalso. apply : negP. 
     eapply reduce_condition with (a':=a2). apply Hstep. rewrite catA in HG0.  apply : HG0.
     rewrite mem_cat. apply/orP. right. rewrite inE. apply/orP. right. apply (@mem_mask  _ _ mm). rewrite Heq2.
     by rewrite mem_cat inE  eqxx orbC. auto using IO_II_in_action.  
Qed.


Lemma stepG_linear : forall g G l g', stepG g G l g' -> Linear g -> Linear g'.
Proof.
move => g G l g'. elim/stepG_ind2.  
- eauto using linear_sgmsg.
- eauto using linear_branch.  
- intros. rewrite /Linear. case.
 * eauto using stepG_aux. 
 * intros. simpl in H3. inversion H3;subst. apply : H0;eauto using linear_sgmsg. 
- intros. rewrite /Linear. case.
 * eauto using stepG_aux.
 * intros. simpl in H3. inversion H3;subst.
   move : (app_Forall3 H0)=>[] HH HH1.
   case Heq : (n < size gs).
  **  apply : HH;eauto using linear_branch.  
  ** rewrite nth_default in H6; last lia.  inversion H6. by move : H7=> /nil_ll  => [] []. 
Qed.

Print value.
(*Consider inductive global types and local types*)
Unset Elimination Schemes. Check seq.
CoInductive seType  : Type :=
  | SEEnd : seType  
  | SESend : ch -> value -> seType -> seType
  | SEReceive : ch -> value  ->  seType -> seType
  | SESelect : ch  -> seq seType  -> seType
  | SEBranch : ch -> seq seType -> seType.
Set Elimination Schemes.
 
(*Inductive se_eqF (R : seType -> seType -> Prop) : seType -> seType -> Prop :=
| seq_end : se_eqF R SEEnd SEEnd
| seq_send e0 e1 c v :  R e0 e1 -> se_eqF R (SESend c v e0) (SESend c v e1)
| seq_receive e0 e1 c v : R e0 e1 -> se_eqF R (SEReceive c v e0) (SEReceive c v e1)
| seq_select es0 es1 c : Forall2 R es0 es1 -> se_eqF R (SESelect c es0) (SESelect c es1)
| seq_branch es0 es1 c : Forall2 R es0 es1 -> se_eqF R (SEBranch c es0) (SEBranch c es1).

Notation se_eq := (paco2 se_eqF bot2).*)


Inductive part_of : gType -> ptcp -> Prop :=
| po_msg p a u g0 : in_action p a -> part_of (GMsg a u g0) p
| po_msg2 p g0 a u : part_of g0 p -> part_of (GMsg a u g0) p
| po_branch p a gs : in_action p a -> part_of (GBranch a gs) p
| po_branch2 gs p a g : In g gs -> part_of g p -> part_of (GBranch a gs) p.
Hint Constructors part_of.
(*
Inductive exists_g (P0 : action -> Prop) : gType -> Prop :=
| exists_msg0 a u g0 : P0 a -> exists_g P0 (GMsg a u g0)
| exists_msg1 a u g0 : exists_g P0 g0 -> exists_g P0 (GMsg a u g0)
| exists_branch0 a gs : P0 a -> exists_g P0 (GBranch a gs)
| exists_branch1 a g gs : In g gs -> exists_g P0 g -> exists_g P0 (GBranch a gs).



Lemma either : forall g P, exists_g P g \/ paco2 all_g bot2 (fun a => ~ P a) g.


*)

(*Maybe cp_notin is not necessary*)
Inductive co_projF (R : gType -> ptcp -> seType -> Prop) : gType -> ptcp -> seType -> Prop :=
| cp_msg_from g p0 e p1 c u : R g p0 e -> co_projF R (GMsg (Action p0 p1 c) u g) p0 (SESend c u e)
| cp_msg_to g p0 e p1 c u : R g p1 e -> co_projF R (GMsg (Action p0 p1 c) u g) p1 (SEReceive c u e)
| cp_msg_other g a e  u p : ~in_action p a -> R g p e -> co_projF R (GMsg a u g) p e
| cp_branch_from gs es p0 p1 c : Forall2 (fun g e => R g p0 e) gs es -> 
                                 co_projF R (GBranch (Action p0 p1 c) gs) p0 (SESelect c es)
| cp_branch_to gs es p0 p1 c : Forall2 (fun g e => R g p1 e) gs es -> 
                               co_projF R (GBranch (Action p0 p1 c) gs) p1 (SEBranch c es)
| cp_branch_other gs p e a :  ~~ in_action p a -> Forall (fun g => R g p e) gs -> 
                               co_projF R (GBranch a gs) p e
| cp_notin p g  : ~ part_of g p -> co_projF R g p SEEnd.
Hint Constructors co_projF.


Lemma co_proj_mono : monotone3 co_projF.
Proof.
move => x y. intros. inversion IN;subst;eauto.
apply/cp_branch_from. induction H;auto.  
apply/cp_branch_to. induction H;auto. 
apply/cp_branch_other. done. induction H0;auto. 
Qed.

Hint Resolve co_proj_mono : paco.
Notation  co_proj := (paco3 co_projF bot3).

(*Definition p0 := Ptcp 0.
Definition p1 := Ptcp 1.
Definition c := Ch 0.
Definition act := Action p0 p1 c.
Definition v := VSeqSort nil.

CoFixpoint sg_rec := GMsg act v sg_rec.
CoFixpoint es_rec := SESend (Ch 0) v es_rec.

Definition frob g := 
match g with 
| SGEnd => SGEnd 
| GMsg a u g => GMsg a u g
| GBranch a gs => GBranch a gs
end.

Definition frob2 g := 
match g with 
| SEEnd => SEEnd
| SESend a u g => SESend a u g
| SEReceive a u g => SEReceive a u g
| SESelect c es => SESelect c es
| SEBranch c es => SEBranch c es
end.

Lemma unfold_sg : sg_rec  = frob sg_rec.
destruct sg_rec. done. done. done.
Qed.

Lemma unfold_es : es_rec = frob2 es_rec.
destruct es_rec; done. 
Qed.
Example test2 : co_proj sg_rec p0  es_rec.
pcofix CIH.
rewrite unfold_sg unfold_es.  simpl. pfold. constructor. right.  done. 
Qed.*)

From mathcomp Require Import finmap.

Open Scope fmap_scope.
Definition is_full_proj (d : {fmap ptcp -> seType}) g (P : ptcp -> Prop) := 
(forall p e, P p -> co_proj g p e -> d.[? p] = Some e) /\ (forall p, ~ P p -> d.[? p] = None).

Inductive rec_red : seType -> (ch * (value + nat)) -> seType -> Prop :=
| rr_msg c v e0  : rec_red (SEReceive c v e0) (c, inl v) e0
| rr_eb n es c : n < size es -> rec_red (SEBranch c es) (c, inr n) (nth SEEnd es n).
Hint Constructors rec_red.

Inductive send_red : seType ->  (ch * (value + nat))  -> seType -> Prop :=
| sr_msg c v e0  : send_red (SESend c v e0) (c, inl v) e0
| sr_msg0 c c' v e0 e0' l ann : send_red e0 l e0' ->  c <> c' -> send_red (SESend c v e0) (c', ann) (SESend c v e0')
| sr_eb n es c  : n < size es -> send_red (SESelect c es) (c, inr n) (nth SEEnd es n)
| sr_eb0 es0 es1 c c' ann : Forall2 (fun e0 e1 => send_red e0 (c',ann) e1) es0 es1 -> c <> c' ->  send_red (SESelect c es0) (c',ann) (SESelect c es1).
Hint Constructors send_red.

(*Remove d'*)
Inductive ctx_red : {fmap ptcp -> seType} -> (action * (value + nat)) -> {fmap ptcp -> seType} -> Prop :=
| ctx_red_comm (d d' : {fmap ptcp -> seType})  p0 p1 c e0 e0' e1 e1' ann : 
                 d.[? p0] = Some e0 -> d'.[? p0] = Some e0' ->  
                 d.[? p1] = Some e1 -> d'.[? p1] = Some e1'  -> 
                 send_red e0 (c, ann) e0' -> rec_red e1 (c,ann) e1' -> 
                 (forall p, p \notin [:: p0;p1] ->  d.[? p] = d'.[? p]) ->
                 ctx_red d (Action p0 p1 c, ann) d'.

Definition label_change l :=
match l with 
| LU a u => (a,inl u)
| LN a n => (a,inr n)
end.

Lemma end_no_ptcp : forall p,  ~ part_of SGEnd p.
Proof.
intros. move => H. inversion H.
Qed.


Inductive non_refl (P : gType -> Prop) : gType -> Prop :=
| nr_end : non_refl P SGEnd
| nr_msg a u g0 : ptcp_from a <> ptcp_to a -> P g0 -> non_refl P (GMsg a u g0)
| nr_branch a gs : ptcp_from a <> ptcp_to a -> Forall P gs -> non_refl P (GBranch a gs).
Hint Constructors non_refl.

Lemma non_refl_mono : monotone1 non_refl.
Proof.
move => x y. intros. inversion IN;auto. constructor. done. subst. induction H0;auto. 
Qed.

Hint Resolve non_refl_mono : paco.

Definition Coherent g := Linear g /\ (forall p, exists e, co_proj g p e) /\ paco1 non_refl bot1 g.

Definition ptcp_of_act a := let : Action p0 p1 _ := a in p0::p1::nil.

(*Fixpoint ptcps_of_g (g : gType) := 
match g with 
| GMsg a _ g0 => (ptcp_of_act a)++(ptcps_of_g g0)
| GBranch a gs => (ptcp_of_act a)++flatten (map ptcps_of_g gs)
| GRec g0 => ptcps_of_g g0
| _ => nil
end.

Lemma ptcp_in_action : forall p a,  p \in ptcp_of_act a = in_action p a.
Proof.
intros. case : a. intros. by  rewrite /= !inE.
Qed.*)


Lemma msg_cont_proj : forall a p u g e, (ptcp_from a) <> (ptcp_to a) -> co_proj (GMsg a u g) p e -> exists e', (if p == (ptcp_from a) then e = SESend (action_ch a) u e' else if p == (ptcp_to a) then e = SEReceive (action_ch a) u e' else e = e')  /\ co_proj g p e'.
Proof.
intros.  punfold H0. inversion H0;subst.    
- rewrite /= eqxx. inversion H6. exists e0. split. done. auto. done.
- rewrite eqxx.  case : (eqVneq p p2) H6 H. move => ->. done. intros. inversion H6. eauto. done. 
- exists e. destruct a. simpl in H6. move : H6. move/negP.  rewrite negb_or. move/andP=>[]. rewrite -!eqbF_neg. move/eqP=>-> /eqP=> ->. 
  inversion H7. eauto. done.
- exists SEEnd. have : ~ in_action p a. move => H2. apply H1. auto. 
  destruct a. simpl. move/negP. rewrite negb_or. move /andP=>[].  rewrite -!eqbF_neg. move /eqP=>-> /eqP ->. 
  split;auto. pfold. apply cp_notin. move => H2. apply H1.  apply po_msg2. auto.  
Qed.

Lemma msg_cont_other : forall p p1 p2 c0 u g0 e_big, p1 <> p2 -> p \notin [:: p1; p2] -> co_proj (GMsg (Action p1 p2 c0) u g0) p e_big ->  co_proj g0 p e_big.
Proof.
intros. have : ptcp_from (Action p2 p3 c0) <> ptcp_to (Action p2 p3 c0). done. intros.
move : (msg_cont_proj x H1)=> [] e'. move : H0. rewrite /= !inE negb_or. move/andP=>[]. rewrite -!eqbF_neg. repeat move/eqP=>->.
by move=> [] ->.
Qed.

Lemma part_of_from : forall p p2 c0 u g0 , part_of (GMsg (Action p p2 c0) u g0) p.
Proof.
intros. constructor. by rewrite /= eqxx. 
Qed.


Lemma part_of_to : forall p p2 c0 u g0 , part_of (GMsg (Action p p2 c0) u g0) p2.
Proof.
intros. constructor. by rewrite /= eqxx orbC. 
Qed.

Hint Resolve part_of_from part_of_to.


(*Fixpoint all_ind_g (P : action -> bool) g := 
match g with 
| GEnd => true 
| GMsg a u g0 => P a && all_ind_g P g0
| GBranch a gs => P a && all (all_ind_g P) gs 
| GRec g => all_ind_g P g
| GVar _ => true 
end.

Inductive all_g (R : (action -> Prop) -> gType -> Prop) (P0 : action -> Prop) : gType -> Prop :=
| all_end : all_g R P0 SGEnd
| all_msg a u g0 : R P0 g0 -> P0 a -> all_g R P0 (GMsg a u g0)
| all_branch a gs : Forall (R P0) gs -> all_g R P0 (GBranch a gs).*)





Lemma part_of_or : forall g p, (part_of g p) \/ (~ part_of g p).
Proof. 
Admitted.


Lemma non_refl_msg : forall p p2 c0 u g0, paco1 non_refl bot1 (GMsg (Action p p2 c0) u g0) -> p <> p2.
Proof.
intros. punfold H. inversion H. subst. simpl in H2. done.
Qed.


Lemma sg_to_se : forall g l g' d d',  step g l g'  -> 
Coherent g -> is_full_proj d g (fun p => part_of g p) -> 
 is_full_proj d' g' (fun p => part_of g p) -> ctx_red d (label_change l) d'.
Proof.
move => g l g' d d'. elim/step_ind; intros; rewrite /=.
- unfold Coherent in H. destruct H,H2. case : a H H0 H1 H2 H3.  intros. move : (H2 p)  (H2 p2)=> [] ef Hf [] et Ht.
  have : ptcp_from (Action p p2 c0) <> (ptcp_to (Action p p2 c0)). punfold H3.  inversion H3. by simpl in*. intros. 
  move : (msg_cont_proj x Hf). rewrite /= eqxx. move => [] ef' [] Hef' Hprojef'.
  move : (msg_cont_proj x Ht). rewrite /= eqxx. have : p2 == p = false. simpl in x.  apply/eqP. 
  move => HH. apply x. subst. done. move=>->. move => [] et' [] Het' Hprojet. unfold is_full_proj in *.
  destruct H0,H1.  
  eapply ctx_red_comm with (e0:= ef)(e1:=et)(e0':= ef')(e1':=et');subst;auto.  
  rewrite /=.  intros.  move : (part_of_or (GMsg (Action p p2 c0) u g0) p3)=>[ HH | HH].
 * move : (H2 p3)=> [] e_big eProj. erewrite H0. erewrite H1. f_equal. done. 
   apply : msg_cont_other. 2: { apply : H6. }. 
   apply : non_refl_msg. apply : H3.  apply eProj. done.  done.
 * intros.  rewrite H4 //= H5 //=. 
- unfold Coherent in H0. destruct H0, H3. case : a H H0 H1 H2 H3 H4.  intros. move : (H3 p)  (H3 p2)=> [] ef Hf [] et Ht.
  have : ptcp_from (Action p p2 c0) <> (ptcp_to (Action p p2 c0)). punfold H4.  inversion H4. by simpl in*. intros. 
  move : (msg_cont_proj x Hf). rewrite /= eqxx. move => [] ef' [] Hef' Hprojef'.
  move : (msg_cont_proj x Ht). rewrite /= eqxx. have : p2 == p = false. simpl in x.  apply/eqP. 
  move => HH. apply x. subst. done. move=>->. move => [] et' [] Het' Hprojet. unfold is_full_proj in *.
  destruct H0,H1.  
  eapply ctx_red_comm with (e0:= ef)(e1:=et)(e0':= ef')(e1':=et');subst;auto.  
  rewrite /=.  intros.  move : (part_of_or (GMsg (Action p p2 c0) u g0) p3)=>[ HH | HH].
 * move : (H2 p3)=> [] e_big eProj. erewrite H0. erewrite H1. f_equal. done. 
   apply : msg_cont_other. 2: { apply : H6. }. 
   apply : non_refl_msg. apply : H3.  apply eProj. done.  done.
 * intros.  rewrite H4 //= H5 //=. 
Admitted.


Lemma Unroll_contractive : forall g gs, GUnroll g gs -> contractive g.
Proof.
move => g gs. unfold GUnroll. intros. punfold SH. UnUnU move : H. elim/SUnravel_ind2. induction H;auto. elim.

Lemma step_goal : forall g  gs gs' l,  step gs l gs'  -> GUnroll g gs -> exists g', GUnroll g' gs' /\ stepi g l g'.
Proof.
move => g g' gs gs'. elim. 
- intros. unfold GUnroll in H. punfold H. remember (mu_height g). elim : n  g Heqn H. 
 * intros. inversion H;subst. exists g1. split.  pfold. done. done. done. 
 * intros. inversion H0;subst. exists g1. split. done. done. 
  simpl in Heqn. inversion Heqn. pclearbot. punfold H1. rewrite -(@mu_height_subst g1 (GRec g1) 0) in H3.  move : (H _ H3 H1)=> [] g'' []. intros. exists g''. split. done.  apply GRI_rec. done.  Print contractive_i. done.
  intros. subst. pclearbot. apply H2. induction H. 
 * 
unfold GUnroll.  elim. 
- intros. punfold H. inversion H;subst. 
 * H0 H1. intros. induction H.  elim : H. 
- intros.
unfold GUnroll. intros. split. intros. induction H1. 
-
punfold H. elim : H.
- intros. inversion H.
- intros.
Lemma step_spec : forall gs l gs', step gs l gs' -> exists g g', GUnroll g gs /\ GUnroll g' gs' /\ step gs l gs'.


Lemma stepi_spec : forall g l g', stepi g l g' -> exists gs gs', GUnroll g gs /\ GUnroll g' gs' /\ step gs l gs'.
Proof.
move => g l g'.  elim. 
- intros. rewrite /GUnroll in H,H0.  punfold H. inversion H. subst. punfold H0.  apply/unroll_uniq. apply : H5. apply : H0. done. inversion H5;subst. 
intros. elim : H.
- intros.
(*Error in endpoint type, used mysort instead of value*)


Print ptcp.
Check obind. Check ESelect. Check EReceive. Check ERec. Check nth. Check map.
Fixpoint project n (g : gType) {struct g} :  endpoint :=
match g with 
| GEnd => EEnd
| GMsg (Action (Ptcp n0) (Ptcp n1) c) u g0 => if n0 == n then ESend c u (project n g0)
                                             else if n1 == n then EReceive c u (project n g0)
                                             else project n g0
| GBranch (Action (Ptcp n0) (Ptcp n1) c) gs =>if n0 == n then ESelect c (map (project n) gs)
                                             else if n1 == n then EBranch c (map (project  n) gs)
                                             else match gs with | nil => EEnd | g'::_ => project n g' end
| GVar n => EVar n
| GRec g0 => match project n g0 with 
            | EEnd => EEnd 
            | e0 => ERec e0
            end
end.
Locate flat_map.


Definition pid g := undup (ptcps_of_g g).
 Check filter.

Definition same_projection_aux n gs := exists e, Forall (fun g => project n g = e) gs.


Fixpoint Forall' {A : Type} (P : A -> Prop) l : Prop  :=
match l with 
| nil => True 
| a::l' => P a /\ (Forall' P l')
end.


Fixpoint same_proj g {struct g} :=
let fix proj_aux gs :=  
match gs with 
| nil => True 
| a::l' => same_proj a /\ (proj_aux l')
end in
match g with 
| GMsg _ _ g0 => same_proj g0
| GBranch a gs => (forall n, n \notin (ptcps_of_act a) -> exists e,  Forall' (fun g => project n g = e) gs) /\ proj_aux gs
| GRec g0 => same_proj g0
| _ => True
end.

Fixpoint acts_of_g g := 
match g with 
| GMsg a _ g0 => a::(acts_of_g g0)
| GBranch a gs => a::(flatten (map acts_of_g gs))
| GRec g => acts_of_g g 
| _ => nil
end.

Definition no_refl_action g := forall a, a \in (acts_of_g g) -> ptcp_from a != ptcp_to a.

Definition coherent g := no_refl_action g /\ same_proj g /\ (exists sg, GUnroll g sg /\ Linear sg). (*Maybe more requirements, boundness/contractiveness? No, that is implicit in the fact that g can be unrolled to sg*)

(*Next steps continue p.23*)

(*Not guarded co-recursive call, consequence of deletion in projection*)
(*CoFixpoint project (sg : gType) (n : nat) :  seType :=
match sg with 
| SGEnd => SEEnd
| GMsg (Action (Ptcp n0) (Ptcp n1) c) u g0 => if n0 == n then (SESend c u (project g0 n))
                                              else if n1 == n then (SERec c u (project g0 n))
                                              else project g0 n
| _ => SBot
end.*)






















(*represent local type semantics using sets of local types and sets of queues*)


(*
Definition project2_forall (A B: Type) (R : A -> B -> Type) (l0 : seq A) (l1 : seq B) (H : Forall2 R l0 l1) :=
match H with
| Forall2_nil=> nil
| Forall2_cons _ G _ GS _ _ => G::GS
end.


Fixpoint G_of_step sg l sg'  (H : step sg l sg') : gType  := 
match H with 
| GR1 a u _ => GMsg a u SGEnd
| GR2 a n _ _ _ => GBranch a nil
| GR3 a u _ _ _ H' _ => GMsg a u (G_of_step H')
| GR4 a _ gs _ H' _  => GBranch a (project2_forall H')
end.

Check stepG_ind.
 



Fixpoint trace_of_step sg l sg'  (H : step sg l sg') : seq (seq label) := 
match H with 
| GR1 a u _ => [::[::LU a u]]
| GR2 a n _ _ _ => [::[::LN a n]]
| GR3 a u _ _ _ H' _ => map (cons (LU a u)) (trace_of_step H')
| GR4 a _ gs _ _ _ _ _ H' _  => flatten (mkseq (fun i => map (cons (LN a i)) (trace_of_step (H' i))) (size gs))
end.

Fixpoint reduce (ls : seq label) (sg : gType)  {struct ls} : option gType :=
match sg,ls with 
| _,nil => Some sg
| GMsg a u sg', (LU a' u')::nil => if (a == a') && (u == u') then Some sg' else None
| GBranch a sgs, (LN a' n)::nil => if (a == a') then nth_error sgs n else None
| GMsg a u sg', (LU a' u')::ls' => if (a == a') && (u == u') then match reduce ls' sg' with
                                                                  | Some sg'' => Some (GMsg a u sg'')
                                                                  | None => None
                                                                 end
                                                             else None
| GBranch a sgs, (LN a' n)::ls' => if a == a' then match nth_error sgs n with 
                                                   | Some sg' => match reduce ls' sg' with
                                                                 | Some sg'' => Some (GBranch a (set_nth SGEnd sgs n sg''))
                                                                 | None => None
                                                                 end
                                                   |  None => None
                                                   end
                                              else None
| _,_ => None
end.
Check foldr.
Definition rreduce lls sg := foldr (fun t r => obind (reduce t) r  ) (Some sg) lls.

(*Fixpoint repeat_reduce lls sg :=
match lls with 
 | nil => Some sg
 | ls::lls' => match reduce ls sg with 
             | Some sg' => repeat_reduce lls' sg' 
             | None => None 
             end
end.*)

Definition wf_actions ls :=
match ls with
| nil => true 
| l::ls' => let receivers := map ptcp_to (belast l ls')
          in all (fun r => ~~(in_action r (last l ls'))) receivers
end.

Lemma wf_actions_cons : forall aa a,  ~~(in_action (ptcp_to a) (last a aa)) ->  wf_actions aa -> wf_actions (a::aa).
Proof.
elim. 
- move => a. rewrite /=. done. 
- move => a l IH a0.  rewrite /=. intros. apply/andP. split. done. done. 
Qed.


Definition wf_labels ls := wf_actions (map act_of_label ls).

Lemma wf_labels_cons : forall l0 l1 ls,  ptcp_to (act_of_label l0) \notin last l1 ls ->  wf_labels (l1::ls) -> wf_labels (l0::l1::ls).
Proof. Admitted.


Lemma step_reduce_aux : forall lls a u g , rreduce (map (fun ls => (LU a u) :: ls) lls) (GMsg a u g) = omap (GMsg a u) (rreduce lls g).
Proof. Admitted.

Lemma step_reduce_branch : forall lls a gs n d, n < size gs -> rreduce (map (cons (LN a n)) lls) (GBranch a gs) = omap (fun g' => GBranch a (set_nth d gs n g')) (rreduce lls (nth d gs n)).
Proof. Admitted.


Lemma nth_error_zip : forall (gs gs' : seq gType) (P : gType -> gType -> Prop), (forall i g g',
       nth_error gs i = Some g ->
       nth_error gs' i = Some g' -> P g g')  -> Forall2 P gs gs'.
Proof. Admitted.

Lemma repeat_reduce_app :  forall lls0 lls1 sg, rreduce (lls0 ++ lls1) sg = obind (rreduce lls1) (rreduce lls0 sg).
Proof. Admitted.

Lemma step_reduce : forall sg l sg' (H : step sg l sg'), rreduce (trace_of_step H) sg = Some sg'.
Proof. 
move => sg l sg'. elim.
- intros. by rewrite /= !eqxx /=. 
- intros. by rewrite /= !eqxx /= e. 
- move => a u l0 g1 g2 s H i. rewrite /=.
 by rewrite step_reduce_aux H. 
- move => a l0 gs gs' d d' Heq Hstepd IHd Hstep IH H. rewrite /= /mkseq. 

  suff: (rreduce [seq LN a i :: y | i <- iota 0 (size gs), y <- trace_of_step (Hstep i)] (GBranch a gs) = Some (GBranch a gs')). 

 rewrite step_reduce_branch.
  elim : gs Heq Hstep IH. 
 * case : gs'; last done. move => _ Hstep Hrec. rewrite /=. done. 
 * move => a1 l1 IH. case : gs' IH ;first done.
   move => a2 l2 IH. case. intros.  rewrite /=. 
   rewrite repeat_reduce_app. rewrite step_reduce_branch.  
   move : (IH0 0). rewrite /=. move => ->. rewrite /=.
 move : (nth_error_zip IH). 
  clear IH. rewrite {1}/reduce_prop.  elim : gs gs' Heq Hstep. 
 * case; last done. rewrite /=. move => _ H. 
   rewrite /reduce_prop. move => _. exists nil. rewrite /=. split;auto. split;auto.
   move => ls. rewrite in_nil. done.
 * move => sg0 sgs0 IH []. rewrite /=.  done.
   move => sg1 sgs1. rewrite /=. case. move => Heq Hstep [] Hred_top Hred_rest. 
   rewrite /reduce_prop.
   intros.  move => Print List.Forall. rewrite /List.Forall.
 elim :  Search nth_error.


Definition reduce_prop l sg sg' := exists lls, repeat_reduce lls sg = Some sg' /\ all wf_labels lls /\ (forall ls, ls \in lls -> exists l' ls', ls = l'::ls' /\ last l' ls' = l).

Lemma step_reduce : forall sg l sg', step sg l sg' -> reduce_prop l sg sg'.
Proof. 
move => sg l sg'. elim.
- intros. exists ([::[::(LU a u)]]). rewrite /= !eqxx /=. split;auto. split;auto.
  move => ls. rewrite inE. move/eqP => [] ->. exists (LU a u). exists nil. auto.
- intros. exists ([::[::(LN a n)]]). rewrite /= eqxx /=. rewrite H. split; auto. split;auto.
  move => ls.  rewrite inE. move/eqP => [] ->. exists (LN a n). exists nil. auto.
- move => g1 l0 g2 a u H [] lls [] H1 [] H2 H3 H4. 
  exists (map (fun ls => (LU a u)::ls) lls). split.
 * rewrite step_reduce_aux. rewrite H1. done.   
 * split. 
  ** apply/allP. move => a_ls Hin. move : (mapP Hin)=> [] ls Hin2. 
     case : a_ls Hin. done. move => a0 ls' Hin. case. move => -> ->. 
     case : ls Hin2. done. move => a1 l1 Hin2. apply wf_labels_cons. rewrite /=. 
     move : (H3 _ Hin2) => [] l' [] ls'' [] [] -> -> ->. done. 
     apply/(allP H2). done.
  ** move => ls /mapP. move => [] ls' Hin'. case : (H3 _ Hin') => x [] ls'' [] ->. 
     exists (LU a u). exists (x::ls''). split;auto. 
- move => a l0 gs gs' Heq Hstep IH Hrec. move : (nth_error_zip IH). 
  clear IH. rewrite {1}/reduce_prop.  elim : gs gs' Heq Hstep. 
 * case; last done. rewrite /=. move => _ H. 
   rewrite /reduce_prop. move => _. exists nil. rewrite /=. split;auto. split;auto.
   move => ls. rewrite in_nil. done.
 * move => sg0 sgs0 IH []. rewrite /=.  done.
   move => sg1 sgs1. rewrite /=. case. move => Heq Hstep [] Hred_top Hred_rest. 
   rewrite /reduce_prop.
   intros.  move => Print List.Forall. rewrite /List.Forall.
 elim :  Search nth_error.


Lemma step_reduce : forall sg l sg', step sg l sg' -> exists lls, repeat_reduce lls sg = Some sg' /\ all wf_labels lls /\ (forall ls, ls \in lls -> exists l' ls', ls = l'::ls' /\ last l' ls' = l).  
Proof. 
move => sg l sg'. elim.
- intros. exists ([::[::(LU a u)]]). rewrite /= !eqxx /=. split;auto. split;auto.
  move => ls. rewrite inE. move/eqP => [] ->. exists (LU a u). exists nil. auto.
- intros. exists ([::[::(LN a n)]]). rewrite /= eqxx /=. rewrite H. split; auto. split;auto.
  move => ls.  rewrite inE. move/eqP => [] ->. exists (LN a n). exists nil. auto.
- move => g1 l0 g2 a u H [] lls [] H1 [] H2 H3 H4. 
  exists (map (fun ls => (LU a u)::ls) lls). split.
 * rewrite step_reduce_aux. rewrite H1. done.   
 * split. 
  ** apply/allP. move => a_ls Hin. move : (mapP Hin)=> [] ls Hin2. 
     case : a_ls Hin. done. move => a0 ls' Hin. case. move => -> ->. 
     case : ls Hin2. done. move => a1 l1 Hin2. apply wf_labels_cons. rewrite /=. 
     move : (H3 _ Hin2) => [] l' [] ls'' [] [] -> -> ->. done. 
     apply/(allP H2). done.
  ** move => ls /mapP. move => [] ls' Hin'. case : (H3 _ Hin') => x [] ls'' [] ->. 
     exists (LU a u). exists (x::ls''). split;auto. 
- move => a l0 gs gs' g g' Hstep IH Hrec. move : (nth_error_zip IH). 
 elim :  Search nth_error.


Lemma linear_reduce : forall sg ls sg', Linear sg -> reduce sg ls = Some sg' -> wf_labels ls -> Linear sg'.
Proof. Admitted.

Lemma linear_repeat_reduce_cons : forall l sg sg' a,  repeat_reduce (a :: l) sg = Some sg' -> exists sg'', reduce sg a = Some sg'' /\ repeat_reduce l sg'' = Some sg'.
Proof.
move => l sg sg' a.  rewrite /=. destruct (reduce sg a). intros. exists s. auto.
done. 
Qed.

Lemma linear_repeat_reduce : forall lls sg sg', Linear sg -> repeat_reduce sg lls = Some sg' -> all wf_labels lls -> Linear sg'.
Proof. 
elim. 
- rewrite /=. intros. injection H0. move=><-. done. 
- intros. move : (linear_repeat_reduce_cons H1)=> [] x []. intros. move : H2.  rewrite /=. move/andP=>[]. intros. move : (linear_reduce H0 a0 a1). intros. apply :H. apply linear_reduce0. apply b. apply b0. 
Qed.

Lemma linear_step : forall sg l sg', step sg l sg' -> Linear sg -> Linear sg'.
Proof. 
intros.  move : (step_reduce H) =>[] x [H2 H3]. apply/linear_repeat_reduce.  apply H0. apply H2. 
apply H3. 
Qed.







Fixpoint end_list sgs :=
match sgs with 
| nil => true 
| GEnd::sgs' => end_list sgs'
| _::sgs' => false
end.

Fixpoint reduce (sg : gType) (g : gType) {struct g} :=
let fix reduce_list sgs gs {struct gs} := 
match sgs,gs with 
 | nil,nil => Some nil
 | sg::sgs',g::gs' =>  obind (fun sgs'' => omap (fun sg' => sg'::sgs'' )  (reduce sg g)) (reduce_list sgs' gs')
 | _,_ => None 
end
in
match sg , g with 
| _,GEnd => Some sg
| GMsg a u sg, GMsg a' u' GEnd => if (a == a') && (u == u') then Some sg else None
| GMsg a u sg, GMsg a' u' g' => if (a == a') && (u == u') then omap (fun sg' => GMsg a u sg') (reduce sg g') else None
| GBranch a sgs, GBranch a' gs  => if a == a' then 
                                    if end_list gs then nth_error sgs (size gs)
                                                   else omap (fun sgs' => GBranch a sgs') (reduce_list sgs gs) 
                                  else None
| _,_ => None
end.

(*receiver constranint boolean predicate on labels
 main lemma. if there is a normal reduction, there exists indcutive global types with receiver constraint s.t we can do the same reduction. By linearity and receiver constraint on this label, we know its leaves aren't used in any in/output chains. Next steps?
 A sub type relation. The bigger type contains all paths that are in the smaller type
 Define next as a partial function, next g a i, nexts g ais

 How do I connect all this to acturaly show the reduced G is linear?
 we can do the same red*)



(*Change ≺ to sequence of labels. Normal reduction implies a sequence of computation reductions that each have receiver constraint. Suffices to show that such a computation reduction preserves chains. Only affected chains are prefixes of ≺ sequence. If reduction sequence = ≺ sequence, the channel condition doesn't hold. If reduction sequence is a prefix, there exists a bitmask such that ≺ sequence such that chains are preserved *)
Lemma red_lin : forall g g_l g', Linear g -> reduce g g_l = Some g' -> Linear g'.
Proof. Admitted.





(*Besides well formedness we can also define input dependency and output dependency on rose trees
 and transform the tricky statement about k <> k' in the proof to there not existing any input or output dependency
 in the well formed rose tree that was used to reduce with because of the receiver criteria*)
Inductive wf_r (A : Type) : rose A -> A -> Prop :=
| wf_r0 a : wf_r (Rose a nil) a
| wf_r1 rs a1 a : (forall r, In r rs -> wf_r r a1) ->  wf_r (Rose a rs) a1.

Check nth_error.

Inductive reduce : gType -> rose label -> gType -> Prop :=
| GMsg0 a u g0 : reduce (GMsg a u g0) (Rose (LU a u) nil) g0
| GMsg1 a u g0 g0' r' : reduce g0 r' g0' -> reduce (GMsg a u g0) (Rose (LU a u) ([::r'])) (GMsg a u g0')
| GBranch0 a n g0 gs g: List.nth_error gs n = Some g -> reduce (GBranch a gs) (Rose (LN a n) nil) g0
| GBranch1 a a' rs gs  gs' n g r g' : (forall r, In r rs -> wf_r r a')  ->  (forall i, nth_error gs i = Some g -> nth_error rs i = Some r -> nth_error gs' i = Some g' -> reduce g r g' ) -> reduce (SGBranch a gs) (Rose (LN a n) rs) (SGBranch a gs').



Fixpoint reduce (g : gTypey) (r : rose label) :=
match g,r with 
| GMsg a u g0, Rose (LU a' u') nil => if a == a' && u == u' then Some g0 else None
| GMsg a u g0, Rose (LU a' u') ([r']) => if a == a' && u == u' then omap (fun g' => GMsg a u g') (reduce g0 r')
| SGBranch a gs, Rose (LN a' n) nil => if a == a' then List.nth_error gs n
| SGBranch a gs, Rose (LN a' n) rs => if a == a' && leq (size gs) (size rs) then 

*)
