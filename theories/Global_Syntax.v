(*Require Export Dep.fintype. *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import zify.

From Equations Require Import Equations.
From mathcomp Require Import fintype.
From deriving Require Import deriving. 
Require Import Dep.Syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition nat_of_ptcp (p : ptcp) := let: Ptcp n := p in n.
Canonical ptctp_newType := Eval hnf in [newType for nat_of_ptcp]. 
Definition ptcp_eqMixin := [eqMixin of ptcp by <:]. 
Canonical ptcp_eqType := Eval hnf in EqType ptcp ptcp_eqMixin.
Definition ptcp_choiceMixin := [choiceMixin of ptcp by <:].
Canonical ptcp_ChoiceType := Eval hnf in ChoiceType ptcp ptcp_choiceMixin.
Definition ptcp_countMixin := [countMixin of ptcp by <:].
Canonical ptcp_countType := CountType ptcp ptcp_countMixin.


Definition nat_of_ch (c : ch) := let: Ch n := c in n.
Canonical ch_newType := Eval hnf in [newType for nat_of_ch].
Definition ch_eqMixin := [eqMixin of ch by <:]. 
Canonical ch_eqType := Eval hnf in EqType ch ch_eqMixin. 
Definition ch_choiceMixin := [choiceMixin of ch by <:].
Canonical ch_ChoiceType := Eval hnf in ChoiceType ch ch_choiceMixin.
Definition ch_countMixin := [countMixin of ch by <:].
Canonical ch_countType := CountType ch ch_countMixin.

Definition prod_of_action (a : action) := let '(Action p0 p1 c) := a in (p0,p1,c). 
Definition action_indDef := [indDef for action_rect].
Canonical action_indType := IndType action action_indDef.
Definition action_eqMixin := [derive eqMixin for action].
Canonical action_eqType := EqType action action_eqMixin.
Definition action_choiceMixin := [derive choiceMixin for action].
Canonical action_choiceType := ChoiceType action action_choiceMixin.
Definition action_countMixin := [derive countMixin for action].
Canonical action_countType := CountType action action_countMixin.

Definition ptcp_from (a : action) := let : Action p0 _ _ := a in p0.
Definition ptcp_to (a : action) := let : Action _ p1 _ := a in p1.
Definition action_ch (a : action) := let : Action _ _ c := a in c.


(*It is hard to give a mutually inductive nested induction principle*)
(*
Scheme gType_ind := Induction for gType Sort Prop 
with value_ind := Induction for value Sort Prop 
with mysort_ind := Induction for mysort Sort Prop 
with endpoint_ind := Induction for endpoint Sort Prop.

Check gType_ind.
Combined Scheme gvme_ind from gType_ind,value_ind,mysort_ind,endpoint_ind.
*)



Section Elimination.

Variables (Pg : gType -> Type) 
          (Pv : value -> Type) 
          (Pe : endpoint -> Type) 
          (Pm : mysort -> Type)
          (P_glist : seq gType -> Type)
          (P_elist : seq endpoint -> Type)
          (P_mlist : seq mysort -> Type).

Hypothesis Pg_var : (forall n : nat, Pg (GVar n)).
Hypothesis Pg_end : Pg GEnd.
Hypothesis Pg_rec : (forall g : gType, Pg g -> Pg (GRec g)).
Hypothesis Pg_msg : (forall (a : action) (v : value), Pv v -> forall g : gType, Pg g -> Pg (GMsg a v g)).
Hypothesis Pg_branch : (forall (a : action) (l : seq gType), P_glist l  -> Pg (GBranch a l)).

Hypothesis Pv_vst : forall l : seq mysort, P_mlist l -> Pv (VSeqSort l).
Hypothesis Pv_vlt : forall e, Pe e -> forall p, Pv (VLT e p).

Hypothesis Pm_bool : Pm SBool.
Hypothesis Pm_nat : Pm SNat.
Hypothesis Pm_sgtype : forall g : gType, Pg g -> Pm (SGType g).

Hypothesis Pe_var : forall n : nat, Pe (EVar n). 
Hypothesis Pe_end : Pe EEnd.
Hypothesis Pe_send : forall (c : ch) (s : value), Pv s -> forall e : endpoint, Pe e -> Pe (ESend c s e).
Hypothesis Pe_receive :  forall (c : ch) (s : value), Pv s -> forall e : endpoint, Pe e -> Pe (EReceive c s e).
Hypothesis Pe_sel : forall (c : ch) (l : seq endpoint), P_elist l  -> Pe (ESelect c l).
Hypothesis Pe_branch : forall (c : ch) (l : seq endpoint), P_elist l -> Pe (EBranch c l).
Hypothesis Pe_rec : forall e : endpoint, Pe e -> Pe (ERec e).

Hypothesis P_glist_0 : P_glist nil.
Hypothesis P_glist_cons : forall g, Pg g -> forall l, P_glist l -> P_glist (g::l).

Hypothesis P_elist_0 : P_elist nil.
Hypothesis P_elist_cons : forall e, Pe e -> forall l, P_elist l -> P_elist (e::l).

Hypothesis P_mlist_0 : P_mlist nil.
Hypothesis P_mlist_cons : forall s, Pm s -> forall l, P_mlist l -> P_mlist (s::l).

(*Maybe used derive mutual induct instead*)
Fixpoint gType_rect g : Pg g :=
  let fix seq_gType_rect gs : P_glist gs := 
    match gs with 
     | [::] => P_glist_0
     | g'::gs' => P_glist_cons (gType_rect g') (seq_gType_rect gs') 
     end in
  match g with 
   | GVar n => Pg_var n
   | GEnd => Pg_end
   | GRec g => Pg_rec (gType_rect g)
   | GMsg a u g => Pg_msg a (value_rect u) (gType_rect g)
   | GBranch a l => Pg_branch a (seq_gType_rect l)
   end
with mysort_rect m : Pm m :=
match m with 
| SBool => Pm_bool
| SNat => Pm_nat
| SGType g => Pm_sgtype (gType_rect g)
end
with value_rect v : Pv v :=
let fix seq_mysort_rect ss : P_mlist ss :=
 match ss with
  | [::] => P_mlist_0
  | m::ms => P_mlist_cons (mysort_rect m) (seq_mysort_rect ms)
 end
in
match v with 
| VSeqSort ss => Pv_vst (seq_mysort_rect ss)
| VLT e p => Pv_vlt (endpoint_rect e) p
end

with endpoint_rect e : Pe e :=
let fix seq_endpoint_rect ss : P_elist ss :=
 match ss with
  | [::] => P_elist_0
  | m::ms => P_elist_cons (endpoint_rect m) (seq_endpoint_rect ms)
 end in
match e with
| EVar n => Pe_var n
| EEnd => Pe_end
| ESend c m e => Pe_send c (value_rect m) (endpoint_rect e)
| EReceive c m e => Pe_receive c (value_rect m) (endpoint_rect e)
| ESelect c es => Pe_sel c (seq_endpoint_rect es)
| EBranch c es => Pe_branch c (seq_endpoint_rect es)
| ERec e => Pe_rec (endpoint_rect e)
end.



Definition seq_gType_rect : forall gs, P_glist gs :=
 fix seq_gType_rect gs : P_glist gs := 
    match gs with 
     | [::] => P_glist_0
     | g'::gs' => P_glist_cons (gType_rect g') (seq_gType_rect gs') 
     end.

Definition seq_mysort_rect : forall ms, P_mlist ms :=
 fix seq_mysort_rect ss : P_mlist ss :=
 match ss with
  | [::] => P_mlist_0
  | m::ms => P_mlist_cons (mysort_rect m) (seq_mysort_rect ms)
 end.

Definition seq_endpoint_rect : forall es, P_elist es :=
fix seq_endpoint_rect ss : P_elist ss :=
 match ss with
  | [::] => P_elist_0
  | m::ms => P_elist_cons (endpoint_rect m) (seq_endpoint_rect ms)
 end.

End Elimination.


Combined Scheme mut_ind_aux from gType_rect, mysort_rect, value_rect, endpoint_rect.

Notation In := List.In.
Notation Forall := List.Forall.
Section SpecializeElimination. 
Variables (Pg : gType -> Prop) 
          (Pv : value -> Prop) 
          (Pe : endpoint -> Prop) 
          (Ps : mysort -> Prop).

Definition mut_ind := (@mut_ind_aux Pg Pv Pe Ps (Forall Pg) (Forall Pe) (Forall Ps)).  
(*(fun gl => forall g, In g gl ->Pg g)
                                                (fun el => forall e, In e el ->Pe e)
                                                (fun sl  => forall s, In s sl ->Ps s)). *)

Definition true_pred A := fun (_ : A) => nat.
Definition gType_rect_true := (@gType_rect Pg  (@true_pred value) (@true_pred endpoint) (@true_pred mysort) (fun gl => forall g, In g gl ->Pg g)
                                                (@true_pred (seq endpoint))
                                                (@true_pred (seq mysort))).
End SpecializeElimination.



Fixpoint gType_eqb (g0 g1 : gType) { struct g0} : bool :=
let list_eq := fix list_eq s1 s2 {struct s1} := 
                                 match s1,s2 with
                                  | [::] , [::] => true 
                                  | x1 :: s1', x2 :: s2' =>  gType_eqb x1 x2 && (list_eq s1' s2') 
                                  | _ , _ => false 
                                  end
in
match g0, g1 with
| GMsg a0 v0 g0', GMsg a0' v0' g1' => (a0 == a0') && value_eqb v0 v0' && (gType_eqb g0' g1') 
| GRec g0', GRec g1' => gType_eqb g0' g1' 
| GEnd, GEnd => true
| GBranch a gs, GBranch a' gs' => (a == a') && (list_eq  gs gs')
| GVar n, GVar n' => n == n'
| _, _ => false
end
with value_eqb (v0 v1 : value) {struct v0} :=
let list_eq := fix list_eq s1 s2 {struct s1} := 
                                 match s1,s2 with
                                  | [::] , [::] => true 
                                  | x1 :: s1', x2 :: s2' => mysort_eqb x1 x2 && (list_eq s1' s2') 
                                  | _ , _ => false 
                                  end
in
match v0, v1 with 
| VSeqSort s0, VSeqSort s1 => list_eq s0 s1
| VLT e0 p0, VLT e1 p1 => endpoint_eqb e0 e1 && ( p0 == p1)
| _ , _ => false
end 

with endpoint_eqb (e0 e1 : endpoint) {struct e0} :=
let list_eq := fix list_eq s1 s2 {struct s1} := 
                                 match s1,s2 with
                                  | [::] , [::] => true 
                                  | x1 :: s1', x2 :: s2' => endpoint_eqb x1 x2 && (list_eq s1' s2') 
                                  | _ , _ => false 
                                  end
in
match e0, e1 with
| EVar n0, EVar n1 => n0 == n1
| EEnd , EEnd => true
| ESend ch0 s0 e0, ESend ch1 s1 e1 => (ch0 == ch1) && (value_eqb s0 s1) && (endpoint_eqb e0 e1)
| EReceive ch0 s0 e0, EReceive ch1 s1 e1 => (ch0 == ch1) && (value_eqb s0 s1) && (endpoint_eqb e0 e1)
| ESelect ch0 s0, ESelect ch1 s1 => (ch0 == ch1) && (list_eq s0 s1)
| EBranch ch0 s0, EBranch ch1 s1 =>  (ch0 == ch1) && (list_eq s0 s1)
| ERec e0, ERec e1 => endpoint_eqb e0 e1
| _ , _ => false
end
with mysort_eqb (st0 st1 : mysort) {struct st0} :=
match st0,st1 with 
 | SBool, SBool => true
 | SNat, SNat => true
 | SGType g0, SGType g1 => gType_eqb g0 g1
 | _ , _ => false
end.


Ltac case_filter :=  case;try (rewrite /= ; constructor ; done);intros.
Ltac case_filter_on x :=  move : x;case_filter.

Ltac inject :=  split; [ by move=>-> | by case ].
Ltac inject2 :=  split;[ case; by move =>->-> | case;by move =>->-> ]. 
Ltac inject3 := split; [ case;  move=>->; case; move=>->->; done |  case; move =>->->->; done]. 

Locate in_eq. 
Lemma refl_eqbs :  reflexive gType_eqb * (reflexive mysort_eqb * (reflexive value_eqb * (reflexive endpoint_eqb))). 
Proof. unfold reflexive. 
apply : mut_ind; intros;rewrite /= ?eqxx /=; 
       try solve [by rewrite /= | by rewrite H H0 | by rewrite H | induction l; first done; last (inversion H; rewrite H2 /=; auto)| constructor; auto].  
Defined.



Definition reflect_pred A (r : A -> A -> bool) := fun x => forall y, reflect ( x = y) (r x y).
Definition tp A (n : A) :=  True. Check (reflect_pred gType_eqb).
Ltac inject_refl := match goal with [ |- reflect (?f ?n = ?f ?n') _ ] => apply (@equivP (n = n')) end; last (try inject).
Ltac inject_refl2 := match goal with [ |- reflect (?f ?n0 ?n1 = ?f ?n0' ?n1') _ ] => apply (@equivP (n0 = n0' /\ n1 = n1')) end; last (try inject2).

Ltac inject_refl3 := match goal with [ |- reflect (?f ?n0 ?n1 ?n2 = ?f ?n0' ?n1' ?n2') _ ] => apply (@equivP (n0 = n0' /\ n1 = n1' /\ n2 = n2')) end; last (try inject3).

Lemma reflect_and : forall p0 p1 b0 b1, reflect p0 b0 -> reflect p1 b1 ->  reflect (p0 /\ p1) (b0 && b1).
Proof.
intros. inversion H;inversion H0; rewrite /=. constructor. auto. 
constructor. case. intros. auto. constructor. case. intros. done. constructor.  
case. intros. done.
Qed.

Definition list_eq {A} (r : A -> A -> bool) l0 l1 :=  (fix list_eq
     (s1 s2 : seq A) {struct s1} :
       bool :=
     match s1 with
     | [::] =>
         match s2 with
         | [::] => true
         | _ :: _ => false
         end
     | x1 :: s1' =>
         match s2 with
         | [::] => false
         | x2 :: s2' =>
             r x1 x2 &&
             list_eq s1' s2'
         end
     end) l0 l1.



Ltac eqbr := rewrite /= refl_eqbs ; try done.

Definition leib_eq (A : Type) (f : A -> A -> bool) := forall a b, f a b <-> a = b.
Ltac inj := split; solve [ by move/eqP=>-> | by case; move=>->].
Lemma axioms_eqbs : leib_eq gType_eqb *  (leib_eq mysort_eqb *  (leib_eq value_eqb *  leib_eq endpoint_eqb)).
Proof. unfold leib_eq.  apply : mut_ind. 
- intro. case_filter. intros. rewrite /=. inj.
- case_filter.
- intros g IH. case_filter.  rewrite /=. rewrite IH.  inj. 
- intros. case_filter_on b. rewrite /=. split.  
 * move/andP => [] /andP => [] [] /eqP=>->.  rewrite H H0. by move =>->->. 
 * case. move =>->->->. by rewrite eqxx /= !refl_eqbs. 
- intros. case_filter_on b. rewrite /=. split. 
 * move/andP=> [] /eqP=>->. intros. f_equal. generalize dependent l0.
   move : H. induction l. move => H. case_filter. done. 
   move => H. case_filter. done. 
   move : b. move/andP. case. intros. inversion H. subst. f_equal. by  rewrite -H2.   apply IHl. 
   done.  apply b. 
 * case. move=>->->. rewrite eqxx /=.  generalize dependent l0.
   case_filter. rewrite refl_eqbs /=.  induction l0. done. 
   rewrite refl_eqbs /=. done. 
- intros. case_filter_on b. rewrite /=. split. 
 * intros. f_equal. generalize dependent l0. induction l.
  ** case_filter. done.
  ** case_filter. done. 
     move : H0. move/andP. case. intros. inversion H. subst. f_equal. 
     apply/H2. done. auto.
 * case. move =>->. induction l0. done. rewrite refl_eqbs /=. apply IHl0. 
- intros. case_filter_on b. destruct p0. rewrite /=. split. 
 * move/andP. case. rewrite H. move =>-> /eqP =>->. done. 
 * case.  move=>->->. by rewrite eqxx refl_eqbs. 
- intros. case_filter_on b. 
- intro. case_filter_on b. 
- intros. move : b. case_filter. rewrite /=. split. 
 * by move/H=>->. case. move=>->. apply refl_eqbs.
- intros. move : b. case_filter. rewrite /=.  split. 
 * by move/eqP=>->. 
 * case. by move=>->. 
- case; rewrite/=; try done. 
- move => c s IH e. destruct b; rewrite/=; try done. split. 
 move/andP =>[] /andP [] /eqP -> /IH -> /H ->. done.
  case. move=>->->->. by rewrite eqxx !refl_eqbs. 

- intros. case_filter_on b.  rewrite /=. split. 
 * move/andP=>[] /andP [] /eqP -> /H -> /H0 ->. done. 
   case. move=>->->->. by rewrite eqxx !refl_eqbs.

- intros. case_filter_on b.  rewrite /=. split. 
  * move/andP=>[] /eqP ->. intros. f_equal.
   elim : l l0 H b. case;done. 
   intros. elim : l0 b; first done. intros. move : (andP b) =>[].  intros.
   inversion H0.  subst. f_equal;auto.
   apply/H4. done. auto. 
  * case. move =>->->. rewrite eqxx //=.
    elim : l0 H. auto.  rewrite /=. intros. rewrite refl_eqbs //=.
     apply/H. auto. 

- intros. case_filter_on b.  rewrite /=. split. 
  * move/andP=>[] /eqP ->. intros. f_equal.
   elim : l l0 H b. case;done. 
   intros. elim : l0 b; first done. intros. move : (andP b) =>[].  intros. inversion H0. f_equal;auto.
   apply/H4. done. auto. 
  * case. move =>->->. rewrite eqxx //=.
    elim : l0 H. auto.  rewrite /=. intros. rewrite refl_eqbs //=.
     apply/H. auto. 

- intros. case_filter_on b. rewrite /=. rewrite H. split;auto.
  move=>->. done.
  case. done.
all : try (rewrite /=; done).
all : intros;constructor;auto.  
Defined.



Lemma iff_reflect : forall A (eqb : A -> A -> bool),
 (forall a0 a1, eqb a0 a1 <-> a0 = a1) -> forall x y , reflect (x = y) (eqb x y).
Proof.
intros. destruct (eqb x y) eqn:Heqn.
- constructor.  rewrite <- H. done. constructor.  intro. specialize H with x y. destruct H. 
  apply H1 in H0. rewrite Heqn in H0. done. 
Qed.

Lemma endpoint_axiom : Equality.axiom endpoint_eqb.
Proof. move : axioms_eqbs. do ? (case;intro). move/iff_reflect. done. 
Qed.

Lemma gType_axiom : Equality.axiom gType_eqb.
Proof. move : axioms_eqbs. do ? (case;intro). move : a.  move/iff_reflect.  done. 
Qed.

Lemma mysort_axiom : Equality.axiom mysort_eqb.
Proof. move : axioms_eqbs. do ? (case;intro). move : a0.  move/iff_reflect.  done. 
Qed.

Lemma value_axiom : Equality.axiom value_eqb.
Proof. move : axioms_eqbs. do ? (case;intro). move : a1.  move/iff_reflect.  done. 
Qed.

Definition endpoint_EqMixin := EqMixin endpoint_axiom.
Canonical endpoint_EqType := EqType endpoint endpoint_EqMixin.

Definition gType_EqMixin := EqMixin gType_axiom.
Canonical gType_EqType := EqType gType gType_EqMixin.

Definition mysort_EqMixin := EqMixin mysort_axiom.
Canonical mysort_EqType := EqType mysort mysort_EqMixin.

Definition value_EqMixin := EqMixin value_axiom.
Canonical value_EqType := EqType value value_EqMixin.




Lemma inP : forall {A : eqType} l (g : A) , reflect (List.In g l) (g \in l).
Proof.
move => A. elim.
rewrite /=. intros. rewrite in_nil. constructor. done.
- move => a l H g. rewrite /=. apply Bool.iff_reflect. split. case.
move=>->. by rewrite in_cons eqxx. rewrite in_cons. move/H=>->.
by rewrite orbC. 
rewrite inE. move/orP =>[].  move/eqP=>->. auto. move/H. auto.
Qed.


Lemma gType_ind
     : forall (Pg : gType -> Prop),
       (forall n : nat, Pg (GVar n)) ->
       Pg GEnd ->
       (forall g : gType, Pg g -> Pg (GRec g)) ->
       (forall (a : action) (v : value),
        forall g : gType,
        Pg g -> Pg (GMsg a v g)) ->
       (forall (a : action) (l : seq gType),
         (forall g, g \in l -> Pg g) -> Pg (GBranch a l)) ->
       forall g : gType, Pg g.
Proof.
intros. apply : gType_rect_true;auto.
intros. apply H3. intros. apply H4. by apply/inP. 
all: try (rewrite /true_pred; constructor). 
rewrite /=. done. rewrite /=. 
intros. case : H6. move=><-. auto. auto. 
Qed.
Locate scons.
Fixpoint build_sigma_aux sigma g : (nat -> gType) := 
match g with 
| GRec g' => build_sigma_aux (unscoped.scons g sigma) g'
| _ => GVar
end.

Definition build_sigma g := build_sigma_aux GVar g.

Fixpoint unf_aux sigma g := 
match g with 
| GRec g' => unf_aux (unscoped.scons g sigma) g'
| _ => subst_gType sigma g
end.

Notation unf := (unf_aux GVar).

Fixpoint bound_i (i : nat) g  := 
match g with 
| GEnd => true
| GMsg _ _ g0 => bound_i i g0
| GBranch _ gs => all (bound_i i) gs
| GRec g0 => bound_i (S i) g0
| GVar n => n < i
end.

(*Inspired by Francisco*)
Fixpoint contractive_i (d : nat) g :=
match g with 
| GEnd => true
| GMsg _ _ g0 => contractive_i 0 g0
| GBranch _ gs => all (contractive_i 0) gs
| GRec g0 => contractive_i (S d) g0
| GVar n => d <= n
end. 

Fixpoint mu_height g :=
match g with
| GRec g0 => (mu_height g0).+1
| _ => 0
end.

Definition g_next g := 
match unf g with 
| GMsg a u g0 => Some (a,[::g0])
| GBranch a gs => Some (a,gs)
| _ => None
end.

Fixpoint unf2 (sigma : nat -> gType) g i :=  if i is i'.+1  then 
                                            if g is GRec g' then unf2 sigma (subst_gType (unscoped.scons g GVar) g') i' 
                                                            else subst_gType sigma g 
                                                         else g.

Require Import Dep.unscoped.


Fixpoint up_iter (sigma : nat -> gType) i := if i is i'.+1 then (up_iter (up_gType_gType sigma) i') else sigma.

Lemma  up_iter_test : forall k n sigma, (GVar n)[up_iter sigma k] = if n < k then (GVar n) else sigma n.
Proof.
elim.
elim.  intros. rewrite /=. done.
       intros. rewrite /=. done. 
intros. simpl. rewrite H. destruct (n0 < n) eqn :Heqn. have : n0 < n.+1 by lia. move=>->. done. case : n0 Heqn. rewrite /=.
 done. simpl. intros. rewrite /=. destruct ( n0.+1 < n.+1) eqn:Heqn2. asimpl. 
Admitted.


Lemma move_sigma : forall g' sigma, bound_i 0 g' ->unf_aux sigma g' = unf_aux GVar (g'[sigma]). 
Proof. 
intros g'. remember (mu_height g'). elim : n g' Heqn.
2 : { move => n H. case; try done. intros. simpl.  asimpl. inversion Heqn. rewrite H //=. symmetry. rewrite H. f_equal. asimpl. f_equal. f_equal. f_equal.
Admitted.


Lemma cont_lt : forall (g : gType) i j, j < i -> contractive_i i g -> contractive_i j g.
Proof.
elim;auto.
- rewrite /=. move => n i j. move/ltP=> + /leP;intros.  apply/leP. lia. 
- move => g H.  rewrite /=. intros. have : j.+1 < i.+1. apply/ltP. move : H0. move/ltP. lia. eauto. 
Qed.


Lemma unf_spec : forall g, bound_i 0 g -> contractive_i 0 g -> unf_aux GVar g = unf2 GVar g (mu_height g).
Proof.
intros g. remember (mu_height g). elim : n g Heqn.
- case; try done. 
 * intros. rewrite /=. f_equal. rewrite idSubst_gType //=.
 * intros. rewrite /=. f_equal. clear Heqn. elim : l H H0.  done. intros. simpl. f_equal.
   rewrite idSubst_gType //=. apply H. apply (andP H0). apply (andP H1). 
- move => n H [];try done.  intros. rewrite /=. rewrite -H //=. rewrite move_sigma //=.
  Admitted.

Lemma bound_subst : forall g sigma , bound_i 0 g -> g[sigma]=g.
Proof. Admitted.



(*Lemma mu_height_subst : forall g0 g1  i, contractive_i (S i) g0 -> mu_height (subst_gType i g0 g1) = mu_height g0.
Proof. 
elim; try solve [by rewrite /=].
- rewrite /=. intros. case : (eqVneq n i) H. move=>->. by rewrite ltnn. by rewrite /=. 
- intros. rewrite /=. f_equal. apply H. done. 
Qed.
*)



(*
Lemma unf_spec : forall g sigma, unf_aux sigma g = unf2 g (mu_height g).
Proof. 
move => g. remember (mu_height g). elim  : n g Heqn.
- intros. rewrite /=.  case : g  H Heqn H0. all : try  solve [rewrite //=]. 
  * intros. rewrite /=.  rewrite idSubst_gType //=. 
  * intros. rewrite /=. f_equal. clear Heqn. elim : l H H0. done. intros. simpl. 
    f_equal. rewrite idSubst_gType //=. simpl in *.  apply H. apply (andP H0). apply (andP H2).
- intros. rewrite /=. case : g Heqn H0 H1; try done.
  intros. simpl. rewrite test.  rewrite H. done. rewrite mu_height_subst //=. inversion Heqn. auto. 
   rewrite bound_cont_subst //=. apply : (@cont_lt _ 1). lia. done. intros. apply : bound_cont_eq. 
   simpl in H1. eauto. done. intros. apply bound_subst'. done. done. done.  done.
Qed.*)






(*
Lemma test : forall g' g sigma, (forall x, sigma x = GVar x) -> unf_aux (unscoped.scons g sigma) g' = unf_aux sigma (substitution 0 g' g).
Proof.
intros g'. remember (mu_height g'). elim : n g' Heqn.
- case. intros.  rewrite /=. case : (eqVneq n 0). intros. subst. asimpl.
 

Lemma bound_cont_subst : forall (g g': gType) i j, bound_i (S i) g -> contractive_i j g -> bound_i 0 g' -> (forall j, contractive_i j g') -> 
contractive_i j (substitution i g g').
Proof.
elim; (try solve [rewrite /= ;auto]).
- rewrite/=. move => v g' i j. case : (eqVneq v i).  done. simpl. done.
- rewrite /=. intros. apply/allP. move=> gsub /mapP. case. intros. subst. 
  apply H;auto. auto using (allP H0), (allP H1). auto using (allP H1). 
Qed.


Lemma bound_cont_eq : forall (g : gType) i, bound_i i g -> contractive_i i g -> (forall j, contractive_i j g).
Proof.
elim; rewrite/=;auto.
- rewrite /=. move => v i /ltP + /leP. lia. 
- rewrite /=. intros. eauto. 
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


Lemma bound_0 : forall (g : gType) j, bound_i 0 g -> bound_i j g.
Proof.
intros. case : j. done. intros. apply  : (@bound_lt _ 0). done. done.
Qed.

Lemma bound_subst' : forall (g g': gType) i, bound_i (S i) g -> bound_i 0 g' -> bound_i i (substitution i g g').
Proof.
elim.
-  rewrite /=;intros;case : (eqVneq n i).
   move=><-. apply bound_0. done. rewrite /bound_i. move : H. move=> /ltP H1 /eqP H2. 
   apply/ltP. lia. 
- rewrite /=. done. 
- rewrite /=. intros. apply H. done. done.
- rewrite /=. intros. auto. 
- rewrite /=. intros. move : (allP H0)=> H2. apply/allP. move => l' /mapP. case. intros. 
  subst. apply H;auto.
Qed.

Lemma unf_spec : forall g sigma, contractive_i 0 g -> bound_i 0 g -> (forall x, sigma x = GVar x) -> unf_aux sigma g = unf2 g (mu_height g).
Proof. 
move => g. remember (mu_height g). elim  : n g Heqn.
- intros. rewrite /=.  case : g  H Heqn H0. all : try  solve [rewrite //=]. 
  * intros. rewrite /=.  rewrite idSubst_gType //=. 
  * intros. rewrite /=. f_equal. clear Heqn. elim : l H H0. done. intros. simpl. 
    f_equal. rewrite idSubst_gType //=. simpl in *.  apply H. apply (andP H0). apply (andP H2).
- intros. rewrite /=. case : g Heqn H0 H1; try done.
  intros. simpl. rewrite test.  rewrite H. done. rewrite mu_height_subst //=. inversion Heqn. auto. 
   rewrite bound_cont_subst //=. apply : (@cont_lt _ 1). lia. done. intros. apply : bound_cont_eq. 
   simpl in H1. eauto. done. intros. apply bound_subst'. done. done. done.  done.
Qed.


Notation dec x := (Sumbool.sumbool_of_bool x).

Equations unf_recs (i : nat) g : gType by wf (mu_height g)  :=
unf_recs i (GRec g) := if (dec (contractive_i i (GRec g))) is left _  then (unf_recs i (substitution i g (GRec g))) else g;
unf_recs i g := g.
Next Obligation.
rewrite mu_height_subst. done. done.
Qed.



Definition act_of_g g :=
match unf_recs 0 g with 
| GMsg a _ _ => Some a
| GBranch a _ => Some a
| _ => None
end.

End Operations.*)
Check unf_aux.

Notation bound := (bound_i 0).
Notation contractive := (contractive_i 0).

(*Notation "G [ G0 ]" := (substitution 0 G G0)(at level 0, format "G [ G0 ]").*)

Notation gt_pred := (fun n0 n1 g => bound_i n0 g && contractive_i n1 g).




(*
attempt to simplify equality.axiom proof 


Definition eqb_i_eq {A} (r : A -> A -> bool) :=  forall g0 g1, r g0 g1 -> g0 = g1.



Lemma test :  eqb_i_eq gType_eqb * (eqb_i_eq mysort_eqb * (eqb_i_eq value_eqb * eqb_i_eq endpoint_eqb)). 
Proof. unfold eqb_i_eq.
apply : mut_ind.
move => n []; rewrite /= //=. by move=> n1 /eqP ->. 
move => []; rewrite /= //=. 
move => g IH []; rewrite /= //=. by  move=> g0 /IH ->. 
move => a v IH0 g IH1 []; rewrite /= //=. move => a0 v0 g0. 
by move/andP=>[] /andP [] /eqP -> /IH0 -> /IH1 ->. 

move => a l IH0 []; rewrite /= //=. move => a0 l0. 
move/andP=>[] /eqP ->.  intros. f_equal.
apply/(list_eqb_i_eq IH0)/b. 

move => l IH [] l1. rewrite/=. intros. f_equal.
apply/(list_eqb_i_eq IH)/H.

by rewrite /=.

move => e IH p []; rewrite /= //=. by move => e0 p0 /andP [] /IH -> /eqP ->. 
move => []; rewrite /= //=. 
move => []; by rewrite /=. 

move => g IH []; rewrite /=; try done. by move => g0 /IH=>->.

move => a v IH0 g IH1 []; rewrite /= //=. move => a0 v0 g0. 
by move/andP=>[] /andP [] /eqP -> /IH0 -> /IH1 ->. 

move => a l IH0 []; rewrite /= //=. move => a0 l0. 
move/andP=>[] /eqP ->.  intros. f_equal.
apply/(list_eqb_i_eq IH0)/b. 

move => l IH [] l1. rewrite/=. intros. f_equal.
apply/(list_eqb_i_eq IH)/H.

by rewrite /=.

move => l IH [] l0. rewrite /=. elim : l l0 b IH0. case;auto. intros;done. move => a1 l IH [];first done.
move => a2 l0 /andP []. intros. f_equal. apply IH0. simpl;auto. done. apply IH. auto. 
simpl in*;auto.


move : (andP b)=>[]. auto. apply IH. intros. apply IH0. apply IH0. auto. apply IH0. auto. f_equal. move => a1 l IH.   intros. intros.  auto. /andP []. /eqP -> /IH0 -> /IH1 ->. 


by move=> n1 /eqP ->. 

Proof.
elim
Definition n_reflexive {A} (r : A -> A -> bool) := forall a0 a1, a0 <> a1 -> r a0 a1 = false. 
Lemma n_refl_eqbs :  n_reflexive gType_eqb * (n_reflexive mysort_eqb * (n_reflexive value_eqb * n_reflexive endpoint_eqb)). 
Proof. unfold n_reflexive.
apply : mut_ind. 

Admitted.


Lemma test : Equality.axiom gType_eqb.
Proof.
move => g0 g1. case Heq : (gType_eqb g0 g1).
- constructor. apply : refl_eqbs. move : Heq. case : refl_eqbs. rewrite /reflexive. rewrite refl_eqbs.
intros;rewrite /= ?eqxx /=.
case :a1 H.
 try solve [by rewrite /= | by rewrite H H0 | by rewrite H ].


(*Ltac inject_refl := match goal with [ |- reflect (?f ?n = ?f ?n') _ ] => apply (@equivP (n = n')) end; last (try inject).
Ltac inject_refl2 := match goal with [ |- reflect (?f ?n0 ?n1 = ?f ?n0' ?n1') _ ] => apply (@equivP (n0 = n0' /\ n1 = n1')) end; last (try inject2).

Ltac inject_refl3 := match goal with [ |- reflect (?f ?n0 ?n1 ?n2 = ?f ?n0' ?n1' ?n2') _ ] => apply (@equivP (n0 = n0' /\ n1 = n1' /\ n2 = n2')) end; last (try inject3).*)

Lemma reflect_and : forall p0 p1 b0 b1, reflect p0 b0 -> reflect p1 b1 ->  reflect (p0 /\ p1) (b0 && b1).
Proof.
intros. inversion H;inversion H0; rewrite /=. constructor. auto. 
constructor. case. intros. auto. constructor. case. intros. done. constructor.  
case. intros. done.
Qed.

Ltac eqbr := rewrite /= refl_eqbs ; try done.

Ltac inj := split; solve [ by move/eqP=>-> | by case; move=>->].
Lemma axioms_eqbs : reflexive gType_eqb *  (reflexive mysort_eqb *  (reflexive value_eqb *  reflexive endpoint_eqb)).
Proof. apply : mut_ind; intros;rewrite /= ?eqxx /=; 
       try solve [by rewrite /= | by rewrite H H0 | by rewrite H | by rewrite refl_eqbs |
                  elim : l H;auto; intros; rewrite refl_eqbs //=; apply H; intros; apply H0; simpl;auto]. 
Defined.

Lemma iff_reflect : forall A (eqb : A -> A -> bool),
 (forall a0 a1, eqb a0 a1 <-> a0 = a1) -> forall x y , reflect (x = y) (eqb x y).
Proof.
intros. destruct (eqb x y) eqn:Heqn.
- constructor.  rewrite <- H. done. constructor.  intro. specialize H with x y. destruct H. 
  apply H1 in H0. rewrite Heqn in H0. done. 
Qed.

Lemma endpoint_axiom : Equality.axiom endpoint_eqb.
Proof. move => e0 e1.  move : axioms_eqbs. do ? (case;intro). move : a.  move/iff_reflect.  done. 

Proof. move => e e0. case Heq : (endpoint_eqb e e0). constructor. rewrite axioms_eqbs. move : Heq. rewrite -axioms_eqbs. move : axioms_eqbs. do ? (case;intro). move/iff_reflect. done. 
Qed.

Lemma gType_axiom : Equality.axiom gType_eqb.
Proof. move : axioms_eqbs. do ? (case;intro). move : a.  move/iff_reflect.  done. 
Qed.

Lemma mysort_axiom : Equality.axiom mysort_eqb.
Proof. move : axioms_eqbs. do ? (case;intro). move : a0.  move/iff_reflect.  done. 
Qed.

Lemma value_axiom : Equality.axiom value_eqb.
Proof. move : axioms_eqbs. do ? (case;intro). move : a1.  move/iff_reflect.  done. 
Qed.

Definition endpoint_EqMixin := EqMixin endpoint_axiom.
Canonical endpoint_EqType := EqType endpoint endpoint_EqMixin.

Definition gType_EqMixin := EqMixin gType_axiom.
Canonical gType_EqType := EqType gType gType_EqMixin.

Definition mysort_EqMixin := EqMixin mysort_axiom.
Canonical mysort_EqType := EqType mysort mysort_EqMixin.

Definition value_EqMixin := EqMixin value_axiom.
Canonical value_EqType := EqType value value_EqMixin.


*)
