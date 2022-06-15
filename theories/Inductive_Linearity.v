From mathcomp Require Import all_ssreflect finmap zify.



Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From deriving Require Import deriving.
From Dep Require Export Utils.
From Dep Require Import NewSyntax Substitutions.

(*From Dep Require Import Global_Syntax Substitutions.*)


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


(*Let inE := Substitutions.inE.*)




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





(*
Parameter (c : action).
Definition g' := (GRec (GBranch c ([::GVar 0;GVar 1]))).
Definition g := (GRec g'). 

Lemma test : (gunf ids g) = GBranch c ([::g';g]). done. Qed.
*)



Inductive Tr : seq action -> gType  -> Prop :=
| TR_nil G : Tr nil G 
| TRMsg a u aa g0 : Tr aa g0 -> Tr (a::aa) (GMsg a u g0)
| TRBranch d a n gs aa  : n < size gs -> Tr aa (nth d gs n) ->  Tr (a::aa) (GBranch a gs)
| TRUnf aa g : Tr aa (g[g GRec g.:var])  -> Tr aa (GRec g).
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
rewrite delete_cons /=. destruct n eqn:Heqn. by rifliad. 
subst. rewrite /= H. rifliad.  lia.
Qed.

Lemma delete_insert : forall (A : Type) aa n (x : A), (delete (insert aa n x) n) = if n <= size aa then aa else insert aa n x.
Proof. move => A. elim. intros. rewrite /=. destruct n. by  rewrite insert_nil delete_cons /=. 
rewrite insert_nil delete_cons delete_nil. by rifliad.  
intros. rewrite insert_cons. destruct n;rewrite /= delete_cons. done. rewrite H.
rifliad. 
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




Unset Elimination Schemes. Check Forall.



Inductive step : gType -> label  -> gType -> Prop :=
 | GR1 (a : action) u g : contractive2 g -> step (GMsg a u g) (a, inl u) g
 | GR2 a n gs : all contractive2 gs -> n < size gs -> step (GBranch a gs) (a, inr n) (nth GEnd gs n)
 | GR3 a u l g1 g2 : step g1 l g2 -> ptcp_to a \notin l.1 -> step (GMsg a u g1) l (GMsg a u g2)
 | GR4 a l gs gs' : size gs = size gs' -> Forall (fun p => step p.1 l p.2) (zip gs gs') -> (ptcp_to a) \notin l.1  ->  step (GBranch a gs) l (GBranch a gs')
 | GR_rec g l g' g'' : contractive2 g -> contractive2 g'' -> bisimilarg g g'' -> step g'' l g'  -> step g l g'. (*Add contractiveness assumption on g'' because we cant derive contractiveness of g'' from g : counter example : bisimilar a.end and a.(mu. 0) but the second is not contractive*)
Set Elimination Schemes. 
Hint Constructors step. 

(*Update induction principle*)

Lemma step_ind
     :  forall P : gType -> label -> gType -> Prop,
       (forall (a : action) (u : value) (g : gType), contractive2 g -> P (GMsg a u g) (a, inl u) g) ->
       (forall (a : action) (n : nat) (gs : seq gType), all contractive2 gs ->
        n < size gs -> P (GBranch a gs) (a, inr n) (nth GEnd gs n)) ->
       (forall (a : action) (u : value) (l : label) (g1 g2 : gType),
        step g1 l g2 ->
        P g1 l g2 -> ptcp_to a \notin l.1 -> P (GMsg a u g1) l (GMsg a u g2)) ->
       (forall (a : action) (l : label) (gs gs' : seq gType), size gs = size gs' ->
        Forall (fun p => step p.1 l p.2) (zip gs gs') ->  Forall (fun p => P p.1 l p.2) (zip gs gs') -> 

        ptcp_to a \notin l.1 -> P (GBranch a gs) l (GBranch a gs')) ->
       (forall g l g' g'', contractive2 g -> contractive2 g'' -> bisimilarg g g'' -> step g'' l g' -> P g'' l g' -> P g l g') ->
       forall (s : gType) (l : label) (s0 : gType), step s l s0 -> P s l s0.
Proof.
move => P H0 H1 H2 H3 H4. fix IH 4.
move => ss l s1 [].
intros. apply H0;auto. 
intros. apply H1;auto.
intros. apply H2;auto.
intros. apply H3;auto. elim : f;auto.  
intros. apply : H4;auto. all : eauto. 
Qed.

Require Import Paco.paco.


Check act_ofg.
Definition ext_act (p : option (action * option value + fin)) : option action :=
if p is Some (inl (a,_)) then Some a else None.

Fixpoint new_tr s g := 
match s with 
| nil => true 
| a::s' => (ext_act (act_ofg g) == Some a) && (has (fun g => new_tr s' g) (nextg g))
end.

(*Lemma act_ofg_subst : forall g sigma, act_ofg g [g sigma] = act_ofg g.
Proof.
elim;rewrite /=;try done. intros. *)
(*Lemma next_auxg_sigma : forall g sigma1 sigma2, (forall n, next_auxg sigma1 (sigma2 n) = [:: (sigma2 n) [gsigma1]]) -> next_auxg sigma1 g [g sigma2] = next_auxg (sigma2 >> fun g => g[g sigma1]) g.
Proof.
elim;rewrite /=;asimpl;try done;intros. 
destruct n.  asimpl. done. asimpl. done. 
apply H. *)

(*

Fixpoint bound_i (i : nat) g  := 
match g with 
| GEnd => true
| GMsg _ _ g0 => bound_i i g0
| GBranch _ gs => all (bound_i i) gs
| GRec g0 => bound_i (S i) g0
| GVar n => n < i
end.*)

(*Definition sapp (sigma0 sigma1 : nat -> gType) k := fun n => if n < k then sigma0 n else sigma1 n.*)

(*Definition bound g := forall sigma, g[g sigma] = g.


Fixpoint rem_rec g := if g is GRec g' then rem_rec g' else g.

Fixpoint accum_sig g sigma := if g is GRec g' then accum_sig g' (g.:sigma) else sigma.*)

Fixpoint contractive_i (d : nat) g :=
match g with 
| GEnd => true
| GMsg _ _ g0 => contractive_i 0 g0
| GBranch _ gs => all (contractive_i 0) gs
| GRec g0 => contractive_i (S d) g0
| GVar n => d <= n
end. 

(*bound contractive into some predicate*)
Lemma gunf_cont : forall g l, contractive_i (size l) g -> mu_height (gunf l g) = 0.
Proof.
elim;rewrite /=;intros;try done.  
elim : l n H.  done.
intros. simpl. destruct n. done. asimpl.
apply H. done.
apply H. simpl.  done.
Qed.


Lemma l_to_sig_n : forall l n, size l <= n -> (l_to_sig l n) = var (n - (size l)).
Proof.
elim. simpl. intros. asimpl. have : n - 0 = n by lia. move=>-> //=. 
intros. simpl. destruct n.   done.  simpl. have : n.+1 - (size l).+1 = n - (size l). lia. move=>->. 
apply H.  done. 
Qed.

Lemma l_to_sig_nth : forall l n, l_to_sig l n = nth (var (n - (size l))) l n.
Proof. 
elim.  intros. simpl. destruct n.  done. simpl. done.
intros. simpl. destruct n. done.  simpl. have : n.+1 - (size l).+1 = n - size l by lia.   move=>->. apply H. 
Qed.


Lemma l_to_sig_nth2 : forall l n, n < size l -> l_to_sig l n = nth (var (n)) l n.
Proof. 
intros. rewrite l_to_sig_nth. 
erewrite set_nth_default.  eauto.  done.
Qed.


Fixpoint bound_i (i : nat) g  := 
match g with 
| GEnd => true
| GMsg _ _ g0 => bound_i i g0
| GBranch _ gs => all (bound_i i) gs

| GRec g0 => bound_i (S i) g0
| GVar n => n < i
end.

Lemma bound_cont_eq : forall (g : gType) i, bound_i i g -> contractive_i i g -> (forall j, contractive_i j g).
Proof.
elim; rewrite/=;auto.
- rewrite /=. move => v i /ltP + /leP. lia. 
- rewrite /=. intros. eauto. 
Qed.

Lemma contractive_ren : forall g j sigma, (forall n, n <= sigma n) ->  contractive_i j g -> contractive_i j g ⟨g sigma ⟩.
Proof.
elim;intros;simpl.
simpl in H0. specialize H with n. lia. done.  asimpl. apply H.  intros. 
destruct n. done. simpl. asimpl. specialize H0 with n. lia.
done. simpl in H1. apply H.  auto. done.
rewrite all_map. apply/allP. intro. intros. simpl. apply H. done. auto. simpl in H1.  apply (allP H1).  done.
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

Fixpoint substitution (i : nat) g g'  := 
match g with 
| GEnd => GEnd
| GMsg a u g0 => GMsg a u (substitution i g0 g')
| GBranch a gs => GBranch a (map (fun g => substitution i g g) gs)
| GRec g0 => GRec (substitution i.+1 g0 g') 
| GVar n => if n == i then g' else g
end.


(*Lemma bound_contractive_subst : forall (g g': gType) i j, bound_i (S i) g -> contractive_i j g -> bound_i 0 g' -> (forall j, contractive_i j g') -> 
contractive_i j (substitution i g g').
Proof.
elim. 
- rewrite /=. intros. rifliad. done.
- rewrite /=. intros. apply H. done. done. done. done. 
- rewrite /=. intros. apply/allP. move=> gsub Hin. move : (mapP Hin). case. 
intros. subst. apply H. by apply/InP. move : (allP H0). 
move => H4. apply H4 in p. done. move : (allP H1). move => H4. apply H4 in p. done. done. 
  intros. done.
- rewrite /=. intros. 
apply H. done. done. done. done. 
- rewrite /=. intros.  apply/andP. move : (andP H1) (andP H2)=> [] + +[]. intros. split; auto. 
Qed.*)


(*Lemma contractive_subst : forall g sigma j, (forall n, (exists n', sigma n = var n' /\ n'<= n) \/ forall j, contractive_i j (sigma n)) ->  contractive_i j g -> contractive_i j g[g sigma].
Proof.
elim;rewrite /=;intros;try done.
edestruct H.   destruct H1,H1.  rewrite H1. simpl. lia. eauto. eauto. 
asimpl. apply : H. eauto. intros. destruct n. simpl.  auto. simpl. 
edestruct H0. 
rewrite /funcomp H. asimpl. auto. 
right. 
intros. simpl.  asimpl. apply contractive_ren. auto. auto.  auto. 
apply : H.   eauto. auto. auto.   
rewrite all_map. apply/allP. intro. intros. simpl. apply/H. done. auto. apply (allP H1).  done.
Qed.*)

(*
Lemma cont3 : forall l j n, all (contractive_i j) l -> contractive_i j (l_to_sig l n).
Proof.
intros. rewrite l_to_sig_nth.  
elim : l j n H. rewrite /=. intros. auto.  
intros. simpl in *. split_and. 
move : (H j n H2)=>[]. intros. left.  destruct n.  done. simpl. simpl in a0.  
have :  (n.+1 - (size l).+1) =  (n - (size l)).  lia. move=>->. 
clear H H1. 
destruct (n < (size l)) eqn:Heqn. 
apply (allP H2). apply/mem_nth. done. 
rewrite nth_default. rewrite nth_default in a0. simpl in a0. 
simpl.  lia.
apply/contractive_lt. 2 : { 
  2 : { lia. done. 
*)

(*Lemma cont_cons : forall g j sigma, contractive_i j g[g sigma] -> contractive_i j.+1 g[g (scons (var 0) sigma)].
Proof. 
intros.*)

Lemma bound_ren : forall g sigma, bound_i 0 g -> g ⟨g sigma ⟩ = g.
Proof. Admitted. 



(*Lemma cont_3 : forall g j l, contractive_i j g -> all (contractive_i (j - size l)) l ->  contractive_i (j - size l) g [g fun n => nth (var n) l n].
Proof. 
elim; try solve [rewrite /=;intros;try done];intros.
simpl. destruct ( n < size l) eqn:Heqn.
apply  (allP H0). apply/mem_nth. done.
rewrite nth_default;last lia. simpl. simpl in H0. lia. admit. 
simpl.  asimpl. 
have : (j - size l).+1 = j - size (var 0 :: [seq g0 ⟨g ↑ ⟩ | g0 <- l]). rewrite /= size_map /=. lia.

apply H. 
fext. intros. destruct x. done. simpl. rewrite /funcomp. rewrite bound_ren. done. admit.
simpl. intros. *)



(*Lemma cont_unf : forall g (l : seq gType) j ,  (all (contractive_i j )l) -> contractive_i (j + size l) g -> contractive_i j (gunf l g).
Proof. 
elim;rewrite /=;intros;try done.
rewrite l_to_sig_nth.  
destruct (n < size l) eqn:Heqn. 
apply (allP H). apply/mem_nth. done. Check l_to_sig_nth. 
rewrite nth_default. simpl.  lia. lia.
apply : H. simpl. split_and. 
apply/contractive_le. 2 : {  eauto.  }  lia. 
simpl.  apply/contractive_le. 2 : { eauto. } lia. 
have : 0 = 0 - (size l) by lia. move =>->. clear H a v. 
apply/cont_3. done.  have : 0 - size l = 0 by lia. move=>->.  
elim : l g j H0 H1.  intros. simpl. have : 0 - 0 = 0 by lia. move=>->. asimpl. done.
intros. simpl. apply/cont_3.
apply/contractive_subst.  intros.
rewrite l_to_sig_nth.  Check l_to_sig_nth. right. intros. 
have : j - size l = j.+1 - (size l).+1. lia. move=>->. 
apply : H. intros. simpl. split_and.
have : (j.+1 - (size l).+1) = (j- (size l)). lia. move=>->. simpl.
destruct ( (j - size l).+1 < j.+1) eqn:Heqn. apply/contractive_lt. apply : Heqn. eauto. 
have : j <= (j - size l). lia. clear Heqn. intros. 
have : (j - size l).+1 <= j.+1. lia. intros.

apply/contractive_le. eauto. done. done. 
apply/contractive_subst. intros.
 rewrite l_to_sig_nth. *)

(*Lemma gunf_cont2 : forall g, contractive_i 0 g ->  (gunf nil (gunf nil g)) = gunf nil g.
Proof.
intros. move : H.  have : 0 = size (@nil nat). done. move=>-> H. move : (@gunf_cont g nil H)=>H'. 
destruct (gunf nil g);try done. 
simpl. asimpl. done. simpl. asimpl. rewrite map_id. done.
Qed.
*)
(*Lemma gunf_idemp : forall g , contractive g -> gunf sigma' (gunf  g) = gunf sigma g. (*gunf ids (sigma n) = sigma n*)
Proof.
elim;rewrite /=;intros. destruct (sigma n); rewrite  //=;asimpl;try done.  
rewrite map_id. done. done. asimpl.  apply H. intros. destruct n.  asimpl.
  rewrite /gunf.  done. done. 
apply H. intros. destruct n. asimpl. simpl.
specialize  H with n. destruct (sigma n).  simpl. rewrite /gunf //=.'*)




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


(*Lemma guarded_subst2: forall g i k sigma, injective sigma ->  guarded i g -> sigma i = var k -> guarded k g [g sigma].
Proof.
elim;rewrite /=;simpl;intros;try done.
apply/eqP. move=> HH. apply H in HH. lia. 
asimpl. 
have : (sigma i).+1 = ((0 .: sigma >> succn) i.+1).
destruct i.  simpl. rewrite /funcomp. done. simpl. rewrite /funcomp. done.
move=>->. apply H. intro. intros. destruct x1;destruct x2;try done. inversion H2. f_equal.  apply/H0. done. 
done. 
Qed.*)







Lemma inject_ren : forall g g0 sigma,injective sigma -> g ⟨g sigma⟩ = g0 ⟨g sigma ⟩ -> g = g0.
Proof.
elim;rewrite /=;try done;intros.
move : H0. destruct g0;try done. asimpl. case. move/H=>->//=.
destruct g0;try done.
destruct g0;try done. f_equal. inversion H1. apply :H. 2 : {  eauto.} asimpl. auto.
destruct g0;try done. simpl in H1. inversion H1. f_equal. apply : H. 2 : { eauto. }  done. 
destruct g0;try done. simpl in H1. inversion H1. f_equal. 
move : H4.  clear H1 H3.  elim : l l0 H;intros.   destruct l0. done.  done. 
destruct l0. done.  simpl in*. f_equal. inversion H4. apply :H1. auto. 2 : { eauto. } done. 
apply H. intros. apply :H1. auto. eauto. eauto. inversion H4. done.
Qed.


Lemma inject2' : forall sigma, injective sigma ->  injective (var 0 .: sigma >> ⟨g succn ⟩).
Proof. 
intros. intro. intros. destruct x1;destruct x2;try done. move : H0. asimpl. 
destruct (sigma x2);done. move : H0. asimpl. destruct (sigma x1);done. f_equal. simpl in H0. 
move : H0. apply/inject_comp. done. intro. intros. apply/inject_ren. 2 : { eauto. } eauto. 
Qed.


(*Lemma testtest : forall g sigma, injective sigma -> contractive2 g ->  contractive2 g ⟨g sigma ⟩.
Proof.
elim;rewrite /=;try done;intros.
split_and. asimpl. have : 0 = (0 .: sigma >> succn) 0.   done. intros.  rewrite {1}x. apply/guarded_shift. 
auto.  done. 
asimpl. apply H.  auto. done. 
rewrite all_map. apply/allP. intro. intros. simpl. apply H. done. done. apply (allP H1).  done.
Qed.*)

(*Lemma bound_guard : forall g i,  bound_i i g -> guarded i g.
Proof.
elim;rewrite /=;try done;intros.
lia.  apply H.  done. 
Qed.
*)
(*Lemma bound_guard : forall g i,  bound_i i g -> guarded i g.
Proof.
elim;rewrite /=;try done;intros.
lia.  apply H.  done. 
Qed.*)

Lemma fv_shift : forall g v sigma, injective sigma ->  sigma v \in gType_fv g ⟨g sigma ⟩ ->   v \in gType_fv g. 
Proof. 
elim;rewrite /=;intros;try done. 
- move : H0. rewrite !inE.  move/eqP.  move/H=>-> //=. 
move : H1. move/imfsetP=>[] x /=. rewrite !inE /=. asimpl.  split_and.
apply/imfsetP. destruct x.  done. simpl in *. clear H2. subst. 
exists v.+1. simpl. rewrite !inE. split_and.
apply : H. 2 : { apply : H1. } intro. intros. destruct x1;destruct x2. done. done. done. f_equal. 
inversion H. apply/H0. done. 
done. apply : H. eauto.  eauto. 
move : H1. rewrite !big_map !big_exists. move/hasP=>[]. intros. apply/hasP.  exists x.  done. 
eauto. 
Qed.

(*Lemma fv_shift2 : forall g v' sigma, injective sigma ->  v' \in gType_fv g ⟨g sigma ⟩ -> exists v, v \in gType_fv g /\ v' = sigma v. 
Proof.
elim;rewrite /=;intros;try done. 
- move : H0. rewrite !inE.  move/eqP.  intros. exists n. rewrite !inE. auto. 
move : H1. move/imfsetP=>[] x /=. rewrite !inE /=. asimpl.  split_and.
apply H in H1. destruct H1,H1. destruct x0.  simpl in H3. lia. 
simpl in *. subst. asimpl. simpl. exists x0. split;try done. 
apply/imfsetP. simpl. exists ( (sigma >> succn) x0 ). rewrite !inE. split_and. done. simpl in *. clear H2. subst. 
exists v.+1. simpl. rewrite !inE. split_and.
apply : H. 2 : { apply : H1. } intro. intros. destruct x1;destruct x2. done. done. done. f_equal. 
inversion H. apply/H0. done. 
done. apply : H. eauto.  eauto. 
move : H1. rewrite !big_map !big_exists. move/hasP=>[]. intros. apply/hasP.  exists x.  done. 
eauto. 
Qed.
*)


Print up_gType_gType.

Print gType_fv. 
Open Scope nat_scope.
Print gType_fv.
Fixpoint fvg (g : gType) : {fset (nat * bool)} := 
match g with 
| GMsg a u g0 => [fset (n,true) | n in gType_fv g  (* (fvg g0) *)]
| GBranch  a gs  => [fset (n,true) | n in gType_fv g (*(\bigcup_(i <- (map fvg gs )) i)*) ] 
| GRec g0  => [fset ((n.1).-1,n.2) | n in (fvg g0) & n.1 != 0]
| GVar n => [fset (n,false)]
| GEnd => fset0
end.

Lemma guarded_fvg1 : forall g i, guarded i g -> (i,false) \notin fvg g.  
Proof.
elim;rewrite /=;try done;intros;rewrite ?inE //=.
lia. apply/imfsetP=>[]/= [] x /=. rewrite !inE. split_and. inversion q. 
subst. apply/negP. apply : H. eauto. have : x.1.-1.+1 = x.1 by lia. move=>->.
destruct x.  simpl in *. subst. done. 
apply/imfsetP=>[] [] /= x HH []. done. 
apply/imfsetP=>[] [] /= x HH []. done. 
Qed.

Lemma guarded_fvg2 : forall g i, ((i,false)  \notin fvg g) -> guarded i g.
Proof.
elim;rewrite /=;try done;intros.
move : H. rewrite !inE. simpl. lia.
apply H. move : H0.  move/imfsetP=>HH. apply/negP=>HH'. apply/HH. rewrite /=. 
exists (i.+1,false). rewrite !inE. split_and. 
rewrite /=. done. 
Qed.

Lemma guarded_fvg : forall g i, guarded i g <-> ((i,false) \notin fvg g).  
Proof.
intros. split;intros; auto using guarded_fvg1, guarded_fvg2. 
Qed.

(*Lemma fvg_subst : forall g sigma i b, injective sigma -> (sigma i = var i) -> (forall n b, (n,b) \notin (fvg (sigma n))) -> (i, b) \in fvg g [g sigma] ->  (i, b) \in fvg g.
Proof.
elim;rewrite /=;intros;try done. 
rewrite !inE.  apply/eqP. 
have : i = (fun k => if (sigma k) is GVar n' then n' else k) i.  rewrite H1.apply/eqP. f_equal. apply H in H1. subst. 
destruct (eqVneq k n). done. subst. rewrite H1 /= !inE in H0. move : H0. move/eqP. case. intros. subst. done. 
simpl in rewrite H0  /= !inE in H. done. 
simpl in H. rewr*)

Lemma gType_fv_ren: forall g sigma v, injective sigma -> sigma v \in gType_fv g ⟨g sigma⟩ -> v \in gType_fv  g. 
Proof.
elim;rewrite /=;intros;try done.
move : H0. rewrite !inE. move/eqP. move/H. lia. 
move : H1. move/imfsetP=>[] /= x. rewrite !inE. split_and.
apply/imfsetP. simpl. destruct x.  done. simpl in *. 
subst. exists v.+1;try done. rewrite !inE. split_and. apply : H.  2 : { apply : H1. } 
asimpl. auto. apply : H.  2 : { eauto. } done. 
move : H1. rewrite !big_map !big_exists. move/hasP=>[];intros. apply/hasP.
exists x. done. apply : H.  done.  2 : { eauto. } done. 
Qed.

(*Lemma fvg_ren: forall g sigma v b, injective sigma -> (sigma v,b) \in fvg g ⟨g sigma⟩ -> exists b, (v,b) \in fvg g. 
Proof.
elim;rewrite /=;intros;try done. 
move : H0. rewrite !inE. move/eqP. case. move/H. intros. subst. exists false. rewrite !inE. done.
move : H1. move/imfsetP=>[] /= x. rewrite !inE. asimpl. split_and.  destruct x.  simpl in *.
inversion q. subst.  
move : H1. destruct n. done. simpl in *. subst. 
have : (sigma v).+1 = ( 0 .: sigma >> succn) v.+1. simpl. done. 
move=>->. move/H=>HH.
have : injective (0 .: sigma >> succn). auto.  move/HH. move=>[] x /=. intros. 
exists b0. 
apply/imfsetP. simpl. exists (v.+1,b0). 2 : { simpl. done.  }
rewrite !inE /=. split_and. done. simpl in *. apply : H. 
2 : { rewrite -H4 in H1. apply : H1. } 
auto.
move : H1. move/imfsetP=>[] /= x. intros. destruct x. simpl in *. inversion q. subst. apply/imfsetP. inversion q. exists (v0,true);try done.
simpl. subst. 
destruct x.  simpl in *. subst. apply : H. 2 : { apply/gType_fv_ren. 2 : { eauto. } done. 
move : H1.  rewrite !big_map. move/imfsetP=>[]x/=;intros. 
inversion q. subst. 
apply/imfsetP. exists v;try done.  
simpl. move : p . rewrite !big_exists. move/hasP=>[];intros. apply/hasP.
exists x. done. apply :gType_fv_ren. 2 : { eauto. } done.
Qed.*)

(*Lemma fvg_subst : forall g sigma v b, injective sigma -> (v,b) \in fvg g [g sigma] -> sigma v = var v ->  (v,b) \in fvg g.
Proof. 
elim;rewrite /=;try done;intros.
- rewrite !inE. apply/eqP.
Admitted.

Lemma fvg_subst : forall g sigma v, injective sigma -> (v,false) \in fvg g [g sigma] -> exists2 x, (x \in gType_fv g) & ((v,false) \in fvg (sigma x)).
Proof. Admitted.*)
(*elim;rewrite /=;intros;try done. 
exists n. rewrite !inE //=. done. 
move : H1. move/imfsetP=>[] x /=. rewrite !inE. split_and. move : H1. asimpl. move/H=>HH.
have : injective (var 0 .: sigma >> ⟨g ↑ ⟩) . 
rewrite /shift. apply inject2'. done. move/HH=>[]. intros. 
subst. clear HH.  
exists x0.-1. 2 : { destruct x.  simpl in *. 
destruct x0.  simpl in q0. 
rewrite !inE in q0. move : q0.  move/eqP. case. intros. subst. done. 
simpl in q0. rewrite /funcomp in q0. simpl. apply/fvg_ren. 2 : { instantiate (1 := S).  
have : s.-1.+1 = s by lia. move=>->. apply : q0. }. 
done.  } 
apply/imfsetP. simpl. exists x0;try done. rewrite !inE. split_and.
destruct x0.  simpl in q0. move : q0. rewrite !inE. move/eqP. destruct x.   case.
intros. simpl in *. 
lia. done. 
move : H1. move/imfsetP=>[] /= x. intros. destruct a0. inversion q. subst. 
apply : H. done.  done. 
donedestruct (eqP q0). have : injective (((var 0 .: sigma >> ⟨g ↑ ⟩))). 
apply  inject2'. done. move/H=>HH. apply HH in q0. 
intro. intros. destruct x1;destruct x2;try done;simpl in *.



 move : p. move/H. apply H in p. apply/imfsetP. exists x0.-1. simpl. rewrite !inE. split_and. intro. intros. 
destruct x1. simpl in H1. destruct x2. done. simpl in H1. move : H1. asimpl. destruct (sigma x2);try done.  
simpl in H1. destruct x2. move : H1. asimpl. destruct (sigma x1);done. f_equal. simpl in H1. 
move : H1.  rewrite /funcomp. intros. apply/inject2. destruct x1;destruct x2;simpl in H1;try done. 

have : i = (fun k => if (sigma k) is GVar n' then n' else k) i.  rewrite H1.apply/eqP. f_equal. apply H in H1. subst. 
destruct (eqVneq k n). done. subst. rewrite H1 /= !inE in H0. move : H0. move/eqP. case. intros. subst. done. 
simpl in rewrite H0  /= !inE in H. done. 
simpl in H. rewr*)

Lemma contractive2_ren : forall g sigma, injective sigma -> (forall n, n <= sigma n) ->  contractive2  g -> contractive2 g ⟨g sigma ⟩.
Proof.
elim;intros;simpl;try done. 
asimpl. split_and. have : 0 = ( 0 .: sigma >> succn) 0. done. intros. rewrite {1}x.

rewrite -guarded_shift. simpl in H2. split_and. auto.
apply H. auto.  case. done. done.  simpl in H2. split_and. apply H.  done. done. done.
rewrite all_map. apply/allP. intro. intros. simpl. apply H. done.  done. done.  simpl in H2. apply (allP H2). done.
Qed.

(*Lemma guarded_subst : forall (g : gType) i sigma, guarded i g -> 
(forall n, n <> i -> guarded i (sigma n)) -> guarded i (g[g sigma]).
Proof. 
elim;rewrite /=;simpl;intros;try done.
apply H0.  lia. 
asimpl. apply H.  done. 
intros.  destruct n. done.  simpl. rewrite /funcomp. apply/guarded_shift.
intro. intros. inversion H3.  done. 
apply H1.  lia. 
Qed.*)


(*Lemma guarded_subst2 : forall g sigma i , sigma i = var i -> (forall n, n <> i -> guarded i (sigma n)) -> guarded i g -> guarded i g [g sigma].
Proof.
elim;rewrite /=;simpl;intros;try done.
apply H0. lia. 
asimpl. apply H.  simpl. asimpl. rewrite H0. done.
intros. destruct n. done. simpl. asimpl. apply/guarded_shift. done. apply H1. lia. done. 
Qed.*)

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


(*Lemma testtest2 : forall g sigma,contractive2 g -> (forall n, contractive2 (sigma n)) -> (forall n, guarded 0 (sigma n) \/ sigma n = var n) -> contractive2 g [g sigma].
Proof. 
elim;rewrite /=;intros;try done. 
asimpl. split_and. 

apply/guarded_subst2. done. intros. destruct n. done. asimpl. 
specialize H2 with n. destruct H2. 
apply/guarded_ren. done. done. 
rewrite H2. asimpl. done. done.
apply H. done.  intros. destruct n.  done. simpl. asimpl.  apply/contractive2_ren. done. done. done.
intros.  destruct n. auto. 
simpl. asimpl. 
specialize H2 with n.  destruct H2. left. apply/guarded_ren. done. done.
right. rewrite H0. simpl. done.
apply H.  done.  done.  done.
rewrite all_map. apply/allP. intro. intros. simpl. apply H. done. apply (allP H0). done. done.
done. 
Qed.*)


(*Lemma testtest2 : forall g sigma,contractive2 g -> (forall n, contractive2 (sigma n)) -> (forall n, guarded 0 (sigma n) \/ sigma n = var n) -> contractive2 g [g sigma].
Proof.
elim;rewrite /=;intros;try done. 
asimpl. split_and. 

apply/guarded_subst2. done. intros. destruct n. done. asimpl. 
specialize H2 with n. destruct H2. 
apply/guarded_ren. done. done. 
rewrite H2. asimpl. done. done.
apply H. done.  intros. destruct n.  done. simpl. asimpl.  apply/contractive2_ren. done. done. done.
intros.  destruct n. auto. 
simpl. asimpl. 
specialize H2 with n.  destruct H2. left. apply/guarded_ren. done. done.
right. rewrite H0. simpl. done.
apply H.  done.  done.  done.
rewrite all_map. apply/allP. intro. intros. simpl. apply H. done. apply (allP H0). done. done.
done. 
Qed.*)

(*Lemma testtest2 : forall g sigma i, bound_i i g -> contractive2 g -> (forall n, contractive2  (sigma n)) -> (forall n, if i <= n then sigma n = var n else bound_i i (sigma n)) -> contractive2 g [g sigma].
Proof.
elim;rewrite /=;try done;intros.
split_and. asimpl. apply/guarded_subst. done. intros.
destruct n. done.  simpl. asimpl. apply/guarded_fv.  apply/negP. move=> HH. 
apply fv_shift in HH. rewrite gType_fv_ren. apply/bound_guard. 
asimpl. apply :H.  eauto. done. 
intros. destruct n. done. simpl. asimpl. apply/testtest. auto.
specialize H3 with n. auto.  
intros. case_if. destruct n. simpl. done. simpl. asimpl. 
specialize H3 with n. have : i <= n by lia. move => HH. rewrite HH in H3. rewrite H3. asimpl. done. 
simpl. 
destruct n. simpl. rewrite H in H3. move : H3. case_if. done. auto. 
intros. 

have : 0 = (var 0 .: sigma >> ⟨g ↑ ⟩) 0.
apply : guarded_shift.  destruct n.  done.  simpl.
apply/guarded_ren. intros. destruct n0. done.  done. done. 
apply H.  done. intros. asimpl.  destruct n.  done. simpl. 
asimpl. apply/testtest. auto.  auto. 
intros. asimpl. destruct n. simpl.
rewrite all_map. apply/allP. intro. intros. simpl. apply H. done. apply (allP H0).  done.
auto.


 done. 
asimpl.  apply : H.  done. 
intros. destruct n.  simpl. *)


Lemma mu_height_ren : forall g sigma, mu_height g ⟨g sigma ⟩  = mu_height g.
Proof.
elim;rewrite /=;try done;intros.
f_equal. apply : H. 
Qed.

(*Lemma contractive_mu_height : forall g0 g1 i, contractive_i (S i) g0 -> mu_height (substitution i g0 g1) = mu_height g0.
Proof. 
induction g0; try solve [by rewrite /=].
- rewrite /=. intros. case : (eqVneq v i) H. move=>->. by rewrite ltnn. by rewrite /=. 
- intros. rewrite /=. f_equal. apply IHg0. move : H. by rewrite /=.
Qed.*)

Lemma mu_height_subst : forall g0 sigma i,  (forall n, n <= i -> guarded  i g0) -> (forall n, n != i -> mu_height (sigma n) = 0) -> contractive2 g0 -> mu_height (g0[g sigma]) = mu_height g0.
Proof. 
elim; try solve [by rewrite /=];intros.
- asimpl. simpl in H. rewrite H0. done. apply : H. instantiate (1:=0). eauto. 
simpl. f_equal. asimpl. apply H with (i:=i.+1). 2 : { intros. destruct n. simpl. done. simpl. asimpl.
rewrite mu_height_ren. apply H1. lia.  } intros. apply : H0. instantiate (1:=0).  eauto. simpl in H2. split_and.
Qed. 

Definition mu_height_subst0 g0 sigma :=  (@mu_height_subst g0 sigma 0).

Lemma act_ofg_unf : forall g, contractive2 g  -> guarded 0 g -> act_ofg (GRec g) = act_ofg g [gGRec g .: var].
Proof.
intros.
rewrite /act_ofg /= /full_unf /= mu_height_subst0.
rewrite -iterS iterSr. rewrite /=. done. auto. case. done. done.
done.
Qed.

Lemma nextg_unf : forall g, contractive2 g -> guarded 0 g -> nextg (GRec g) = nextg g [gGRec g .: var].
Proof.
intros.
rewrite /nextg /= /full_unf /= mu_height_subst0.
rewrite -iterS iterSr. rewrite /=. done. auto. case. done. done.
done.
Qed.

Lemma TrP1 : forall s g, Tr s g -> contractive2 g ->  new_tr s g.
Proof.
move => s g.
elim;auto;intros;simpl.
- rewrite eqxx /=. asimpl. rewrite H0 //=. 
- rewrite eqxx /=. rewrite /nextg /=.  apply/has_nthP. exists n. done.  apply : H1.  
  simpl in H2. apply (allP H2). apply/mem_nth. done.
- have :  contractive2 g0 [gGRec g0 .: var]. 
  apply/contractive2_subst. simpl in H1. split_and. case. done. intros. done. move/H0. 
  simpl. simpl in H1.
  destruct aa. done. simpl. split_and.  rewrite act_ofg_unf //=. rewrite nextg_unf //=. 
Qed.

Lemma TrP2 : forall s g, contractive2 g -> new_tr s g -> Tr s g.
Proof.
elim;auto;intros;simpl.
remember (mu_height g). 
move : n g Heqn H0 H1. 
elim. intros. destruct g;try done; simpl in H1; split_and; move : H2;rewrite /act_ofg /=; move/eqP; case; intros;
subst. constructor. apply H. destruct (orP H3);try done. destruct (orP H3);try done.
rewrite /nextg /= in H3. 
destruct (hasP H3). move : H1. move/nthP=>HH. specialize HH with GEnd. 
destruct HH. econstructor. eauto. apply H. simpl in H0. apply (allP H0). apply/mem_nth. done. 
rewrite -H4 in H2. apply : H2. 

intros. destruct g;try done. 
constructor. apply H0. rewrite mu_height_subst0. simpl in Heqn. inversion Heqn. done.
intros. simpl in H1. split_and. intros. destruct n0. done. done. simpl in H1. split_and. 
apply/contractive2_subst. simpl in H1. split_and.
case;try done.
move : H2. simpl in H1.  split_and. move : H2. rewrite /= act_ofg_unf //=. rewrite nextg_unf //=. 
Qed.

Lemma TrP : forall s g, contractive2 g -> Tr s g <-> new_tr s g.
Proof.
intros. split;auto using TrP1,TrP2.
Qed.


Lemma bisim_tr : forall s g0 g1, bisimilarg g0 g1 -> new_tr s g0 = new_tr s g1.
Proof. 
elim;intros. done.
simpl. punfold H0. inversion H0. subst. rewrite H1. f_equal. 
clear H1 H0.
remember (nextg g0). remember (nextg g1). clear g0 Heql0 g1 Heql1.  
elim  : l0 l1 H2 H3.
-  case;intros.
 * done. 
 * done. 
- move => a0 l0 IH. case;intros. 
 * done. 
 * simpl. simpl in H3. inversion H3. subst. simpl in H4. erewrite H. 2 : { inversion H4. eauto. done. } 
   f_equal.  apply :IH. all : eauto. 
Qed.


Lemma bisim_Tr : forall s g0 g1, contractive2 g0 -> contractive2 g1 ->  bisimilarg g0 g1 -> Tr s g0 -> Tr s g1.
Proof. 
intros. apply/TrP;try done. rewrite -(@bisim_tr _ _ _  H1).  apply/TrP. done. done. 
Qed.

(*Definition lnext (l : seq action) := if l is x::l' then l' else nil.
Definition lhead (l : seq action) := if l is x::l' then Some x else None.

Lemma bisim_act_aux : forall g g' l,  act_ofg g = lhead l -> g' \in (nextg g) -> Tr (lnext l) g' -> Tr l g.
Proof.
elim;intros;try done. 
simpl in H. destruct l.  done. done. 
simpl.
2 : { inversion H0.  simpl in H0. destruct l. done.  inversion H0. constructor. apply : H. 
move : H1. rewrite /nextg /= !inE. move/eqP. intros. subst. simpl in H. inversion H
elim;simpl;try done;intros.
constructor. rewrite /gsubst. move : H0. rewrite /nextg. asimpl. simpl. intros.
constructor. *)


Lemma bisim_sym: forall g0 g1,  bisimilarg g0 g1 -> bisimilarg g1 g0.
Proof. 
pcofix CIH. intros. punfold H0. inversion H0. pfold. subst.  constructor. rewrite H //=. rewrite H1 //=.
move : H2. move/forallzipP=>Hzip. apply/forallzipP. done.
intros. simpl in *. right. apply : CIH.
suff :  upaco2 bisimilar_fg bot2 (nth GEnd (nextg g0) x0) (nth GEnd (nextg g1) x0).
case. intros. punfold a. pfold. eauto.
case. apply : Hzip. done. rewrite H1. done.
Qed.

Lemma step_contractive : forall g l g', step g l g' -> contractive2 g.
Proof. move => g l g'. elim;try done.
intros. simpl. move : H1. move/forallzipP=>Hzip. simpl in Hzip. apply/allP. intro. move/nthP=>HH. 
specialize HH with GEnd. destruct HH. rewrite -H3. apply Hzip. repeat constructor. done. done. 
Qed.

Lemma step_contractive2 : forall g l g', step g l g' -> contractive2 g'.
Proof. move => g l g'. elim;try done.
intros. apply (allP H).  apply/mem_nth. done. 
intros. simpl. move : H1. move/forallzipP=>Hzip. simpl in Hzip. apply/allP. intro. move/nthP=>HH. 
specialize HH with GEnd. destruct HH. rewrite -H3. apply Hzip. repeat constructor. done. rewrite H. done. 
Qed.

Lemma step_tr_in : forall g vn g', step g vn g' -> forall s, Tr s g' -> Tr s g \/ exists n, Tr (insert s n vn.1) g /\ Forall (fun a => (ptcp_to a) \notin vn.1) (take n s).
Proof.
move => g vn g'. rewrite /insert. elim.
- intros. right. exists 0. simpl. rewrite take0 drop0 /=.  auto. 
- intros. right. exists 0. simpl. rewrite take0 drop0 /=. eauto.  
- intros. destruct s;auto. 
  inversion H2. subst. move : (H0 _ H4)=>[];auto.
  move=> [] n [].  intros. right. exists n.+1. simpl. auto. 
- intros. destruct s; auto.
  inversion H3. subst. move : H1. move/forallzipP=>Hzip. simpl in Hzip. rewrite -H in H7. 
  specialize Hzip with d d n s.
have :  Tr s (nth d gs n) \/
         (exists n0 : fin,
            Tr (take n0 s ++ l.1 :: drop n0 s) (nth d gs n) /\
            Forall (fun a : action => ptcp_to a \notin l.1) (take n0 s)).
apply : Hzip;try done.
case;intros. left. econstructor. eauto. eauto. destruct b. right. 
exists x.+1. split;simpl;try done. econstructor. eauto. destruct H1. eauto. destruct H1. eauto.
- intros. destruct (@H3 _ H4). left.   apply/bisim_Tr. 3 : { apply/bisim_sym. eauto. } done. done. done. 
 right. destruct H5. exists x. destruct H5. split;auto.
  apply/bisim_Tr. 4 : { eauto. } all: try done. apply/bisim_sym. eauto. 
Qed.


Lemma Tr_app : forall (G : gType) l0 l1, Tr (l0++l1) G -> Tr l0 G.
Proof.
intros.  remember (l0 ++ l1). elim : H l0 l1 Heql ;intros.  destruct l0;done. 

destruct l0. done. rewrite cat_cons in Heql. inversion Heql. subst. eauto.  
destruct l0. done. rewrite cat_cons in Heql. inversion Heql. subst.
apply : TRBranch;  eauto. constructor. eauto.  
Qed.


Lemma take_cat2
     : forall (n0 : nat) (T : Type) (s1 s2 : seq T),
       take n0 (s1 ++ s2) = (if n0 <= size s1 then take n0 s1 else s1 ++ take (n0 - size s1) s2).
Proof.
intros. rewrite take_cat. rifliad. rifliad. lia.   have : n0 = size s1 by lia. move=>->. have : size s1 - size s1 = 0 by lia.  move=>->. rewrite take0 cats0. by  rewrite take_size. 
Qed.

Lemma drop_cat2 
     : forall (n0 : nat) (T : Type) (s1 s2 : seq T),
       drop n0 (s1 ++ s2) = (if n0 <= size s1 then drop n0 s1 ++ s2 else drop (n0 - size s1) s2).
Proof. intros. rewrite drop_cat. rifliad. rifliad. lia.  have : n0 = size s1 by lia. move=>->. have : size s1 - size s1 = 0 by lia. move=>->. rewrite drop0. rewrite drop_oversize //=. 
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


(*Lemma in_action_from' : forall p0 p1 c, p0 \in Action p0 p1 c.
Proof. intros.  rewrite !inE. by rewrite /in_mem /= eqxx. Qed.

Lemma in_action_to' : forall p0 p1 c, p1 \in Action p0 p1 c.
Proof. intros. rewrite !inE.  by rewrite /in_mem /= orbC eqxx. Qed.*)

(*Lemma in_action_from : forall a, ptcp_from a \in a.
Proof. intros. destruct a. rewrite /=. rewrite in_action_from' //=. Qed.

Lemma in_action_to : forall a, ptcp_to a \in a.
Proof. intros. destruct a. rewrite /=. rewrite in_action_to' //=. Qed.*)

(*Hint Resolve in_action_from in_action_to in_action_from' in_action_to'.*)

Lemma IO_in_action : forall a0 (l : action), IO a0 l -> (ptcp_to a0) \in l.
Proof.
move => a0 a1. rewrite /IO.  rewrite /IO. move/eqP=>->. by rewrite !inE. 
Qed.

Lemma II_in_action : forall a0 (l : action), II a0 l -> (ptcp_to a0) \in l.
Proof.
move => a0 a1. rewrite /II.  move/eqP=>->. rewrite !inE. lia. 
Qed.


Lemma IO_II_in_action : forall a0 (l : action), IO_II a0 l -> (ptcp_to a0) \in l.
Proof.
move => a0 a1. rewrite /IO_II. move/orP=>[]; auto using IO_in_action, II_in_action. 
Qed.


Lemma InDep_insert : forall a0 aa a1 n x,  n <= size aa -> Forall (fun a : action => ptcp_to a \notin x) (take n aa) -> ptcp_to a0 \notin x -> exists_dep InDep a0 (insert aa n x) a1 -> exists_dep InDep a0 aa a1.
Proof. 
intros. destruct H2,H2,H3,H4. have : n < size x0.  rewrite size_insert in H2. rewrite H2. lia. 
move=> H4. destruct (nth false x0 n == false) eqn:Heqn. 
- move : (eqP Heqn)=>HH. move : H3. rewrite (@mask_delete _ false n (insert aa n x)) //=. rewrite !delete_insert.  rifliad. 
 intros. exists (delete x0 n). rewrite size_delete.  rifliad. rewrite H2 size_insert /=. auto. 
- have : nth false x0 n = true by lia. clear Heqn. move => Heqn. 
  destruct (@insert_spec _ aa n x H).  destruct H5,H5,H6. move : H3. rewrite H6 split_mask; last (rewrite size_cat /= H2 size_insert -H5 size_cat; lia).
  rewrite H7 Heqn /=. 
   have : (a0 :: (mask (take n x0) x1 ++ x :: mask (drop n.+1 x0) x2) ++ [:: a1]) = 
          ((a0 :: (mask (take n x0) x1 ++ [::x])) ++ ((mask (drop n.+1 x0) x2) ++ [:: a1])). 
   rewrite -!catA. rewrite !cat_cons /=. rewrite !catA. f_equal.  rewrite -!catA. f_equal. move=>->.
 move/InDep_iff. move/indep0.

   rewrite cat_path /=. move/andP=>[] _. rewrite andbC /=.  destruct (mask (take n x0) x1) eqn:Heqn4. 
 * rewrite /=. move/IO_II_in_action. move => HH.  rewrite HH in H1. done. 
 * rewrite /=. intros. have : (last a l) \in (take n aa).  rewrite -H5 take_cat. rifliad.  lia. 
   rewrite mem_cat. 
   apply/orP. left. eapply mem_mask with (m:= (take n x0)).  rewrite Heqn4.  by rewrite mem_last.  

   move : H0. rewrite List.Forall_forall.  intros.  apply In_in in x3. apply H0 in x3. apply IO_II_in_action in b. rewrite b in x3. done. 
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



Lemma ch_diff : forall g a0 aa a1, Linear g -> Tr (a0::(aa++[::a1])) g  -> Forall ( fun a => (ptcp_to a) \notin a1) (a0::aa) ->  Forall (fun a => action_ch a != action_ch a1) (a0::aa).
Proof.
intros. apply/List.Forall_forall. intros. 
destruct (eqVneq (action_ch x) (action_ch a1)); last done. inversion H1. subst.
exfalso. simpl in H2. destruct H2. 
- subst. apply : no_indep. apply : H5.  apply H6. move : H. move/Linear_1=>HH.  apply : HH. 
  rewrite -[_::_]cat0s in H0. apply : H0. rewrite /same_ch. apply/eqP. done.
- apply List.in_split in H2.  destruct H2,H2. rewrite H2 in H0. rewrite /Linear in H.
  specialize H with (a0::x0) x x1 a1. 
have : (a0 :: (x0 ++ (x :: x1)%SEQ)%list ++ [:: a1]) = ((a0 :: x0) ++ x :: x1 ++ [:: a1]).
  rewrite /=. f_equal. rewrite -catA. f_equal.


  intros. move : H0.  rewrite x2. move/H=>H3. 
  have : same_ch x a1. by rewrite /same_ch e. move/H3. case. intros. move : H1.  
  rewrite H2. intros. inversion H1. apply List.Forall_app in H8. destruct H8. inversion H9. apply : no_indep. 
  apply H12.  apply H13.  done.
Qed.





(*Shorten proof by using distinct_ch*)
Open Scope nat_scope.
Lemma Linear_step  : forall g l g', step g l g' ->  Linear g -> Linear g'.
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
have : aa_p ++ a0 :: aa ++ [:: a1; l.1] = (aa_p ++ a0 :: aa ++ [:: a1]) ++ [::l.1]. rewrite -!catA !cat_cons. f_equal. Search _ (_ :: (_ ++ _)). f_equal. rewrite -catA. f_equal. move=>->. eauto. move/Tr_app.  intros. eauto. 
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
- move : (eqP Heqn4)=>HH. move : H5. rewrite (@mask_delete _ false n0 (insert aa n0 l.1)) //=. rewrite delete_insert. rifliad.  intros. exists (delete x0 n0). rewrite size_delete.  rifliad. rewrite H4 size_insert /=. split;auto.  

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
  **  rewrite -H6 in HH2. move : HH2. rewrite take_cat. rifliad. lia.
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
  ** intros. rewrite -H6 in HH2. move : HH2. rewrite take_cat. rifliad. lia.
      move/List.Forall_app=>[]. move/List.Forall_forall=> Hf _. intros.  apply/negP. apply : Hf. apply/In_in. apply : b0. done. 
 * move=> [] l' [] a2 HHeq'. rewrite HHeq'.
     rewrite  -!catA -cat_cons. move/indep1. rewrite /= andbC /=. move/IO_II_in_action=> Hia.  exfalso. 
     move : HH2. rewrite -H6. rewrite take_cat. rifliad. lia.
      move/List.Forall_app=>[]. move/List.Forall_forall=> Hf _. apply : negP. apply : Hf. apply/In_in. 2: { apply : Hia. } 
    
       destruct l1.  simpl in Heq0.  inversion Heq0.  eapply mem_mask with (m:= x3). rewrite HHeq'. by rewrite mem_cat inE eqxx orbC. simpl in Heq0. 
inversion Heq0. rewrite mem_cat.  apply/orP. right. rewrite inE. apply/orP. right. eapply mem_mask with (m:=x3). rewrite HHeq'. by  rewrite mem_cat inE eqxx orbC. 
Qed.



