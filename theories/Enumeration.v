Require Import Dep.Syntax.

Require Import Lists.List.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import zify.
From mathcomp Require Import finmap.
From Equations Require Import Equations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Program. 

Ltac uf name := rewrite /name -/name.

Section Enumeration.
Variable U : countType.
Implicit Type g : gType U.
Fixpoint gType_size g :=
match g with
 | GMsg a u g0 => (gType_size  g0).+1
 | GRec g0 => (gType_size g0).+1
 | GBranch a gs => (sumn (map gType_size gs)).+1
 | GEnd => 1
 | GVar n => 1
end.

Definition g_next g :=
match unf_recs g with 
| GMsg _ _ g0 => [::g0]
| GBranch _ gs => gs
| _ => [::]
end.

Fixpoint gEnum n g : seq (gType U) :=
if n is n'.+1 then g::(map (gEnum n') (g_next g)) else g.

Lemma gEnum_correct : forall g ge, ge \in g gEnum (gType_size -> exists2 p, path (grel g_next) g p 



Locate "homo". Locate homomorphism_2.
Fixpoint mu_height g :=
match g with
| GRec g0 => (mu_height g0).+1
| _ => 0
end.

Lemma mu_height_subst : forall (g0 g1 : gType U) i, contractive_i (S i) g0 -> mu_height (substitution i g0 g1) = mu_height g0.
Proof. 
elim; try solve [by rewrite /=].
- rewrite /=. intros. case : (eqVneq n i) H. move=>->. by rewrite ltnn. by rewrite /=. 
- intros. rewrite /=. f_equal. apply H. done. 
Qed.

Lemma bound_subst_eq : forall g i gsub, bound_i i g -> substitution i g gsub = g.
Proof.
elim/gType_ind_list;auto. 
move => n i gsub. rewrite /=. case : (eqVneq n i). lia. done. 
move => g IH. rewrite /=. intros. f_equal. auto. 
move => a l IH.  rewrite /=.  intros. rewrite H //=. 
move => a l IH i gsub. rewrite /=. intros. f_equal.  
elim : l IH H. intros. rewrite /=. done. 
intros. move : H0. rewrite /=.  move/andP => []. intros.  rewrite IH. rewrite H. 
done. intros.  apply IH. by rewrite inE H0 orbC. done. done.
by rewrite inE eqxx. done. 
move => g. rewrite in_nil. done.
intros. move : H1 H H2. rewrite inE. move/orP =>[]. move/eqP=>->. auto. auto. 
Qed.

Notation dec x := (Sumbool.sumbool_of_bool x).

Equations unf_recs (i : nat) (g : gType U)  : gType U by wf (mu_height g)  :=
unf_recs i (GRec g) := if (dec (contractive_i i (GRec g))) is left _  then (unf_recs i (substitution i g (GRec g))) else g;
unf_recs i g := g.
Next Obligation.
rewrite mu_height_subst. done. done.
Qed.

(*Lemma bound_unf : forall i g, bound_i i g = bound_i i (unf_recs i g).
Proof.
elim;auto.
intros. funelim (unf_recs 0 g);auto. rewrite /=. destruct (dec (contractive (GRec g))).
rewrite -H //=. rewrite bound_subst_eq. rewrite -IH. rewrite -IH. simp unf_recs. rewrite bound_subst_eq.*)

Lemma bound_lt : forall (g : gType U) i j, i < j -> bound_i i g -> bound_i j g.
Proof. 
elim/gType_ind_list.
- rewrite /=;auto. move=>n i j.  move=> /leP H /ltP H1. apply/ltP.  lia. 
- rewrite /=;auto. intros. apply : (@H i.+1 j.+1); done. 
- rewrite /=;auto. 
- intros. move : H1. rewrite /=.  move/allP=>H2. apply/allP. move=> l' Hin. move : (H2 l' Hin). 
  apply H;auto. 
- intros. simpl in H. done.
- rewrite /=. intros. case : H1 H3. rewrite inE. case/orP. move/eqP=>->. eauto. 
  eauto.
Qed.


Lemma bound_0 : forall (g : gType U) j, bound g -> bound_i j g.
Proof.
intros. case : j. done. intros. apply  : (@bound_lt _ 0). done. done.
Qed.

Lemma bound_subst : forall (g g': gType U) i, bound_i (S i) g -> bound g' -> bound_i i (substitution i g g').
Proof.
elim/gType_ind_list.
-  rewrite /=;intros;case : (eqVneq n i).
   move=><-. apply bound_0. done. rewrite /bound_i. move : H. move=> /ltP H1 /eqP H2. 
   apply/ltP. lia. 
- rewrite /=. done. 
- rewrite /=. intros. apply H. done. done.
- rewrite /=. intros. auto. 
- rewrite /=. intros. move : (allP H0)=> H2. apply/allP. move => l' /mapP. case. intros. 
  subst. apply H;auto.
- rewrite /=. move => g. by rewrite in_nil. 
- move => g H l IH g0. rewrite inE. case/orP. move/eqP =>->; auto. auto. 
Qed.

Lemma cont_lt : forall (g : gType U) i j, j < i -> contractive_i i g -> contractive_i j g.
Proof.
elim;auto.
- rewrite /=. move => n i j. move/ltP=> + /leP;intros.  apply/leP. lia. 
- move => g H.  rewrite /=. intros. have : j.+1 < i.+1. apply/ltP. move : H0. move/ltP. lia. eauto. 
Qed.

Lemma contractive_0 : forall (g : gType U) i,  contractive_i i g -> contractive g.
Proof.
move=> g. case. done. intros.  apply : cont_lt; last eauto. done.
Qed.


Lemma bound_cont_subst : forall (g g': gType U) i j, bound_i (S i) g -> contractive_i j g -> bound g' -> (forall j, contractive_i j g') -> 
contractive_i j (substitution i g g').
Proof.
elim/gType_ind_list; (try solve [rewrite /= ;auto]).
- rewrite/=. move => v g' i j. case : (eqVneq v i).  done. simpl. done.
- rewrite /=. intros. apply/allP. move=> gsub /mapP. case. intros. subst. 
  apply H;auto. auto using (allP H0), (allP H1). auto using (allP H1). 
- rewrite /=. intros.  move : H1 H2 H3. rewrite inE. case/orP. move/eqP=>->. 
  eauto. eauto. 
Qed.

Lemma bound_cont_eq : forall (g : gType U) i, bound_i i g -> contractive_i i g -> (forall j, contractive_i j g).
Proof.
elim; rewrite/=;auto.
- rewrite /=. move => v i /ltP + /leP. lia. 
- rewrite /=. intros. eauto. 
Qed.


Definition act_of_g g :=
match unf_recs g with 
| GMsg a _ _ => Some a
| GBranch a _ => Some a
| _ => None
end.


Lemma gType_sizegt0 : forall (g : gType U), exists2 n,n = (gType_size g).-1  & gType_size g= n.+1 .
Proof.
elim; do ? rewrite /=;eauto.
Qed.


Definition seq_subst gs g := map (fun g' => g'[g]) gs.

Lemma g_next_var n : (g_next (GVar n)) = [::].
Proof.
reflexivity.
Qed.

Lemma g_next_end : (g_next (GEnd)) = [::].
Proof.
reflexivity.
Qed.




Lemma unf_recs_sub : forall g gsub i, bound_i i g -> contractive_i i g -> unf_recs (substitution i g gsub) = substitution i (unf_recs g) gsub.
Proof. move => g gsub i. intros. rewrite !bound_subst_eq //=.
elim.
- move => n gsub. rewrite /=. case : n. lia. move => n. lia.
- move => gsub i j. intros. rewrite /=. done. 
- move => g IH gsub i j. rewrite /=. intros. simp unf_recs.
  case : (dec (contractive (GRec (substitution i.+1 g gsub)))).  
 + intros. case : (dec (contractive (GRec g))). 
   * rewrite /=. intros. apply IH. simp unf_recs_unfold_clause_1. funelim (unf_recs (GRec (substitution i.+1 g gsub))).  unf_recs.
  simp unf_recs. Set Printing All.
 destruct (@idP (contractive (GRec (substitution i.+1 g gsub)))).  
 case : idP. case : j. by rewrite /=. 
  move => n. rewrite /=. rewrite IH. rewrite -IH. apply IH. rewrite /substitution -/substitution. rewrite /=. intros. rewrite -IH.


Lemma grel_subst : forall g ge gsub, grel g_next g ge -> grel g_next g[gsub] ge[gsub].
Proof.
move => g ge gsub. rewrite /= /g_next. 
destruct (unf_recs g) eqn:Heqn; try (rewrite in_nil;done). 
rewrite inE. move => /eqP=>->.  
have : unf_recs g[gsub] = GMsg a s g0[gsub]. 

admit.
move=>->. rewrite inE. done. 
move => g ge. rewrite /= /g_next. rewrite /mu_height-/mu_height /=. 
destruct (unf_recs g) eqn:Heqn; try (rewrite in_nil;done). 
rewrite inE. move => H1 H2 /eqP=>->.  

have : unf_recs (g[GRec g]) = GMsg a s g0[GRec g]. admit.
move => H3. move : H3 Heqn=>->. 
rewrite /unf_recs_aux. 
destruct ( unf_recs_aux (mu_height g) (g) [GRec g]) eqn:Heqn2. 
 
have : g = GVar n. case : g Heqn2 Heqn; try done.  
move => g. intros. move <-. rewrite /=.
rewrite /unf_recs_aux -/unf_recs_aux.
Lemma path_to_rec : forall g ge p, path (grel g_next) g p -> ge = last g p -> path (grel g_next) (GRec g) (seq_subst p (GRec g)) /\ ge[GRec g] = last (GRec g) (seq_subst p (GRec g)).





Check nodes_of.
Lemma mem_undup : forall (A : eqType) (l : seq A) (a : A), (a \in (undup l)) = (a \in l).
Proof. 
move => A. elim. 
- by rewrite /=.
- move => a l IH a0.  rewrite /=. case: (@idP (a \in l)). 
 + intros. rewrite IH inE. case : (eqVneq a0 a). move=>->. by rewrite /=. 
   by rewrite /=. 
 + move => H. rewrite inE. case : (eqVneq a0 a). move=>->. by rewrite inE eqxx.  
   rewrite /= IH inE. case : (a0 == a); by rewrite /=. 
Qed.

Lemma nodes_of_spec : forall g ge, reachable g ge <-> ge \in nodes_of g.
Proof.
move => g ge. split.
- intros. 
  rewrite /nodes_of. rewrite mem_undup. apply/flattenP.
  move : (reach_1_s H)=> [] s Hin Hreach. rewrite /reachable /reachable_aux. move => [] p Hp [] H1 H2.

  rewrite /rec_depth.  case : (reachable_to_lt g). intros. 
  move : (p _ H). move/reachable_lt_s=> [] ges H1. exists ges. apply/reachable_in_traject_in. done. done. 
- rewrite /nodes_of mem_undup /rec_depth. case : (reachable_to_lt g). move => x H. move/flattenP=> [] s.
  intros.  apply/reach_s_1. eauto. apply/in_traject_reachable.  eauto. 
Qed.






Lemma g_in_enum : forall n (g : gType U), g \in gType_enum n g.
Proof.
elim. rewrite /=. move => g. by rewrite inE eqxx. 
move => n. intros. by rewrite /= inE eqxx. 
Qed.



Lemma next_in_enum : forall (g'' g g' : gType U) n, g \in gType_enum n g'' -> 
                                            g'' \in g_next g' -> g \in gType_enum n.+1 g'.
Proof.
move => g'' g g' n. 
(*case : (gType_sizegt0 g''). move => x H ->. 
case : (gType_sizegt0 g'). move => x1 H1 ->. *)
rewrite /=. move => Hg. rewrite /g_next.
case Hg' : (unf_recs g'); do ? by rewrite in_nil. 
 + move => Heq. move : Heq Hg'. rewrite inE. move/eqP=><-. 
   by rewrite inE Hg orbC. 
 + move => Hin. rewrite inE. apply/orP. right. 
   apply/flattenP. exists (gType_enum n (g'')). apply/mapP.
   exists g''. done. done. by rewrite Hg. 
Qed.


Check (grel next2).




Lemma rem_recs_le : forall g, gType_size (rem_recs g) <= gType_size g.
Proof.
elim; do ? by rewrite /=.
Qed.



Lemma g_next_rem_size : forall g g', g' \in g_next_rem g -> gType_size g' <= gType_size g.
Proof.
move => g g'.  rewrite /g_next_rem. destruct (rem_recs g) eqn:Heqn;do ? by rewrite in_nil.
- rewrite inE. move/eqP=>->. rewrite (leq_trans _ (rem_recs_le g)) //= Heqn //=.   
  move => Hin. rewrite (leq_trans _ (rem_recs_le g)) //= Heqn /=.
  clear Heqn. 
  elim : l Hin; first by rewrite in_nil.
  move => a0 l H. rewrite inE. move/orP. case. 
 + move/eqP=>->. rewrite /= addnC -addnA. rewrite leq_addr //=. rewrite /=. rewrite [gType_size _ + _]addnC addnA addnC. 
   
   move/H=> H'. rewrite (leq_trans H') //=. rewrite leq_addl //=. 
Qed.


Lemma rem_path : forall (g : gType U) p, path (grel g_next_rem) g p -> size p <= gType_size g.
Proof. 
Admitted.


(*
Lemma enumP : forall (g g': gType U) n, (exists p, path (grel g_next) g p /\ g' = last g p /\ size p <= n) -> 
exists2 p', path (grel g_next) g p' & 

L*)
(*Lemma next2P : forall p (g : gType U), path (grel g_next) g p -> exists (p' : seq (gType U * gType U)), path my_rel (g,g) p'. *)

Lemma enumP1 : forall (g g': gType U) n, (exists p, path (grel g_next) g p /\ g' = last g p /\ size p <= n) -> g' \in gType_enum n g.
Proof.
move=> g g' n.  case. move => x. move : g g' n. elim : x.
- rewrite /=. move => g g' n [] _ [] ->. by rewrite g_in_enum.
- rewrite /=. move => a l H g g' n [] /andP. case. intros. case : b0. move => H'. 
  case : n. move/ltP.  lia. move => n H''. (* rewrite /=. H''. 
 (* rewrite H''.  *)  Search _ (_ < _). *)  apply : next_in_enum. apply H. split. eauto. split. done. done. done. 
Qed.

Lemma enumP2 : forall n (g g': gType U), g' \in gType_enum n g -> (exists p, path (grel g_next) g p /\ g' = last g p /\ size p <= n).
Proof. 
elim. 
move => g g'. rewrite /= inE. move/eqP=>->. exists [::]. rewrite /=. auto.
move => n IH g g'. rewrite /= inE. move/orP. case.
- move/eqP=>->. exists [::]. rewrite /=. auto.
- destruct (unf_recs g) eqn:Heqn; try by do ? rewrite in_nil.
 + intros. move : (IH _ _ b). case. intros. exists (g0::x).
   rewrite /= /g_next. by rewrite Heqn inE eqxx.
 + move/flattenP. case. move => x. move/mapP. case. move => x0 Hin -> Henum.
  move : (IH _ _ Henum). case. intros. exists (x0::x1).
  by rewrite /= /g_next Heqn Hin.
Qed.  

Lemma enumP_aux : forall (g g': gType U) n, reflect (exists p, path (grel g_next) g p /\ g' = last g p /\ size p <= n) (g' \in gType_enum n g).
Proof.

move => g g' n. apply Bool.iff_reflect. split.
- intros. apply enumP1. case : H. intros. case : p. intros. case : b. intros. eauto.
apply enumP2. 
Qed.

Lemma goal  : forall g p, path (grel g_next) g p -> size (shorten g p) < gType_size g.
Proof. Admitted.

(*simplify sublemmas needed for this*)
Lemma enumP: forall (g g': gType U), reflect (exists p, path (grel g_next) g p /\ g' = last g p) (g' \in gType_enum (gType_size g) g).
Proof.
move => g g'. case : (enumP_aux g g').
intros. constructor. case : p. move => x [] + []. eauto. 
intros. constructor. intro H. apply n. case : H. intros. exists (shorten g x).
split;auto. Check shortenP. case : p. intros. case : (shortenP a). intros. done.
case : p. 
split. Search _ (last _ (shorten _ _)). rewrite b. case : (shortenP a). intros. done. 
auto using path_size. 
Qed.

Lemma path_size : forall p (g : gType U) , path (grel g_next) g p -> exists p', path (grel g_next) g p' /\ last g p = last g p' /\ size p' << gType_size g. 
Proof. 
Admitted.

Lemma enumP: forall (g g': gType U), reflect (exists p, path (grel g_next) g p /\ g' = last g p) (g' \in gType_enum (gType_size g) g).
Proof.
move => g g'. case : (enumP_aux g g').
intros. constructor. case : p. move => x [] + []. eauto. 
intros. constructor. intro H. apply n. case : H. intros. exists (shorten g x).
split;auto. Check shortenP. case : p. intros. case : (shortenP a). intros. done.
case : p. 
split. Search _ (last _ (shorten _ _)). rewrite b. case : (shortenP a). intros. done. 
auto using path_size. 
Qed.


Lemma gType_enum_aux_self : forall (gs : seq (gType U))  (g : gType U) n, g \in gs -> g \in (gType_enum_aux n gs g).
Proof.

Lemma gType_enum_aux_self : forall (g : gType U) (gs : seq (gType U)) n, g \in (gType_enum_aux (n.+1) gs g).
Proof.
move=> g gs n. rewrite /=. case : (@idP (g \in gs));auto.
move=>Hnin. elim (g_next g). 
- by rewrite /= inE eqxx. 
- move => a l IH. rewrite /=. case : n IH. rewrite /=;auto. intros.  
  rewrite /=. intros. 
done. Definition gType_enum (g : gType U) := undup (filter (fun g_f : gType U => act_of_g g_f != None) (gType_enum_aux (gType_size g) nil g)).
End Enumeration.
