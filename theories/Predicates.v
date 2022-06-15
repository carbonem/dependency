From mathcomp Require Import all_ssreflect zify.
From mathcomp Require Import finmap.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Dep Require Import NewSyntax Inductive_Linearity Substitutions.


Let inE := Inductive_Linearity.inE.


(*Lemma apply_allP : forall (A : eqType) (P : A -> bool) l x, all P l -> x \in l -> P x. intros. by apply (allP H). Qed.
Lemma apply_allP2 : forall (A : eqType) (P : A -> bool) l x (P0 : bool), P0 && all P l -> x \in l -> P x. 
intros. destruct (andP H). by apply (allP H2). Qed.

Hint Resolve apply_allP apply_allP2.

Lemma and_left : forall (b0 b1 : bool), b0 && b1 -> b0.
Proof. intros. apply (andP H). Qed. 

Lemma and_right : forall (b0 b1 : bool), b0 && b1 -> b1.
Proof. intros. apply (andP H). Qed. 


Lemma true_right : forall (b : bool), b -> b && true.
Proof. intros. rewrite H. done. Qed.

Hint Resolve and_left and_right mem_nth true_right. 
*)





Fixpoint action_pred g :=
match g with 
| GMsg a u g0 => (~~ (ptcp_from a == ptcp_to a)) && action_pred g0
| GBranch a gs => (~~ (ptcp_from a == ptcp_to a)) && all action_pred gs
| GRec g0 => action_pred g0
| _ => true 
end.


Fixpoint size_pred (g : gType) :=
match g with 
| GMsg a u g0 => size_pred g0
| GBranch a gs => (0 < size gs) && all size_pred gs
| GRec g0 => size_pred g0
| _ => true
end.






Fixpoint rproject g p := 
match g with 
| GEnd => EEnd
| GMsg a u g0 => if p == (ptcp_from a) then EMsg Sd (action_ch a) u (rproject g0 p) 
                               else if p == (ptcp_to a) then EMsg Rd (action_ch a) u (rproject g0 p) else rproject g0 p
| GBranch a gs => if p == (ptcp_from a) then EBranch Sd (action_ch a) (map (fun g => rproject g p) gs)
                                else if p == (ptcp_to a) then EBranch Rd (action_ch a) (map (fun g => rproject g p) gs) else if gs is g'::gs' then rproject g' p else EEnd
| GRec g => (ERec (rproject g p))
| GVar n => EVar n
end.


Definition shiftdown := ren_endpoint predn.

Check id. Check scons GEnd GVar.
(*Fixpoint prep (g : gType) :=
match g with
| GVar j => GVar j
| GEnd => GEnd
| GMsg a u g0 => GMsg a u (prep  g0)
| GBranch a gs => GBranch a (map prep gs) 
| GRec g0 => GRec (subst_gType (scons GEnd GVar) (prep g0))
end. 

Fixpoint gType_fv_aux (g : gType) :=
match g with
| GVar j => [fset j]
| GEnd => fset0
| GMsg _ _ g0 => gType_fv_aux g0
| GBranch _ gs => \bigcup_( i <- map gType_fv_aux gs) i 
| GRec g0 => gType_fv_aux g0
end. 

Definition new_fv g := gType_fv_aux (prep g).*)



(*Fixpoint endpoint_fv i (e : endpoint) :=
match e with
| EVar j => if i <= j then [fset j - i] else fset0
| EEnd => fset0
| EMsg _ _ _ g0 => endpoint_fv i g0
| EBranch _ _ gs => \bigcup_( i <- map (endpoint_fv i) gs) i 
| ERec g0 => (endpoint_fv i.+1 g0)
end. *)

Definition predn_opt n := if n is n'.+1 then Some n' else None.

Lemma predn_inj : injective predn_opt.
Proof.
move => x. intros. destruct x. destruct x2. done. simpl in H. done. destruct x2.  simpl in H. done. simpl in H. inversion H. subst. done. 
Qed.


Print pmap. Check oapp.



(*Lemma efv_test : forall e, endpoint_fv (ERec e) = endpoint_fv (subst_endpoint (scons EEnd EVar ) e). 
Proof. Admitted.*)

(*Lemma efv_test2 : forall e, endpoint_fv (subst_endpoint sigma e) = sigma @` (endpoint_fv e).*)
(*Fixpoint gType_fv (g : gType) :=
match g with
| GVar j => [::j]
| GEnd => nil
| GMsg _ _ g0 => gType_fv g0
| GBranch _ gs => flatten (map gType_fv gs)
| GRec g0 =>  map predn (filter (fun g => g != 0) (gType_fv g0))
end. *)

(*Fixpoint clean e := 
match e with 
| EMsg d c v e0 => EMsg d c v (clean e0)
| EBranch d c es => EBranch d c (map clean es)
| ERec e0 => if clean e0 == EVar 0 then EEnd else if 0 \in endpoint_fv e0 then ERec (clean e0) else  (clean e0) ⟨ predn ⟩ 
| EVar j => EVar j
| EEnd => EEnd
end.  *)


Lemma mem_imfset2
     : forall (K T : choiceType) (f : T -> K) (p : {fset T }),
       forall x : T, (x \in p) -> (f x \in f @` p).
Proof.
intros. Search _ Imfset.imfset. apply in_imfset. done.  
Qed.
Ltac fsetTac :=  apply/fsetP=>k;rewrite ?inE /=;try lia.

Definition bool_iff := Bool.eq_iff_eq_true.


Lemma predn_fset0 (A B : choiceType) (f : A -> B):  f @` fset0 = fset0.
Proof. 
fsetTac. rewrite Imfset.imfsetE /=. rewrite seq_fsetE !inE //=.  
Qed.

(*Lemma endpoint_rename : forall e,  endpoint_fv (ren_endpoint predn e) = predn @` endpoint_fv e.
Proof. 
elim;rewrite /=;intros. rewrite Imfset.imfsetE /=. fsetTac. rewrite seq_fsetE.
apply bool_iff. split. move/eqP=>->. rewrite map_f //=. rewrite !inE //=. 
move/mapP=>[]. intros. rewrite !inE in p. rewrite -(eqP p) -q //= eqxx //=.
rewrite predn_fset0 //=.
f_equal.*)

(*Lemma fv_shiftdown : forall e i, i \notin (endpoint_fv i e)  -> endpoint_fv i (shiftdown e) = endpoint_fv i.+1 e.
Proof. 
elim;rewrite /=;try done;intros.
move : H. rifliad;rewrite !inE;intros. all : try fsetTac. 
rewrite -H //=. asimpl.  rewrite /shiftdown.
 asimpl. f_equal. clear H0. clear H. rewrite /scons.
fext.  intros. 
Admitted.
*)
(*Lemma endpoint_subset : forall e i j, i <= j -> endpoint_fv j e `<=` endpoint_fv i e.
Proof. Admitted.*)

Lemma imfsetP2 (T K : choiceType) (f : T -> K) (S : {fset T}) (k : K) :
  reflect (exists2 x : T, x \in S & k = f x) (k \in f @` S).
Proof. apply/imfsetP. Qed.


Lemma false_b : forall (b : bool), (false = b) <-> ~ b. 
Proof. destruct b;split;done. Qed.

Lemma true_b : forall (b : bool), (true = b) <-> b. 
Proof. destruct b; split;done. Qed.

Let bbrw := (false_b,true_b).

(*Lemma fv_predn : forall e, endpoint_fv e ⟨ predn ⟩ = [fset predn n | n in endpoint_fv e].
Proof. intros. fsetTac. destruct (k \in endpoint_fv e ⟨ predn ⟩) eqn:Heqn;rewrite Heqn /= bbrw.
apply/imfsetP.
elim : e k Heqn;intros.
- exists n. rewrite /= !inE //=. move : Heqn. rewrite /= !inE //=. lia.
- rewrite /= !inE //= in Heqn. 
- rewrite /= ?inE in Heqn.
  exists k. rewrite /=. move : Heqn. asimpl. move => HH.  
  have :  (k \in endpoint_fv e ⟨e predn ⟩). admit. move/H=>[]. move => x. simpl.
  intros. apply/imfsetP. exists x. simpl. rewrite !inE /=. split_and. 
  have : ( 0 .: predn >> succn ) = (0 .: id). fext. intros.  case. done. intros. simpl. destruct n. asimpl.  simpl. done.
asimpl_in Heqn. rewrite /= !inE //=. move : Heqn. rewrite /= !inE //=. lia.

 -
  elim;intros.
fsetTac. destruct (eqVneq k n.-1). rewrite bbrw.  
apply/imfsetP. exists n. simpl. rewrite !inE //=. done. 
rewrite bbrw.  move/imfsetP. move=>[] x. simpl. rewrite !inE. move/eqP=>->. lia. 
simpl. fsetTac. rewrite bbrw. move/imfsetP=>[] x. simpl. rewrite !inE //=.
fsetTac. asimpl.*)

(*Lemma subst_nop : forall e e' x, x \notin (fv e) -> subst_e x e e' = e. Proof. 
elim;rewrite /=;try done;intros. move : H. rewrite !inE.  rewrite neg_sym. move/negbTE=>->. done. 
move : H0. rewrite !inE. move/orP=>[]. by rewrite eq_sym=>->.  
intros. rifliad. rewrite H //=. 
f_equal. auto. f_equal. rewrite big_map in H0.  induction l. done. simpl. f_equal.  apply H.  rewrite !inE.  lia. simpl in H0. move : H0. 
rewrite big_cons. rewrite !inE. split_and. apply IHl. intros. apply H. rewrite !inE H1. lia. done. move : H0.  rewrite big_cons !inE. split_and. 
Qed.*)




(*Lemma fv_subst : forall  e e' n x, fv e' = fset0 -> n <> x -> (n \in (fv (subst_e x e e'))) = (n \in (fv e)).
Proof. elim;rewrite /=;try done;intros. rewrite !inE. rifliad. rewrite H !inE. have : n0 == n = false by lia. by move=>->. 
rewrite /= !inE. done. 
rifliad. rewrite /=. Check mem_map. Search (_ \in (map _ _)). Search _ (_ \in _ = _ \in _).  Search _ ((is_true _ -> is_true _) -> _ = _). rewrite !inE.  destruct (n0 != n)eqn:Heqn;rewrite /= //=.   rewrite Heqn //=.
apply H. done. done. rewrite Heqn //=. 
rewrite !big_map.  elim : l H. rewrite !big_nil. done. intros. rewrite !big_cons. rewrite !inE. rewrite H2 //=. 
destruct ( (n \in fv a)) eqn:Heqn; rewrite !Heqn //=. apply H. intros. apply H2. rewrite !inE H3. lia. done. done. 
Qed.*)

(*Lemma fv_nil_evar : forall e n, endpoint_fv 0 e = fset0 -> e <> EVar n. 
Proof.
elim;rewrite /=;try  done. intros. have : n \in [fset n]. by  rewrite !inE. move : H. have : n - 0 = n by lia. move=>->. move/fsetP=>->. done. 
Qed.

Lemma fset_nil : forall (A : choiceType) (n : A), [fset n] = fset0 -> False.
Proof. intros. move : H. move/fsetP=>HH. suff : n \in [fset n] = (n \in fset0). rewrite !inE eqxx //=. done. 
Qed.
*)
(*Lemma clean_up : forall e sigma, clean (endpoint_ren e S) [↑__endpoint sigma] = (clean e) [↑__endpoint sigma].*)

(*Lemma in_subst : forall e sigma, (endpoint_fv (e [e sigma])) = sigma @` (endpoint_fv e).*)


(*Lemma in_subst : forall v e n sigma, v \in (endpoint_fv e) ->  sigma v = EVar n ->  n \in (endpoint_fv (e [e sigma])). 
Proof. 
move => v e. elim : e v;asimpl;intros. rewrite !inE in H. rewrite -(eqP H) H0 //= !inE //=. 
rewrite !inE //= in H.
rewrite /endpoint_fv -/endpoint_fv. rewrite seq_fsetE. Search _ (_ \in pmap _ _). rewrite mem_pmap. apply/mapP.  exists v. 
move : H0. rewrite /endpoint_fv -/endpoint_fv.  rewrite seq_fsetE mem_pmap. move/mapP=>[]. intros. apply : H. eauto. 
destruct x. done.  simpl. asimpl. simpl in q. done. simpl. substify. asimpl.

move : H0. simpl. rewrite mem_map.
simpl. rewrite fsetE.*)

(*

asimpl. simpl. symmetry. case_if. rewrite -(eqP H2). 
  move : H1. destruct (clean e);rewrite /=;asimpl. destruct n.  done. simpl. asimpl. destruct (sigma n);rewrite /=;asimpl. 
  destruct n0. all : try done. rifliad. substify. move/eqP. rewrite /shiftdown. asimpl. move : H1. substify. asimpl. rewrite H. 
  

have :  subst_endpoint (scons (var 0) (sigma >> (⟨ ↑ ⟩ >> clean)))  == var 0 = false.

case_if. 
  simpl. case_if. move : H2. 
asimpl. rs. done.
- rs. case_if.  
 * rs. rewrite (eqP H1) /=. rifliad. rs. by rewrite /= eqxx. rewrite subst_nop //=. rewrite fv_clean. lia. 
 * rs. rewrite /= H //=.  rewrite fv_subst //=. symmetry. case_if.
  ** rs. rewrite (eqP H2) /=. rs. rewrite H1 eqxx. done.
  ** case_if.
   *** rs. rewrite /= H1. rifliad. exfalso. move : H4.  destruct (clean e);rewrite /=;rs. rifliad. move/eqP. apply : fv_nil_evar. 
       rewrite fv_clean //=. by rewrite H2. done. done. done. rifliad. 

   *** rs. rifliad. exfalso. move : H5. rewrite !inE H3. have : n != x by lia. move=>->. done. rewrite !inE H3.
       have : n != x by lia. move=>-> /=. rifliad. 
       destruct (clean e);rewrite /=;rs.  rifliad. rewrite (eqP H5) in H4. rs_in H4. rewrite eqxx in H4. rewrite -fv_clean in H0.  rewrite (eqP H4) in H0. rs_in H0. by apply fset_nil in H0. rs_in H4. rewrite H5 in H4. lia. done.
      all : try  by move : (eqP H4).   rs_in H4. rifliad. rs. f_equal. auto.  rs. f_equal. 
- rewrite -!map_comp. apply/eq_in_map. move => ll Hin /=. rewrite H //=.
Qed.

Lemma clean_subst : forall (e0 : endpoint)  e' x, endpoint_fv 0 e' = fset0 -> clean (e0[s e'//x]) = (clean e0)[s clean e'//x].
Proof.
elim;intros. 
- rs. rifliad.
- rs. done.
- rs. case_if.  
 * rs. rewrite (eqP H1) /=. rifliad. rs. by rewrite /= eqxx. rewrite subst_nop //=. rewrite fv_clean. lia. 
 * rs. rewrite /= H //=.  rewrite fv_subst //=. symmetry. case_if.
  ** rs. rewrite (eqP H2) /=. rs. rewrite H1 eqxx. done.
  ** case_if.
   *** rs. rewrite /= H1. rifliad. exfalso. move : H4.  destruct (clean e);rewrite /=;rs. rifliad. move/eqP. apply : fv_nil_evar. 
       rewrite fv_clean //=. by rewrite H2. done. done. done. rifliad. 

   *** rs. rifliad. exfalso. move : H5. rewrite !inE H3. have : n != x by lia. move=>->. done. rewrite !inE H3.
       have : n != x by lia. move=>-> /=. rifliad. 
       destruct (clean e);rewrite /=;rs.  rifliad. rewrite (eqP H5) in H4. rs_in H4. rewrite eqxx in H4. rewrite -fv_clean in H0.  rewrite (eqP H4) in H0. rs_in H0. by apply fset_nil in H0. rs_in H4. rewrite H5 in H4. lia. done.
      all : try  by move : (eqP H4).   rs_in H4. rifliad. rs. f_equal. auto.  rs. f_equal. 
- rewrite -!map_comp. apply/eq_in_map. move => ll Hin /=. rewrite H //=.
Qed.*)

(*Lemma rproject_subst : forall g g0 p i,  rproject (g[s g0//i]) p = (rproject g p)[s (rproject g0 p)//i].
Proof. elim;rewrite /=;try done;intros;rs. rifliad. rifliad. rewrite /=.  rewrite H. done.  
rifliad. simpl. rs. f_equal. done. simpl. rs. f_equal. done. 
rifliad. simpl. rs. f_equal. 
rewrite -!map_comp. apply/eq_in_map. move=>ll Hin. simpl. apply H.  done. 
simpl. rs.  f_equal.
rewrite -!map_comp. apply/eq_in_map. move=>ll Hin. simpl. apply H.  done. destruct l. done. simpl. apply H. rewrite !inE. done. 
Qed.*)

(*
Lemma fv_rename : forall e f, endpoint_fv e ⟨ f ⟩ = [fset f n | n in (endpoint_fv e)].
Proof.
elim;rewrite /=;intros. fsetTac. destruct (eqVneq k (f n));rewrite bbrw.
apply/imfsetP. exists n. rewrite /= !inE eqxx. done. done.
move/imfsetP=>[] x.  rewrite /= !inE. move/eqP=>->. lia.
rewrite predn_fset0 //=. asimpl. Print up_ren. 
fsetTac. symmetry. destruct ( (k \in f @` [fset n.-1 | n in endpoint_fv e & n != 0])) eqn:Heqn;rewrite Heqn bbrw.
move : Heqn. move/imfsetP=>[] x /= H' H2. subst.  move : H'. move/imfsetP=>[] x0 /=. rewrite !inE /=.
split_and. subst.  rewrite H. 
simpl. apply/imfsetP. exists x0. rewrite /= !inE H1  andbC /=. rewrite H. 
apply/imfsetP. exists x0. simpl. done. destruct x0.  done. simpl. have : f = predn. admit. move=>->. destruct x0. done. asimpl. simpl. move : H'.rewrite !inE. split_and.  exists x0.  done. rewrite H2 q. destruct x0. done. 
 simpl.  asimpl. admit.
done. simpl. asimpl. 
simpl in q. subst.  simpl.
Lemma fv_clean : forall e, endpoint_fv (clean e) = endpoint_fv e. 
Proof. elim;try solve [rewrite /=;try done];intros. 
rewrite /=. rifliad;simpl. 
fsetTac. rewrite (eqP H0) /= in H. rewrite -H.   rewrite bbrw. move/imfsetP=>[] x. simpl. rewrite !inE. split_and. lia.
rewrite H. done. fsetTac. 
rewrite H. fsetTac.

rewrite (eqP H0) in H. simpl. simpl in H. rewrite -H. simpl in H.
fsetTac. apply/negP/negP. move=>_. move/imfsetP=>[]. move => x. simpl. rewrite !inE. split_and. lia. done. 
rewrite /shiftdown.  *)

(*move => H.  apply/negP.
have : [fset n.-1 | n in [fset 0] & n != 0] = [fset n.-1 | n in [fset 0]]. 
fsetTac. f_equal. rewrite /mem /=. f_equal. 
 Unset Printing Notations. Check mem. rewrite predn_fset0. rewrite -H //=.
fsetTac. Check inE. rewrite Imfset.imfsetE /= seq_fsetE /=. Set Printing Coercions.    rewrite enum_fsetE /=. Unset Printing Notations.
apply/negP/negP. move=>_. apply/negP. rewrite seq_fsetE. Set Printing Coercions. rewrite !inE. rewrite enum_fsetE /=.
unlock. simpl. rewrite seq_fset. unlock. fsetTac.  Search _ (seq_fset).  _ _ = _). rewrite  simpl. rewrite !inE. unlock tt.
rewrite /= H //=. rewrite fv_shiftdown. done. rewrite H. apply/negP=>HH.  apply negbT in H1. apply/negP. apply/H1. 
apply/fsubsetP. apply endpoint_subset. 2 : { eauto. } lia.
rewrite /=. rewrite !big_map. induction l. rewrite !big_nil //=. rewrite !big_cons. f_equal. apply H. done. 
apply IHl. auto. 
Qed.*)

(*Fixpoint project g p := 
match g with 
| GEnd => EEnd
| GMsg a u g0 => if p == (ptcp_from a) then EMsg Sd (action_ch a) u (project g0 p) 
                               else if p == (ptcp_to a) then EMsg Rd (action_ch a) u (project g0 p) else project g0 p
| GBranch a gs => if p == (ptcp_from a) then EBranch Sd (action_ch a) (map (fun g => project g p) gs)
                                else if p == (ptcp_to a) then EBranch Rd (action_ch a) (map (fun g => project g p) gs) else if gs is g'::gs' then project g' p else EEnd
| GRec g => if (project g p) == EVar 0 then EEnd 
           else if (*0 \notin fv (project g p)*) project g p == (project g p) ⟨1.:S⟩ then  (project g p) ⟨ predn ⟩  
                else   ERec( project g p)
| GVar n => EVar n
end.*)

Fixpoint project g p := 
match g with 
| GEnd => EEnd
| GMsg a u g0 => if p == (ptcp_from a) then EMsg Sd (action_ch a) u (project g0 p) 
                               else if p == (ptcp_to a) then EMsg Rd (action_ch a) u (project g0 p) else project g0 p
| GBranch a gs => if p == (ptcp_from a) then EBranch Sd (action_ch a) (map (fun g => project g p) gs)
                                else if p == (ptcp_to a) then EBranch Rd (action_ch a) (map (fun g => project g p) gs) else if gs is g'::gs' then project g' p else EEnd
| GRec g => if (project g p) == EVar 0 then EEnd 
            else   ERec( project g p)
| GVar n => EVar n
end.

Lemma match_n : forall (gs : seq gType) k,  match gs with
  | [::] => EEnd
  | g'0 :: _ => project g'0 k end = project (nth GEnd gs 0) k.
Proof.
elim. done. intros. rewrite /=. done.
Qed.

(*Lemma free : forall e, e ⟨0.:sigma ⟩ =  e ⟨1.:sigma ⟩ -> *)

Lemma zero_cons : forall (e : endpoint) , e⟨e 0.:succn⟩ = e.
Proof.
elim;intros.
asimpl. f_equal. destruct n;done.  done. asimpl. f_equal. done. asimpl. f_equal. done.
asimpl. f_equal. induction l;try done. simpl. f_equal.  apply H. auto. auto.  
Qed.

Lemma inj_rem : forall e0 e1 f f', injective f  -> e0 ⟨e f⟩ = e1 ⟨e f⟩ -> e0 ⟨e f' ⟩ = e1 ⟨e f' ⟩.
Proof. 
elim. intros. destruct e1;try done.  f_equal. move : H0. asimpl. case. move/H. by move=>->. 
- case;try done.
- intros. asimpl.  destruct e1;try done. f_equal. move : H1.  asimpl. intros. f_equal. 
  apply : H. have : injective (0 .: f >> succn ).
  intro. intros. destruct x1;destruct x2. done. move : H.  asimpl.
done.  move : H. asimpl. done. f_equal. move : H. asimpl. case. move/H0. done. move => HH. apply : HH. 

(*intro. intros. destruct x1;destruct x2. done. move : H.  asimpl.
done.  move : H. asimpl. done. f_equal. move : H. asimpl. case. move/H1. done. *)
  move : H1.  asimpl. case. intros. eauto.
- intros. destruct e1;try done.
 move : H1.  asimpl. case. intros.  subst. f_equal. eauto. 
- intros. move : H1.  asimpl. destruct e1;try done. asimpl. case. intros. subst. f_equal.
  move : H3. elim : l l0 H;simpl. destruct l0. done. done. destruct l0. done. 
  simpl. intros. f_equal. apply : H1. auto. eauto. inversion H3. done.  apply H. 
  intros. apply : H1. eauto. eauto. eauto.  inversion H3. eauto. 
Qed.


Lemma inj_rem2 : forall e0 e1 f , injective f  -> e0 ⟨e f⟩ = e1 ⟨e f⟩ -> e0 = e1.
Proof. intros. have : e0 = e0 ⟨id⟩.  asimpl. done. move=>->. 
have : e1 = e1 ⟨id⟩. asimpl. done. move=>->. apply/inj_rem. eauto. eauto.
Qed.


(*Print scons.
Lemma scons_comp :forall (k : nat) sigma, scons k sigma = (fun n => if n == sigma 0 then k else if n == k.+1 then sigma n is n'.+1 then n' else k) >> sigma.
Proof. 
intros. fext.  destruct x. asimpl. done. asimpl. done. 
Qed.*)




(*e ⟨e 0 .: sigma >> succn ⟩ = e ⟨e 1 .: sigma >> succn ⟩ -> e ⟨e 0 .: succn ⟩ = e ⟨e 1 .: succn ⟩
*)

Lemma big_exists : forall (A : eqType) (B : choiceType) (l : seq A) (f0 : A -> {fset B}) p, p \in \bigcup_(j <- l) (f0 j) = has (fun x => p \in f0 x) l. 
Proof. 
move => A B. elim. move => f0 p. rewrite big_nil. done. intros. simpl. rewrite big_cons !inE. destruct ( (p \in f0 a) ) eqn:Heqn;rewrite /=. 
done.
apply H.
Qed.


Lemma inj_rem4 : forall e  f f' , 
(forall v, v \in endpoint_fv e -> f v = f' v) -> e ⟨e f⟩  = e ⟨e f'⟩ .
Proof.  
elim;intros.
- asimpl. rewrite H.  done. rewrite /= !inE //=. done.
asimpl. f_equal.  apply H.  intros. destruct v. done. asimpl. rewrite H0. done. 
simpl. apply/imfsetP. exists v.+1. simpl. rewrite !inE. split_and. done. asimpl. f_equal. apply H. auto. 
asimpl. f_equal. apply/eq_in_map. move => g. intros. apply H. done. intros.  apply H0.
simpl. rewrite big_map. rewrite big_exists. apply/hasP. exists g. done. done.
Qed.

Lemma inj_rem5 : forall e  f f' v , 
 e ⟨e f⟩  = e ⟨e f'⟩ ->  f v <> f' v -> v \notin endpoint_fv e.
Proof.  
elim;intros;rewrite /= ?inE;try done. move : H. asimpl. case. intros. destruct (eqVneq v n). subst. done. done. 
move : H0. asimpl. case. move/H=>HH. apply/negP. move/imfsetP=>[] x /=. rewrite !inE. split_and. 
specialize HH with v.+1.  move : HH. asimpl. move => HH. have : (f v).+1 <> (f' v).+1. move => H'. inversion H'. apply H1. 
done.  move/HH. subst. simpl. destruct x. done. simpl. simpl in *. rewrite H0 //=. 
apply: H. move : H0. asimpl. case. eauto. eauto.
rewrite big_map big_exists. move : H0. asimpl. case. move/eq_in_map=>HH.
apply/negP.  move/hasP=>[] x. intros. apply/negP. apply  H with (f:=f)(f':=f'). all : eauto. 
Qed.


Lemma inj_rem4' : forall e  f f' , 
(forall v, v \in endpoint_fv e -> f v = f' v) -> e [e f]  = e [e f'] .
Proof.  
elim;intros.
- asimpl. rewrite H.  done. rewrite /= !inE. done.
done. asimpl. f_equal.  apply H.  intros. destruct v. done. asimpl. rewrite H0. done. 
simpl. apply/imfsetP. exists v.+1. simpl. rewrite !inE. split_and. done. asimpl. f_equal. apply H. auto. 
asimpl. f_equal. apply/eq_in_map. move => g. intros. apply H. done. intros.  apply H0.
simpl. rewrite big_map. rewrite big_exists. apply/hasP. exists g. done. done.
Qed.

Lemma inj_rem5' : forall e  f f' v , 
 e [e f]  = e [e f'] ->  f v <> f' v -> v \notin endpoint_fv e.
Proof.  
elim;intros;rewrite /= ?inE;try done. move : H. asimpl. case. intros. destruct (eqVneq v n). subst. done. done. 
move : H0. asimpl. case. move/H=>HH. apply/negP. move/imfsetP=>[] x /=. rewrite !inE. split_and. 
specialize HH with v.+1.  move : HH. asimpl. move => HH. have :  (f v) ⟨e ↑ ⟩ <> (f' v) ⟨e ↑ ⟩.  
 move => H'. apply inj_rem2 in H'. apply H1. done. intro. rewrite /shift.  intros. inversion H3. done. 
move/HH. subst. simpl. destruct x. done. simpl. simpl in *. rewrite H0 //=. 
apply: H. move : H0. asimpl. case. eauto. eauto.
rewrite big_map big_exists. move : H0. asimpl. case. move/eq_in_map=>HH.
apply/negP.  move/hasP=>[] x. intros. apply/negP. apply  H with (f:=f)(f':=f'). all : eauto. 
Qed.


(*elim;intros;rewrite /=;asimpl. move : H. asimpl. case. intros. f_equal. 
destruct n.  simpl in*.  done. simpl in *. done. done.
f_equal. move : H0. asimpl. case. intros. 
suff :  e ⟨e (i.+1 .: f >> succn) ⟩ = e ⟨e (j.+1 .: f >> succn) ⟩.
admit.  apply H. apply H in H0. 
suff :  e ⟨e (i.+1 .: f' >> succn) ⟩ = e ⟨e (j.+1 .: f' >> succn) ⟩.
admit.  apply : H0. apply : H. eauto. move : H1. asimpl. done. done.
.
apply H0. apply H in H1. done. done. apply H. 
- move : H1. destruct e1; asimpl;simpl; try done. case. intros. f_apply 
move : H1.  asimpl. destruct n;destruct n0. asimpl. done. asimpl. 
 done.destruct n;destruct n0;asimpl;try done.  move : H2. asimpl. intros. apply H0 in H2. done. 
move : H2.  asimpl. intros. specialize H1 with n. subst. liasetoid_rewrite H2 in H1. 
rewrite H0. move=>->.*)

(*Lemma testtest : forall e sigma (L : seq nat) i j,  (forall (k : nat), k \notin L -> (i .: sigma >> succn) k = (j .: sigma >> succn) k)  ->
  forall k, k \notin L -> (e i .: succn ) k = ( j.: succn ) k.
Proof.
elim;intros.
- move : H. asimpl. case. intros. f_equal. move : H.  destruct n. asimpl. done. asimpl. done. done. 
asimpl.
move : H0. asimpl. case. intros. f_equal. erewrite H.*)


Lemma project_ren : forall g p sigma, project (g ⟨ sigma ⟩) p = (project g p) ⟨ sigma ⟩.
Proof.
elim;intros.
- simpl. done.
- done.
- simpl. asimpl. rewrite H. symmetry. case_if.
 * rewrite (eqP H0) //=.
 * case_if.
  ** exfalso. move : H1 H0.  
     move/eqP. destruct (project g p);asimpl;rewrite /=. case. destruct n. asimpl. done. asimpl.
done. all : try done. 
simpl.
rifliad;asimpl;try done. f_equal. auto.  f_equal. auto. auto.
simpl. rifliad;asimpl;try done. f_equal. rewrite -!map_comp. apply/eq_in_map=>l'. intros. simpl.
apply H. done. 
 f_equal. rewrite -!map_comp. apply/eq_in_map=>l'. intros. simpl.
apply H. done. 
rewrite !match_n. induction l. done. simpl. apply H. auto. 
Qed.


Lemma project_subst : forall g p sigma, project (g[g sigma]) p = (project g p) [ sigma >> (fun g => project g p)].
Proof.
elim;intros.
- simpl. done.
- done.
- simpl. asimpl. rewrite H. symmetry. case_if.
 * rewrite (eqP H0) //=.
 * case_if.
  ** exfalso. move : H1 H0.  
     move/eqP. destruct (project g p);asimpl;rewrite /=. destruct n. asimpl. done. asimpl. simpl. 
     rewrite project_ren. all : try done. 
     destruct  (project (sigma n) p);simpl;asimpl.
     destruct n0. done. done. all : try done. 
     simpl. f_equal. asimpl. simpl. f_equal.
     fext. intros. destruct x. asimpl. done.
     asimpl. simpl. rewrite project_ren. done.
simpl.
rifliad;asimpl;try done. f_equal. auto.  f_equal. auto. auto.
simpl. rifliad;asimpl;try done. f_equal. rewrite -!map_comp. apply/eq_in_map=>l'. intros. simpl.
apply H. done. 
 f_equal. rewrite -!map_comp. apply/eq_in_map=>l'. intros. simpl.
apply H. done. 
rewrite !match_n. induction l. done. simpl. apply H. auto. 
Qed.






Definition fset_ptcp := {fset ptcp}.
Definition env := {fmap ptcp -> endpoint}.
Definition projmap  (S : fset_ptcp) (g : gType)  : env := [fmap p : S => project g (val p)].



From Paco Require Import paco.

(*Inductive UnravelE (r : endpoint -> endpoint -> Prop) : endpoint -> endpoint -> Prop :=
 | UEndE : UnravelE r EEnd EEnd
 | UMsgE d c u g0 sg0 : UnravelE r g0 sg0 -> UnravelE r (EMsg d c u g0) (EMsg d c u sg0)
 | UBranchE d c gs sgs : size gs = size sgs -> Forall (fun p => UnravelE r p.1 p.2) (zip gs sgs) ->  UnravelE r (EBranch d c gs) (EBranch d c sgs)
 | URecE g sg n : r g[e ERec n g//n] sg  -> UnravelE r (ERec n g) sg.
Hint Constructors UnravelE.
Notation unf := (paco2 UnravelE bot2).


Definition ueqe e0 e1 := exists e, unf e0 e /\ unf e1 e.*)
(**)
(*Reserved Notation "e0 =f= e1" (at level 60). *)


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



(*Fixpoint emu_height g :=
match g with
| ERec n g0 => (emu_height g0).+1
| _ => 0
end.*)

(*Definition eunf g := if g is ERec n g' then (g'[s ERec n g'//n]) else g.

Lemma emu_height_subst : forall g0 g1  i, eguarded i g0 -> econtractive g0 -> emu_height (g0[s g1//i]) = emu_height g0.
Proof. 
elim; try solve [by rewrite /=].
- rewrite /=. rs.  intros. split_and. rewrite (negbTE H). done. 
- intros. simpl. simpl in H0. rs. split_and. destruct (i == n) eqn:Heqn.  rewrite eq_sym Heqn. done.  
  simpl in H1. rifliad. rs. split_and. 
Qed.


Lemma fsubset_in : forall (A : choiceType) (b c : {fset A}), b `<=` c -> (forall j, j \in b -> j \in c).
Proof.
intros. Search _ fsub1set. move : H0. rewrite -!fsub1set.  intros. apply : fsubset_trans. apply : H0. apply H. 
Qed.*)

(*Lemma efv_subst : forall (g : endpoint) g0 n, fv g0 `<=` fv g  -> fv (g[s g0 // n]) = fv g `\ n. 
Proof. 
elim;rewrite /=;rs;intros;apply/fsetP=>k;rewrite !inE.
- rifliad. rewrite (eqP H0). move : H.  move/fsubset_in =>HH. rewrite -(eqP H0). specialize HH with k. rewrite !inE in HH. 
destruct (k \in fv g0). destruct (eqVneq k n). simpl. specialize HH with k. rewrite -HH. move/fsubset_ rewrite /bound. move/eqP=>->. rewrite !inE. by destruct (eqVneq k n0).
- rewrite /= !inE. destruct (eqVneq k n). subst. lia. lia. 
- lia.
- rifliad. rewrite /= (eqP H1) !inE. destruct (k != n0);rewrite /=. done. done.
- rewrite /= H //= !inE. destruct (k != n);rewrite /=;try lia.  rewrite H //= !inE. done.
- rewrite !big_map. induction l. rewrite !big_nil !inE. lia. 
  rewrite !big_cons !inE H //= !inE. destruct (k != n);rewrite /=. destruct (k \in fv a) eqn:Heqn;rewrite Heqn //=.
  rewrite /= in IHl. apply IHl. intros. apply H. eauto. done. rewrite /= in IHl. apply IHl. intros. apply H. eauto. done.
Qed.*)

(*Lemma fv_subst : forall g g0 n, ebound g0 -> fv (g[e g0 // n]) = fv g `\ n. 
Proof. 
elim;rewrite /=;intros;apply/fsetP=>k;rewrite !inE.
- rifliad. rewrite (eqP H0). move : H.  rewrite /bound. move/eqP=>->. rewrite !inE. by destruct (eqVneq k n0).
- rewrite /= !inE. destruct (eqVneq k n). subst. lia. lia. 
- lia.
- rifliad. rewrite /= (eqP H1) !inE. destruct (k != n0);rewrite /=. done. done.
- rewrite /= H //= !inE. destruct (k != n);rewrite /=;try lia.  rewrite H //= !inE. done.
- rewrite !big_map. induction l. rewrite !big_nil !inE. lia. 
  rewrite !big_cons !inE H //= !inE. destruct (k != n);rewrite /=. destruct (k \in fv a) eqn:Heqn;rewrite Heqn //=.
  rewrite /= in IHl. apply IHl. intros. apply H. eauto. done. rewrite /= in IHl. apply IHl. intros. apply H. eauto. done.
Qed.*)


(*Lemma bound_subst : forall (g : endpoint) g' i, fv g = [fset i] -> bound g' -> bound (g[s g'//i]).
Proof. intros. move : H0. rewrite /bound. move/eqP=>HH. rewrite -HH. apply/eqP.  rewrite fv_subst. rewrite H HH. apply/fsetP=>k. rewrite !inE. destruct (eqVneq k i);done.  rewrite /bound. done. 
Qed.

Lemma notin_eguarded : forall g n, n \notin fv g  -> eguarded n g.
Proof. elim;rewrite /bound //=;intros. move : H. rewrite !inE. lia. move : H0. rewrite !inE. move/orP=>[]. lia. intros.  
rewrite H //=. lia. 
Qed.

Implicit Type (g : endpoint).

Lemma bound_notin : forall g n, bound g -> n \notin fv g.
Proof. intros. rewrite /bound in H. rewrite (eqP H) !inE. done. Qed.
Lemma bound_eguarded : forall g n, bound g  -> eguarded n g.
Proof. intros. apply notin_eguarded. apply bound_notin. done. Qed.

Lemma eguarded_subst : forall g g' n i, eguarded n g -> bound g' -> eguarded n (g)[s g' // i].
Proof. elim;rewrite /=;intros. rs. rifliad. apply bound_eguarded. done. done. rs. rifliad. rs. 


destruct (orP H0). by rewrite H3.  rewrite H //=. lia. done. done.
Qed.



Lemma econtractive_subst : forall g g' i, (*i \in fv g ->*) econtractive g -> econtractive g' -> bound g' -> econtractive (substitute i g g').
Proof.
elim;  (try solve [rewrite /= ;auto]).
- rewrite/=;rs. move => v g' i j. case : (eqVneq v i).  done. simpl. done.
- intros. rewrite /=. rs. rifliad. simpl. split_and. simpl in H1. split_and. apply eguarded_subst. simpl in H0. split_and. done.  apply H. simpl in H0. move : H0. split_and. done. done. 
- rewrite /=. rs. intros. move : H0. intros. rewrite all_map. apply/allP=> l' Hin. simpl. apply H;auto.  
  apply (allP H0). done. 
Qed.

Lemma bound_econtractive_subst : forall g0 g1 i, fv g0 = [fset i] -> bound g1 ->   econtractive g0 -> econtractive g1 ->  bound (g0[s g1//i]) && econtractive (g0[s g1//i]).
Proof.
intros.  split_and. apply bound_subst;auto. apply econtractive_subst;auto.  
Qed.


Notation e_pred g := (bound g && econtractive g). 


(*Lemma substitute_nop : forall g g' x, x \notin (fv g) -> substitute x g g' = g. 
Proof. 
elim;rewrite /=;try done;intros. move : H. rewrite !inE.  rewrite neg_sym. move/negbTE=>->. done. 
move : H0. rewrite !inE.  move/orP=>[]. intros. by  rewrite eq_sym a. rifliad. intros. f_equal. auto. f_equal. 
auto.
f_equal. rewrite big_map in H0.  induction l. done. simpl. f_equal.  apply H.  rewrite !inE.  lia. move : H0. 
rewrite big_cons. rewrite !inE. split_and. apply IHl. intros. apply H. rewrite !inE H1. lia. done. move : H0.  rewrite big_cons !inE. split_and. 
Qed.*)

Lemma eunf_pred : forall g , e_pred  g -> e_pred (eunf g).
Proof.
intros. rewrite /eunf. destruct g. move : (andP H)=>[];intros.  apply/andP. split. simpl. simpl in a. lia. simpl in *. lia. 
- done.
- simpl in *. split_and. done. destruct (n \notin (fv g)) eqn:Heqn.  rewrite subst_nop //=.  move : H.  rewrite /bound /=. rewrite /=. rs.
  rewrite mem_fsetD1 //=.  rs. split_and. 

 split_and. apply bound_subst. move : H0. rewrite /bound. rs. intros. apply/fsetP=>k. rewrite !inE. 
  destruct  (eqVneq k n). subst. have : n \in fv g. lia. done. have : false = (k \in fset0).  done. move=>->. move : H0. move/eqP/fsetP=>H0. rewrite -H0. rewrite !inE i /=. done. 
  done. apply econtractive_subst.  simpl in H1. split_and. done. done. 
Qed.


Lemma eiter_pred : forall k e,  e_pred e -> e_pred (iter k (fun g => eunf g) e).
Proof. elim;rewrite /=;intros. apply/andP.  destruct (andP H). split;auto. 
apply eunf_pred. apply H. done. 
Qed.


Lemma emu_height_eunf : forall g , e_pred g -> (emu_height g).-1 = emu_height (eunf g).
Proof.
move => g. rewrite /=. elim : g; try solve [intros;rewrite /=;done].
- intros. rewrite /eunf. rs.  rewrite /=. rs. split_and. simpl in H1,H2. split_and. rewrite emu_height_subst. done. done. done. 
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

Notation full_eunf g := (iter (emu_height g) (fun g' => eunf g') g). *)


(*Definition next g :=
match full_eunf g with 
| EMsg _ _ _ g0 => [::g0]
| EBranch _ _ gs => gs
| _ => [::]
end.*)

(*
Definition act_of g :=
match full_eunf g with 
| EMsg _ a _ _ => inr a
| EBranch _ a _ => inr a
| EVar n => inl (Some n)
| _ => inl None
end.
*)

(*Fixpoint act_of g :=
match g  with 
| EMsg _ a _ _ => inr a
| EBranch _ a _ => inr a
| ERec g0 => act_of g0 
| EVar n => inl (Some n)
| _ => inl None
end.*)


Definition ptcp_le (p0 p1 : ptcp) := let: Ptcp n0 := p0 in let: Ptcp n1 := p1 in n0 <= n1.

  Lemma nat_list_max : forall (xs : list ptcp),
    { n : ptcp | forall x, x \in xs -> ptcp_le x  n }.
  Proof.
    induction xs as [ | x xs [y H] ].
    (* case: nil *)
    exists (Ptcp 0). inversion 1.
    (* case: cons x xs *) destruct x,y.
    exists (Ptcp (n + n0)%nat). intros z J. move : J. rewrite inE. move/orP=>[]. move/eqP=>->. rewrite /=. lia. move/H. rewrite /ptcp_le. destruct z.  lia. 
   Qed.

 Lemma atom_fresh_for_list :
    forall (xs : list ptcp), { n : ptcp | ~ n \in xs }.
  Proof.
    intros xs. destruct (nat_list_max xs) as [x H]. destruct x. exists (Ptcp (n.+1)).
    intros J. rewrite /ptcp_le in H. apply H in J. lia. 
  Qed. 
Definition fresh (S : fset_ptcp) :=
    match atom_fresh_for_list S with
      (exist x _ ) => x
    end.


Fixpoint project_pred  (g : gType):=  
match g with 
| GMsg a u g0 => project_pred g0 
| GBranch a gs => let S := ptcps g in 
                 all (fun (g' : gType)  => 
                         all (fun p => bisim_dec (project (nth GEnd gs 0) p) (project g' p)) 
                         (fresh S |` (S `\` a )))
                      gs 
(*                 (all (fun (g : gType) => fv (nth GEnd gs 0) == fv g) gs)*)
                 && (all project_pred gs)
| GRec g0 => project_pred g0
| _ => true 
end.



Fixpoint same_vars (e : endpoint ) :=
match e with 
| EBranch d c l => all (fun e' => endpoint_fv (nth EEnd l 0) == endpoint_fv e') l && (all same_vars l)
| EMsg _ _ _ e0 => same_vars e0
| ERec e0 => same_vars e0
| _ => true 
end.

Fixpoint same_varsg (e : gType ) :=
match e with 
| GBranch c l => all (fun e' => gType_fv (nth GEnd l 0) == gType_fv e') l && (all same_varsg l)
| GMsg _ _ e0 => same_varsg e0
| GRec e0 => same_varsg e0
| _ => true 
end.



(*Lemma in_foldr : forall l n,  n \in foldr (fun g' : gType => cat (fv_g g')) nil l ->  exists g, g \in l /\ n \in (fv_g g).
Proof. elim;try done;move => l n H n'.
rewrite /= mem_cat. move/orP=>[]. intros. exists l. rewrite !inE /= a. auto.
move/H. move=>[] x [].  intros. exists x. rewrite !inE a b. lia. Qed.*)

(*Lemma in_foldr2 : forall l n p g, g \in l -> n \in (fv (project  g p)) ->  n \in foldr (fun g' : gType => cat (fv (project g' p))) nil l.
Proof. elim;try done;intros. move : H0.
rewrite !inE. move/orP=>[]. move/eqP. intros. subst. simpl. rewrite mem_cat H1. done. intros.  simpl. rewrite mem_cat. apply/orP. right. apply : H. eauto. done. 
Qed.*)


(*
Lemma fv_project_in : forall g p n, lpreds rec_pred g ->  (n \in (fv_g g)) -> (n  \in (fv (project g p))).
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

Lemma fv_project_eq : forall g p n, lpreds rec_pred g ->  (n \in fv_g g) = (n \in fv (project g p)).
Proof. intros. destruct ( (n \in fv_g g)) eqn:Heqn. rewrite fv_project_in //=.
destruct ((n \in fv (project g p))) eqn:Heqn2. erewrite fv_rproject_in in Heqn. done. eauto. done. 
Qed.*)



(*Lemma fv_g_unf : forall g g0 n, bound g0 -> fv_g (g[g g0 // n]) = fv_g g `\ n. 
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


(*
Inductive unf_eq : endpoint -> endpoint -> Prop :=

(*Use Pierces algorithm*)
Inductive unf_eq : endpoint -> endpoint -> Prop :=
 | UEE : EEnd =f= EEnd
 | UEV n :  (EVar n) =f= (EVar n)
 | UEM u g0 g0' d c : g0 =f= g0' -> (EMsg d c u g0) =f= (EMsg d c u g0')
 | UEB gs gs' d c : esize gs = esize gs' -> Forall (fun p => p.1 =f= p.2) (zip gs gs') ->   (EBranch d c gs) =f= (EBranch d c gs')
 | UER2 g g' n : g' =f= g'  -> (ERec n g) =f=  (ERec n g')
 | UERL g g' n : g[s ERec n g//n] =f= g'  -> (ERec n g) =f=  g'
 | UERR g g' n : g =f= g'[s ERec n g'//n]  -> g =f= (ERec n g')
 where "e0 =f= e1" := (unf_eq e0 e1).
Set Elimination Schemes.
Hint Constructors unf_eq.


Lemma unf_eq_ind
     : forall P : endpoint -> endpoint -> Prop,
       P EEnd EEnd ->
       (forall n : nat, P (EVar n) (EVar n)) ->
       (forall (u : value) (g0 g0' : endpoint) (d : dir) (c : ch), g0 =f= g0' -> P g0 g0' -> P (EMsg d c u g0) (EMsg d c u g0')) ->
       (forall (gs gs' : seq endpoint) (d : dir) (c : ch),
        esize gs = esize gs' -> 
Forall (fun p : endpoint * endpoint => p.1 =f= p.2) (zip gs gs') -> 
Forall (fun p : endpoint * endpoint => P p.1  p.2) (zip gs gs') ->
P (EBranch d c gs) (EBranch d c gs')) ->

       (forall (g g' : endpoint) (n : nat), g' =f= g' -> P g' g' -> P (ERec n g) (ERec n g')) ->
       (forall (g : endpoint_substType) (g' : endpoint) (n : nat), (g)[s ERec n g // n] =f= g' -> P (g)[s ERec n g // n] g' -> P (ERec n g) g') ->
       (forall (g : endpoint) (g' : endpoint_substType) (n : nat), g =f= (g')[s ERec n g' // n] -> P g (g')[s ERec n g' // n] -> P g (ERec n g')) ->
       forall e e0 : endpoint, e =f= e0 -> P e e0.
Proof. 
intros. move : e e0 H6. fix IH 3. intros. destruct H6.
apply H. apply H0. apply H1. auto. auto. apply H2. done. 
done. induction H7. done. constructor. auto. done. apply H3. done. 
auto. apply : H4. done. auto. apply : H5. done. auto. 
Qed.


Fixpoint unf_dec e0 e1 :=
match e0,e1 with 
| EEnd,EEnd => true
| EVar n,EVar n' => n == n'
| EMsg d c u e0', EMsg d' c' u' e1' =>  (d == d') && (c == c') && (u == u') && (unf_dec e0' e1')
| ERec n e0', ERec n' e1' =>  if n == n' then unf_dec e0' e1'
                             else unf_dec (ERec n e0') (e1'[s ERec n' e1'])
 ( == d') && (c == c') && (u == u') && (unf_dec e0' e1')


(*Inductive Unravele (r : endpoint -> endpoint -> Prop) : endpoint -> endpoint -> Prop :=
 | UEnde : Unravele r EEnd EEnd
 | UVar n : Unravele r (EVar n) (EVar n)
 | UMsge u g0 g0' d c :  r g0 g0' -> Unravele r (EMsg d c u g0) (EMsg d c u g0')
 | UBranche gs gs' d c : esize gs = esize gs' -> Forall (fun p => r p.1 p.2) (zip gs gs') ->  Unravele r (EBranch d c gs) (EBranch d c gs')
 | URece g g' n : r g[s ERec n g//n] g'  -> Unravele r (ERec n g) g'
 | URece2 g g' n : r g g'[s ERec n g'//n]  -> Unravele r g (ERec n g')
 | Utrans g0 g1 g2 : Unravele r g0 g1 -> Unravele r g1 g2 -> Unravele r g0 g2. (*Should be omitted later, probably not needed*)
Hint Constructors Unravele.
Notation "e0 =( R )= e1" := (Unravele R e0 e1)(at level 60).*)

(*Notation "e =f= e1" := (paco2 Unravele bot2 e e1)(at level 60).*)


(*Notation eq_unf e0 e1 := (is_true (eunf e0 == eunf e1)).*)
(*Lemma ueqe_refl_unf : forall e e' i, bound e' -> e' =f= e' -> e =f= e /\ e[s e'//i] =f= e[s e'//i].
Proof. elim;rewrite/=;rs;intros. rifliad. auto. auto. auto.
rifliad. split. 
pfold. constructor. left. pfold. constructor. left. apply H in H0 as H'.
have : e =f= e /\ (e)[s e' // i] =f= (e)[s e' // i]. apply : H. done. done.
move=>[]. intros.
 apply/Forall_forall. intros. move : H. move/nthP=>Hnth. specialize Hnth with (EEnd,EEnd). destruct Hnth. rewrite -H0. rewrite nth_zip /=. right. apply CIH. done. pfold. constructor. left. pfold. constructor.  right. done. 
Qed.*)

Fixpoint eguarded n g := 
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

Lemma ueqe_refl : forall e,  e =f= e.
Proof. 
elim;rewrite /=;intros;try done. by  constructor. by constructor. constructor. done. apply/forallzipP. done. simpl. intros. have : (nth EEnd l x0) \in l. apply/mem_nth. done. move/H. eauto. 
Qed.

Hint Resolve ueqe_refl. 

Lemma ueqe_sym  : forall e0 e1, e0 =f= e1 ->  e1 =f= e0. 
Proof. intros. induction H;auto.  
constructor. done. Admitted.

Lemma ueqe_trans : forall e0 e1 e2, e0 =f= e1 -> e1 =f= e2 -> e0 =f=  e2.
Proof. Admitted.

Add Parametric Relation : endpoint (fun e0 e1 => e0 =f= e1)
  reflexivity proved by ueqe_refl
  symmetry proved by ueqe_sym
  transitivity proved by ueqe_trans
  as endpoint_setoid.


(*Lemma bool_true (b : bool) : b -> b = true.
destruct b. done. done. 
Qed.*)







Lemma monotone_ueqe : monotone2 Unravele.
Proof. intro. intros.  induction IN;auto.
constructor. done. induction H0. done. auto. eauto.   
Qed.

Hint Resolve monotone_ueqe : paco.

Lemma Unravele_r : forall e0 e1 r, paco2 Unravele bot2 e0 e1 -> paco2 Unravele r e0 e1.
Proof. pcofix CIH.
intros. pfold. apply : monotone_ueqe. punfold H0. intros. ich PR. right. apply CIH. done. Qed.

Hint Resolve Unravele_r.




Definition ueqe_dec (e0 e1 : endpoint) := true.

Lemma ueqeP e0 e1 : reflect (e0 =f= e1) (ueqe_dec e0 e1).
Proof. Admitted.
*)

