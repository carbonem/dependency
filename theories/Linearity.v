From Dep Require Import Global_Syntax.
From mathcomp Require Import all_ssreflect.
From Equations Require Import Equations.
From mathcomp Require Import fintype.
From deriving Require Import deriving.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Linearity.
Variable (U : countType). 
Variable (g : gType U).
Hypotheses (Hbound : bound g) (Hcont : contractive g).

Definition action_from (a : action) := let : Action p0 _ _ := a in p0.
Definition action_to (a : action) := let : Action _ p1 _ := a in p1.
Definition action_ch (a : action) := let : Action _ _ c := a in c.
Definition same_ch (a0 a1 : action) := action_ch a0 == action_ch a1.

Definition opt_rel (g0 g1 : gType U) (P : rel action) :=
if act_of_g g0 is Some a0
  then if act_of_g g1 is Some a1
    then P a0 a1
  else false 
else false.



Definition II_aux (a0 a1 : action) := (action_to a0 == action_to a1).
Definition II_spec (g0 g1 : gType U) := (grel g_next g0 g1) && opt_rel g0 g1 II_aux. 

Definition IO_aux (a0 a1 : action) := (action_to a0 == action_from a1).
Definition IO_spec (g0 g1 : gType U) := (grel g_next g0 g1) && opt_rel g0 g1 IO_aux. 

Definition OO_aux (a0 a1 : action) := (action_from a0 == action_from a1) && (action_ch a0 == action_ch a1).
Definition OO_spec (g0 g1 : gType U) := (grel g_next g0 g1) && opt_rel g0 g1 OO_aux. 

Definition in_dep_spec (g0 g1 : gType U) := (exists (g' : gType U), (exists2 p, path IO_spec g0 p & g' = last g0 p) /\ II_spec g' g1) 
                                      \/ II_spec g0 g1.

Definition OO_IO_spec (g g' : gType U) := OO_spec g g' || IO_spec g g'.
Definition out_dep_spec(g0 g1 : gType U) := exists2 p, path OO_IO_spec g0 p & g1 = last g0 p.

Definition linear_spec := 
forall (g0 g1 : gType U), (exists2 p, path (grel g_next) g p & g0 = last g p) ->
                     (exists2 p, path (grel g_next) g0 p & g1 = last g0 p) ->
                     opt_rel g0 g1 same_ch -> in_dep_spec g0 g1 /\ out_dep_spec g0 g1.
End Linearity. 
