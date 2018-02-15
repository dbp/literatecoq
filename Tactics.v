
Ltac iauto := try solve [intuition (eauto 3)].
Ltac iauto' := try solve [intuition eauto].
Ltac invert H := inversion H; clear H; try subst.

(* NOTE(dbp 2017-03-26): Often when inverting, we only want to handle
   cases that are _not_ variables. This will fail if C is a variable
   of type T *)
Ltac not_var C T :=
  match goal with
  |[ C' : T |- _ ] =>
   match C with
   | C' => fail 2
   | _ => fail 1
   end
  | _ => idtac
  end.

Tactic Notation "hint" constr(E) :=
  let H := fresh "Hint" in
  let t := type of E in
  assert (H : t) by (exact E).

Tactic Notation "hint" constr(E) "," constr(E1) := hint E; hint E1.
Tactic Notation "hint" constr(E) "," constr(E1) "," constr(E2) :=
  hint E; hint E1; hint E2.
Tactic Notation "hint" constr(E) "," constr(E1) "," constr(E2) "," constr(E3) :=
  hint E; hint E1; hint E2; hint E3.
Tactic Notation "hint" constr(E) "," constr(E1) "," constr(E2) "," constr(E3) "," constr(E4) :=
  hint E; hint E1; hint E2; hint E3; hint E4.
Tactic Notation "hint" constr(E) "," constr(E1) "," constr(E2) "," constr(E3) "," constr(E4) "," constr(E5) :=
  hint E; hint E1; hint E2; hint E3; hint E4; hint E5.

Inductive RR (A : Prop) : Prop :=
| rewrite_rule : forall a : A, RR A.

Definition unRR {A : Prop} (r : RR A) :=
  match r with
  | rewrite_rule _ rr => rr
  end.



Tactic Notation "hint_rewrite" constr(E) := 
  let H := fresh "Hint" in
  let t := type of E in
  assert (H : RR t) by (exact (rewrite_rule t E)).

Tactic Notation "hint_rewrite" constr(E) "," constr(E1) :=
  hint_rewrite E; hint_rewrite E1.
Tactic Notation "hint_rewrite" constr(E) "," constr(E1) "," constr(E2) :=
  hint_rewrite E; hint_rewrite E1; hint_rewrite E2.
Tactic Notation "hint_rewrite" constr(E) "," constr(E1) "," constr(E2) "," constr(E3) :=
  hint_rewrite E; hint_rewrite E1; hint_rewrite E2; hint_rewrite E3.

Ltac swap_rewrite t :=
  match type of t with
  | ?v1 = ?v2 => constr:(eq_sym t) 
  | forall x : ?T, _ =>
    (* let ret :=  *)constr:(fun x : T => let r := t x in 
                                      ltac:(let r' := swap_rewrite r in
                                            exact r')) (* in *)
    (* let ret' := (eval cbv zeta in ret) in *)
    (* constr:(ret) *)
  end.

Tactic Notation "hint_rewrite" "<-" constr(E) := 
  let H := fresh "Hint" in
  let E' := swap_rewrite E in
  let t := type of E' in
  assert (H : RR t) by (exact (rewrite_rule t E')).


Hint Extern 5 => match goal with
                |[H : RR (_ = _) |- _] =>
                 progress (rewrite (unRR H) in *)
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *)
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _ _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *)
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _ _ _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *)
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _ _ _ _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *) 
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _ _ _ _ _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *) 
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _ _ _ _ _ _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *) 
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _ _ _ _ _ _ _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *) 
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _ _ _ _ _ _ _ _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *) 
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _ _ _ _ _ _ _ _ _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *) 
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _ _ _ _ _ _ _ _ _ _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *) 
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _ _ _ _ _ _ _ _ _ _ _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *) 
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _ _ _ _ _ _ _ _ _ _ _ _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *) 
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _ _ _ _ _ _ _ _ _ _ _ _ _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *) 
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *) 
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *) 
                end.

                           
Inductive AutoSimpl : Prop :=
| auto_simpl : AutoSimpl.

Tactic Notation "hint_simpl" := 
  let H := fresh "Hint" in
  assert (H : AutoSimpl) by (exact auto_simpl).

                           
Hint Extern 5 => match goal with
                |[H : AutoSimpl |- _] =>
                 progress (simpl in *) 
                end.

                           

Ltac simplify :=
  repeat (simpl in *; 
          match goal with 
          |[H: True |- _] => clear H
          |[H: ?x <> ?x |- _] => exfalso; apply H; reflexivity
          |[|- ?P /\ ?Q] => try (solve [split; eauto 2] || (split; eauto 2; [idtac])); fail
          |[H: ?P /\ ?Q |- _] => invert H
          |[a: ?x * ?y |- _] => destruct a
end).
