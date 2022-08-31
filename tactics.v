Require Import Coq.Lists.List.
Import ListNotations.

Ltac find_if :=
  match goal with
  | [|- if ?e then _ else _] => destruct e
  end.

Theorem hmm : forall (a b c : bool),
    if a
    then if b
         then True
         else True
    else if c
         then True
         else True.
Proof.
  intros.
  (* every successful call to repeat_if will automatically cause a *)
(*   simplification *)
  repeat find_if; constructor.
Qed.

Ltac test_fail :=
  match goal with
  (* fail is a synonym for fail 0? *)
  (* if we use fail 0, match will simply go to the next branch *)
  (* if we changed it to fail 1, then the entire match goal ... would fail *)
  | _ => fail 0
  | _ => intros
  end.

Parameter P Q : Prop.

Theorem id_prop : P -> P.
Proof.
  test_fail.
  assumption.
Qed.

Theorem test : P -> (P -> Q) -> Q.
Proof.
  test_fail.
  generalize (H0 H).
  trivial.
Qed.
(* locally bound variables and unification variables *)
(* https://stackoverflow.com/questions/61795038/ltac-unification-variable-containing-locally-bound-variables *)


From Ltac2 Require Import Ltac2.

Ltac2 idtac () := ().

Ltac2 hello_world () := Message.print (Message.of_string "Debugging info").

Goal True.
  hello_world ().
Abort.

Ltac2 Eval hello_world ().


Ltac2 Eval Message.print (Message.of_constr '(3 + 4)).

Ltac2 bar () := let x := '(3 + 4) in constr:($x + 5).

Ltac2 bar' () := let x := '(3 + 4) in '($x + 5).

Ltac2 Eval bar().

Ltac2 Eval bar'().

Section with_x.
  Context (x:nat).
  Ltac2 foo () := '(3 + &x).
  Ltac2 Eval foo ().
  (* whatever goes in ltac2: must be an effect *)
  (* which is why this does not work *)

  Ltac2 Eval Fresh.in_goal @x.
  Ltac2 Eval Fresh.in_goal @y.


  Goal True.
    (* how to use fresh/gensym in ltac2 *)
  let h := Fresh.in_goal @H in
  pose ($h := 4).

    (* pose ltac2:(foo'' ()). *)
    (* Error: Cannot infer an existential variable of type "?T" in environment: *)
    (* If you get the above message, just ignore it. It makes no sense *)

Abort.

End with_x.

Ltac2 Eval let x := '0 in constr:(1 + ltac2:(exact $x)).

Ltac2 foo' () := let x := '4 in '(3 + $x).
Ltac2 Eval foo' ().
Ltac2 foo'' () := '(let x := 4 in 3 + x).
Ltac2 Eval foo'' ().
Goal True.
  let n := foo'' () in
  pose $n.
Abort.

(* https://stackoverflow.com/questions/67367231/what-does-control-refine-do-in-ltac2 *)

(* use the result of foo' *)
Goal nat.
  let x := foo'' () in
  pose (x := $x); exact x.

  Undo.
  (* alternatively: this is the recommended approach *)
  let x := foo'' () in
  exact $x.

  Undo.
  exact ltac2:(Control.refine (fun _ => foo'' ())).
Qed.


Ltac2 rec map t f ls :=
  match! ls with
  | nil => '(@nil $t)
  | ?x :: ?ls => let ls := map t f ls in
                let x := f x in
                '($x :: $ls)
  end.

Print Ltac2 map.

Ltac2 Eval map 'nat (fun x => '($x + $x)) '[1;2;3;4].

Definition global_x : nat := 4.

(* unquoted variable in '(...) always refer to gallina variables (global or local) *)
Ltac2 Eval '(global_x + 4).

(* not allowed: top-level definitions cannot be bound to a quoted gallina term *)
(* Ltac2 global_x := '5. *)

Ltac2 Eval let x := '4 in '($x + 4).

(* ltac2 and gallina functions live in different namespaces *)
Ltac2 global_x := 4.

Ltac2 global_x' () := '4.

(* why can't you do this? *)
(* Ltac2 global_x'' := '4. *)


Ltac2 tuple_plus_one xy :=
  match! xy with
  | (?x, ?y) => '($x + 1, $y + 1)
  end.

(* so you can match Gallina tuples, but then what does the *)
(* documentation mean when it says you can't match on tuples? Ltac2 *)
(* doesn't really have a tuple data type of its own so I don't know what *)
(* else it refers to *)

Ltac2 Eval tuple_plus_one '(1,2).

Ltac2 Notation x(self) "++" y(self) := Message.concat x y.


From Coq Require Import Lia.








Local Ltac2 lia_ltac1 () := ltac1:(lia).

Ltac2 Notation "lia" := lia_ltac1 ().


From Hammer Require Import Tactics.

Local Ltac2 best_ltac1 () := ltac1:(best).

Ltac2 Notation "best" := best_ltac1 ().

Theorem false : forall x, x + 0 = x.
Proof.
  best.
Qed.



Ltac length ls :=
  match ls with
  | nil => O
  | cons _ ?ls => let l := length ls in
              constr:(S l)
  end.

(* Goal False. *)
(*   let n := length (cons 1 (cons 2 (cons 3 nil))) in *)
(*   pose n. *)

Require Import Coq.Lists.List.

Ltac map T f :=
  (* f is an ltac function from gallina terms to gallina terms *)
  (* ls is a gallina term *)
  let rec map' ls :=
    match ls with
    (* can't ignore T because constr: immediatley forces nil to be typed *)
    | nil => constr:(@nil T)
    | ?x :: ?xs =>
        let xs' := map' xs in
        let x' := f x in
        constr: (x' :: xs')
    end
  in map'.

(* Goal False. *)
(*   let n := map nat ltac:(fun x => constr:(S x)) (cons 1 (cons 2 (cons 3 nil))) in *)
(*   pose n. *)
(* Abort. *)



Theorem simple_eq : forall x, x = x + 0 + 0.
Proof.
  intros x.
  repeat (rewrite <- plus_n_O).
  reflexivity.
Qed.


Theorem simple_eq' : forall x, x = x + 0 + 0.
Proof.
  intros x.


  (* This approach should be quite straightforward *)
  (* Local Hint Extern 1 => ltac2: (match! goal with *)
  (*                               | [|- _ = ?x + 0] => rewrite <- (plus_n_O $x) *)
  (*                              end) : db. *)

  (* x is a ltac1 symbol. We need to use (... |- ...) construct to allow ltac2 access to the x *)
  Local Hint Extern 1 (_ = ?x + 0)
        => let f := ltac2:(x |- let x := Option.get (Ltac1.to_constr x) in
                              rewrite <- (plus_n_O $x))
          in f x : db.

  auto with db.
Qed.


Ltac2 Type sauto_opts :=
  { inv : bool
  ; lq : bool }.

Ltac2 sauto_defopts : sauto_opts := {inv := true; lq := true}.

Ltac2 Eval Int.equal (Int.add 1 2) 3.

(* Print simple_eq. *)

(* Ltac2 length ls := *)


Set Default Proof Mode "Classic".
Theorem swap {A B : Prop} : A * B -> B * A.
Proof.
  tauto.
Qed.
