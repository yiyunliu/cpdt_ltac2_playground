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
  Local Hint Extern 1 => ltac2: (match! goal with
                                | [|- _ = ?x + 0] => rewrite <- (plus_n_O $x)
                               end) : db.

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


Module Type GROUP.
  Parameter G : Set.
  Parameter f : G -> G -> G.
  Parameter id : G.
  Parameter i : G -> G.

  Axiom assoc : forall a b c, f (f a b) c = f a (f b c).
  Axiom ident : forall a, f id a = a.
  Axiom inverse : forall a, f (i a) a = id.
End GROUP.

Module Type GROUP_THEOREMS.
  Declare Module M : GROUP.
  Axiom ident' : forall a, M.f a M.id = a.
  Axiom inverse' : forall a, M.f a (M.i a) = M.id.
  Axiom unique_ident : forall id', (forall a, M.f id' a = a) -> id' = M.id.
End GROUP_THEOREMS.

Module Type GROUP_THEOREMS_F (M : GROUP).
  Axiom ident' : forall a, M.f a M.id = a.
  Axiom inverse' : forall a, M.f a (M.i a) = M.id.
  Axiom unique_ident : forall id', (forall a, M.f id' a = a) -> id' = M.id.
End GROUP_THEOREMS_F.

Module Type GROUP_THEOREMS'.
  Declare Module M : GROUP.

  Set Default Proof Mode "Ltac2".
  Theorem inverse' : forall a, M.f a (M.i a) = M.id.
  Proof.
    Import M.
    intros.
    rewrite <- (ident (f a (i a))).
    rewrite <- (inverse (f a (i a))) at 1.
    do 2 (rewrite assoc).
    rewrite <- (assoc (i a) a (i a)).
    rewrite inverse.
    rewrite ident.
    apply inverse.
  Qed.

  Theorem ident' : forall a, M.f a M.id = a.
  Proof.
    intros a.
    rewrite <- (inverse a).
    rewrite <- assoc.
    rewrite inverse'.
    apply ident.
  Qed.

  Theorem unique_ident : forall id', (forall a, M.f id' a = a) -> id' = M.id.
  Proof.
    intros.
    rewrite <- (H id).
    symmetry.
    apply ident'.
  Qed.

End GROUP_THEOREMS'.

Inductive taut : Set :=
| TautTrue : taut
| TautAnd : taut -> taut -> taut
| TautOr : taut -> taut -> taut
| TautImp : taut -> taut -> taut.

Fixpoint tautDenote (t : taut) : Prop :=
  match t with
  | TautTrue => True
  | TautAnd t1 t2 => tautDenote t1 /\ tautDenote t2
  | TautOr t1 t2 => tautDenote t1 \/ tautDenote t2
  | TautImp t1 t2 => tautDenote t1 -> tautDenote t2
  end.


Set Default Proof Mode "Ltac2".
Theorem tautTrue : forall t : taut, tautDenote t.
  induction t; ltac1:(fcrush).
Qed.

Ltac2 rec tautReify (p : constr) : constr :=
  lazy_match! p with
  | True => 'TautTrue
  | ?p1 /\ ?p2 =>
      let t1 := tautReify p1 in
      let t2 := tautReify p2 in
      '(TautAnd $t1 $t2)
  | ?p1 \/ ?p2 =>
      let t1 := tautReify p1 in
      let t2 := tautReify p2 in
      '(TautOr $t1 $t2)
  | ?p1 -> ?p2 =>
      let t1 := tautReify p1 in
      let t2 := tautReify p2 in
      '(TautImp $t1 $t2)
  end.

Print Ltac2 tautReify.

Ltac2 solve_taut () :=
  lazy_match! goal with
  | [|- ?p] =>
      let t := tautReify p in
      let proof := '(tautTrue $t) in
      exact $proof
  end.

Ltac2 Notation "solve_taut" := solve_taut ().

Theorem true_galore :  (True /\ True) -> (True \/ (True /\ (True -> True))).
Proof.
  solve_taut.
Qed.


Print true_galore.

Module Type monoid.
  Parameter A : Set.
  Parameter e : A.
  Parameter f : A -> A -> A.

  Inductive mexp : Set :=
  | Ident : mexp
  | Var : A -> mexp
  | Op : mexp -> mexp -> mexp.

  Infix "+" := f.

  Ltac2 rec mexpReify (m : constr) : constr :=
    lazy_match! m with
    | e => 'Ident
    | ?a + ?b => let a := mexpReify a in
                let b := mexpReify b in
                '(Op $a $b)
    | ?e => '(Var $e)
    end.

  Axiom assoc : forall a b c, (a + b) + c = a + (b + c).
  Axiom identl : forall a, e + a = a.
  Axiom identr : forall a, a + e = a.

  (* The ltac function and mdenote really should be an isomorphism *)
  Fixpoint mdenote (me : mexp) : A :=
    match me with
    | Ident => e
    | Var v => v
    | Op me1 me2 => mdenote me1 + mdenote me2
    end.

  Fixpoint flatten (me : mexp) : list A :=
    match me with
    | Ident => nil
    | Var x => x :: nil
    | Op me1 me2 => flatten me1 ++ flatten me2
    end.

  Fixpoint mldenote (ms : list A) : A :=
    match ms with
    | [] => e
    | m::ms => m + mldenote ms
    end.

  Lemma flatten_correct': forall ml1 ml2,
      mldenote ml1 + mldenote ml2 = mldenote (ml1 ++ ml2).
  Proof.
    Local Hint Rewrite <- assoc : flatten_db.
    Local Hint Rewrite -> identl : flatten_db.
    Local Hint Rewrite -> identr : flatten_db.
    induction ml1;
      ltac1:(fcrush db: flatten_db).
  Qed.

  Lemma flatten_correct :  forall me, mdenote me = mldenote (flatten me).
  Proof.
    induction me; ltac1:(fcrush use:flatten_correct' rew:db:flatten_db).
  Qed.

  Theorem monoid_reflect : forall me1 me2,
      mldenote (flatten me1) = mldenote (flatten me2)
      -> mdenote me1 = mdenote me2.
  Proof.
    ltac1:(sfirstorder use:flatten_correct).
  Qed.

  Ltac2 solve_monoid () : unit :=
    lazy_match! goal with
    | [ |- ?m1 = ?m2 ] =>
        let me1 := mexpReify m1 in
        let me2 := mexpReify m2 in
        apply monoid_reflect with (me1 := $me1) (me2 := $me2);
        reflexivity
    end.

  Theorem monoid3 : forall x : A, x + (e + x) + x = x + e + (x + x) + e.
  Proof.
    intros.
    solve_monoid ().
  Qed.

End monoid.

Class Lattice (A : Set) := {
    meet : A -> A -> A;
    join : A -> A -> A;
    meet_commutative : forall a b, meet a b = meet b a;
    meet_associative : forall a b c, meet (meet a b) c = meet a (meet b c);
    meet_absorptive : forall a b, meet a (join a b) = a;
    meet_idempotent : forall a, meet a a = a;
    join_commutative : forall a b, join a b = join b a;
    join_associative: forall a b c, join (join a b) c = join a (join b c);
    join_absorptive : forall a b, join a (meet a b) = a;
    join_idempotent : forall a, join a a = a;
}.

Definition leq_lat {A : Set} {_:Lattice A} (a : A) (b : A) :=
  meet a b = a.

Inductive LH :=
| L : LH
| H : LH.

Set Default Proof Mode "Classic".
#[refine, export] Instance LH_Lattice : Lattice LH := {
    meet := fun x y =>
              match x with
              | L => L
              | _ => y
              end ;
    join := fun x y =>
              match x with
              | H => H
              | _ => y
              end;
  }.
Proof.
  all:try solve [qauto inv:LH].
Qed.

Inductive lexp (A : Set) : Set :=
| Var : A -> lexp A
| Meet : lexp A -> lexp A -> lexp A
| Join : lexp A -> lexp A -> lexp A.
Arguments Var {A}.
Arguments Meet {A}.
Arguments Join {A}.

Fixpoint denoteLexp {A : Set} {_:Lattice A} (e : lexp A) :=
  match e with
  | Var a => a
  | Meet e1 e2 => meet (denoteLexp e1) (denoteLexp e2)
  | Join e1 e2 => join (denoteLexp e1) (denoteLexp e2)
  end.

Fixpoint lexp_size {A : Set} (e : lexp A) :=
  match e with
  | Var _ => 0
  | Meet e1 e2 => 1 + lexp_size e1 + lexp_size e2
  | Join e1 e2 => 1 + lexp_size e1 + lexp_size e2
  end.

From Equations Require Import Equations.

Derive NoConfusion for lexp.
Derive Subterm for lexp.

#[tactic="sfirstorder"] Equations splitLeq {A : Set} `{Lattice A} (e1 : lexp A) (e2 : lexp A) : Prop
  by wf (lexp_size e1 + lexp_size e2) lt :=
  splitLeq (Var a1) (Var a2) => leq_lat a1 a2;
  splitLeq (Join e11 e12) e2 => splitLeq e11 e2 /\ splitLeq e12 e2;
  splitLeq e1 (Meet e21 e22) => splitLeq e1 e21 /\ splitLeq e1 e22;
  splitLeq (Var a) (Join e21 e22) => splitLeq (Var a) e21 \/ splitLeq (Var a) e22;
  splitLeq (Meet e11 e12) (Var a) => splitLeq e11 (Var a) \/ splitLeq e12 (Var a);
  splitLeq (Meet e11 e12) (Join e21 e22) => splitLeq e11 (Join e21 e22) \/ splitLeq e12 (Join e21 e22) \/ splitLeq (Meet e11 e12) e21 \/ splitLeq (Meet e11 e12) e22.

Require Import ssreflect.

Hint Resolve
  meet_commutative
  meet_associative
  meet_absorptive
  meet_idempotent
  join_commutative
  join_associative
  join_absorptive
  join_idempotent : lat_db.
Hint Unfold leq_lat : lat_db.

Definition leq_lat' {A : Set} {_:Lattice A} (e1 e2 : A) := join e1 e2 = e2.


Lemma leq_lat_leq_lat'_iff {A : Set} {_:Lattice A} :
  forall e1 e2, leq_lat e1 e2 <-> leq_lat' e1 e2.
Proof.
  move => e1 e2.
  split.
  - rewrite /leq_lat /leq_lat' => H.
    by rewrite -H join_commutative meet_commutative join_absorptive.
  - rewrite /leq_lat /leq_lat' => H.
    by rewrite -H meet_absorptive.
Qed.

Lemma leq_lat_refl {A : Set} {_:Lattice A} (e : A) : leq_lat e e.
Proof.
  qauto db:lat_db.
Qed.

Lemma leq_lat_trans {A : Set} {_:Lattice A} (e1 e2 e3 : A) : leq_lat e1 e2 -> leq_lat e2 e3 -> leq_lat e1 e3.
Proof.
  unfold leq_lat.
  intros.
  rewrite <- H1.
  rewrite meet_associative.
  rewrite H2.
  reflexivity.
Qed.

Lemma leq_lat_antisym {A : Set} {_:Lattice A} (e1 e2 : A) :
  leq_lat e1 e2 -> leq_lat e2 e1 -> e1 = e2.
Proof.
  intros.
  unfold leq_lat in *.
  rewrite meet_commutative in H1.
  congruence.
Qed.

Lemma leq_meet_iff {A : Set} {_:Lattice A} (e1 e2 e3 : A) :
  leq_lat e1 (meet e2 e3) <-> leq_lat e1 e2 /\ leq_lat e1 e3.
Proof.
  split.
  - unfold leq_lat.
    intros.
    split.
    + by rewrite -H1
       {1}meet_associative
       {1}meet_associative
       [meet e3 _]meet_commutative
       -[meet e2 _]meet_associative
       meet_idempotent.
    + by rewrite -H1
       {1}meet_associative
       {1}meet_associative
       meet_idempotent.
  - move => [H1 H2];
      rewrite /leq_lat -meet_associative H1 H2 //.
Qed.

Lemma leq_join_iff {A : Set} {_:Lattice A} (e2 e3 e1 : A) :
  leq_lat (join e2 e3) e1 <-> leq_lat e2 e1 /\ leq_lat e3 e1.
Proof.
  repeat rewrite leq_lat_leq_lat'_iff /leq_lat'.
  split.
  - move => H1.
    split.
    + rewrite -H1
       {1}join_associative
       {1}join_associative
       [join e3 _]join_commutative
       -[join e2 _]join_associative
          join_idempotent
      //.
    + rewrite -H1
       -join_associative
       [join e3 _]join_commutative
       [join _ e3]join_associative
       join_idempotent
      //.
  - move => [H1 H2].
    rewrite join_associative H2 H1 //.
Qed.

(* The other direction is not true.... *)
Lemma leq_join_prime {A : Set} {_:Lattice A} (e1 e2 e3 : A) :
  leq_lat e1 e2 \/ leq_lat e1 e3 -> leq_lat e1 (join e2 e3).
Proof.
  rewrite !leq_lat_leq_lat'_iff !/leq_lat'.
  sauto lq: on use: join_associative.
Qed.

Lemma leq_meet_prime {A : Set} {_:Lattice A} (e1 e2 e3 : A) :
  leq_lat e1 e3 \/ leq_lat e2 e3 -> leq_lat (meet e1 e2) e3.
Proof.
  hfcrush l: on q: on use: meet_associative, meet_commutative.
Qed.


(*  *)
(* Create HintDb leq_meet_join_props. *)
(* #[export]Hint Resolve *)
(*   leq_meet_iff *)
(*   leq_join_iff *)
(*   leq_meet_prime *)
(*   leq_join_prime: leq_meet_join_props. *)


(* Transforming goal *)
Theorem splitLeq_sound {A : Set} {H:Lattice A} (e1 e2 : lexp A) :
  splitLeq e1 e2 -> leq_lat (denoteLexp e1) (denoteLexp e2).
Proof.
  intros.
  Check splitLeq_graph_correct.
  have h0 := splitLeq_graph_correct _ H e1 e2.
  remember (splitLeq e1 e2) as p.
  induction h0 using splitLeq_graph_rect.
  - trivial.
  - hauto l:on rew: off use:leq_meet_iff.
  - hauto lq: on rew: off use: leq_join_prime.
  - hauto lq: on rew: off use: leq_meet_prime.
  - hauto l: on use: leq_meet_iff.
  - hauto lq: on rew: off use: leq_join_prime, leq_meet_prime.
  - hauto l:on rew: off use:leq_join_iff.
Qed.
