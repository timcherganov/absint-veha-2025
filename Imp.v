From Stdlib Require Import ZArith String.

Local Open Scope Z_scope.

(** * Состояние *)

Definition state : Type := string -> Z.

Definition update {Y : Type} (k : string) (y : Y) (f : string -> Y) : string -> Y :=
  fun x => if string_dec k x then y else f x.

(** * Синтаксис *)

Inductive binop : Type := Oplus | Oeq | Olt | Oand.

Inductive unop : Type := Oopp | Oneg.

Inductive exp : Type :=
| Var (x : string)
| Const (n : Z)
| Unop (op : unop) (e : exp)
| Binop (op : binop) (e1 e2 : exp).

Inductive com : Type :=
| Skip
| Assign (x : string) (e : exp)
| Seq (c1 c2 : com)
| If (e : exp) (c1 c2 : com)
| While (e : exp) (c : com).

Infix "::=" := Assign (at level 75).
Infix ";;" := Seq (at level 80, right associativity).

(** * Семантика выражений *)

Definition andz (n m : Z) : Z :=
  match n, m with
  | Z0 , _  => 0
  | _  , Z0 => 0
  | _  , _  => 1
  end.

Definition negz (n : Z) : Z :=
  match n with
  | Z0 => 1
  | _  => 0
  end.

Definition eval_binop (op : binop) : Z -> Z -> Z :=
  match op with
  | Oplus  => Z.add
  | Oeq    => fun m n => Z.b2z (m =? n)
  | Olt    => fun m n => Z.b2z (m <? n)
  | Oand   => andz
  end.

Definition eval_unop (op : unop) : Z -> Z :=
  match op with
  | Oopp => Z.opp
  | Oneg => negz
  end.

Fixpoint eval (e : exp) (s : state) : Z :=
  match e with
  | Var x          => s x
  | Const n        => n
  | Unop op e      => eval_unop op (eval e s)
  | Binop op e1 e2 => eval_binop op (eval e1 s) (eval e2 s)
  end.

(** * Семантика команд *)

Inductive ceval : com -> state -> state -> Prop :=
| ESkip       : forall s,
                ceval Skip s s

| EAssign     : forall s x e,
                ceval (x ::= e) s (update x (eval e s) s)

| ESeq        : forall s1 s2 s3 c1 c2,
                ceval c1 s1 s2 -> ceval c2 s2 s3 ->
                ceval (c1 ;; c2) s1 s3

| EIf         : forall s1 s2 c1 c2 e,
                ceval (if (Z.eq_dec (eval e s1) 0) then c2 else c1) s1 s2 ->
                ceval (If e c1 c2) s1 s2

| EWhileTrue  : forall s1 s2 s3 c e,
                eval e s1 <> 0 ->
                ceval c s1 s2 -> ceval (While e c) s2 s3 ->
                ceval (While e c) s1 s3

| EWhileFalse : forall s c e,
                eval e s = 0 ->
                ceval (While e c) s s.

Hint Constructors ceval : core.
