From Stdlib Require Import FMaps Lia String ZArith.
From AbsInt Require Import Imp.

Local Open Scope Z_scope.
Generalizable Variables A B.

(** * Интерфейс для абстрактных доменов *)

(** Операции на решетке. *)

Class LatticeOp A := {
  ble : A -> A -> bool;
  join : A -> A -> A;
  bot : A;
  top : A;
}.

(** Нотация для операций решетки. *)

Infix "∨" := join (at level 50, no associativity).
Infix "≤?" := ble (at level 70, no associativity).
Notation "⊥" := bot.
Notation "⊤" := top.

(** Нотация для работы с подмножествами. *)

Notation "'𝒫' A" := (A -> Prop) (at level 0).
Notation "x ∈ X" := (X x) (at level 19, only parsing).
Notation "X ⊆ Y" := (forall a, X a -> Y a) (at level 20).
Notation "X ∪ Y" := (fun x => X x \/ Y x) (at level 19).

(** Отображение конкретизации - монотонное отображение из абстрактного
    домена в подмножества элементов конкретного домена. *)

Class Concretization A `{Alat : LatticeOp A} C := {
  γ : A -> 𝒫 C;
  γ_mon : forall a b, a ≤? b = true -> γ a ⊆ γ b;
  γ_join : forall a b, γ a ∪ γ b ⊆ γ (a ∨ b);
  γ_bot : forall n, ~ n ∈ γ ⊥;
  γ_top : forall n, n ∈ γ ⊤;
}.

(** Абстрактные значения должны обладать:
    - структурой решетки;
    - отображением конкретизации, связывающим абстрактные значения с
      конкретными;
    - абстрактными операциями и константами, соответсвующими
      конкретным операциям и константам языка программирования. *)

Class AbsValue A := {
  lat_val :: LatticeOp A;
  γ_val :: Concretization A Z;

  aconst : Z -> A;
  aunop : unop -> A -> A;
  abinop : binop -> A -> A -> A;

  γ_aconst : forall n, n ∈ γ (aconst n);
  γ_aunop : forall n N op, n ∈ γ N -> eval_unop op n ∈ γ (aunop op N);
  γ_abinop : forall n1 n2 N1 N2 op,
    n1 ∈ γ N1 -> n2 ∈ γ N2 -> eval_binop op n1 n2 ∈ γ (abinop op N1 N2);
}.

(** * Абстрактное состояние *)

(** Тип строк является типом с разрешимым равенством. *)

Module StringDec <: DecidableType.
  Definition t := string.
  Definition eq (x y : t) := x = y.

  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition eq_dec := string_dec.
End StringDec.

(** Конечные отображения на строках определяются с помощью модулей из
    стандартной библиотеки. *)

Module StringMap := FMapWeakList.Make(StringDec).
Module SMFact := FMapFacts.WFacts(StringMap).
Module SMProp := FMapFacts.WProperties(StringMap).

Section AbsState.
  Context A `{AbsValue A}.

  (** Абстрактное состояние - это конечное отображение переменных в абстрактные
      значения. Абстрактное состояние должно быть решеткой, в частности иметь ⊥,
      соответвующий пустому множеству конкрекных состояний. Чтобы добавить ⊥
      используем option. *)

  Definition astate := option (StringMap.t A).

  (** Получение абстрактных значений переменных. *)

  Definition getm (x : string) (m : StringMap.t A) : A :=
    match StringMap.find x m with
    | Some N => N
    | None => ⊤
    end.

  Definition get (x : string) (S : astate)  : A :=
    match S with
    | Some m => getm x m
    | None => ⊥
    end.

  (** Присваивание переменным абстрактных значений. *)

  Definition set (x : string) (a : A) (s : astate) : astate :=
    match s with
    | Some m => Some (StringMap.add x a m)
    | None => None
    end.

  (** ** Задание 1

      Определите операции решетки на абстрактных состояних с помощью операций
      решетки на абстрактных значениях. *)

  #[global]
  Instance astateLatticeOp : LatticeOp astate.
  Admitted.

  (** Покажите, что на абстактном состоянии определено отображение
      конкретизации, индуцированное отображением конкретизации на абстрактных
      значениях. *)

  #[global]
  Instance astateConcretization : Concretization astate state.
  Admitted.
End AbsState.

Arguments get {_ _}.
Arguments set {_}.

(** * Неподвижная точка *)

Section fixpoint.
  Context {A C} `{Concretization A C} (f : A -> A).

  Fixpoint iter (n : nat) (S : A) : A :=
    match n with
    | O => ⊤
    | S n' => let S' := f S in
             if ble S' S then S else iter n' S'
    end.

  Definition niter := 10%nat.

  Definition postfixpoint : A := iter niter ⊥.

  (** Неподвижная точка определена корректно. *)

  Lemma postfixpoint_sound :
    γ (f postfixpoint) ⊆ γ postfixpoint.
  Proof.
  Admitted.
End fixpoint.

(** * Корректность абстрактной интерпретации *)

Section Analysis.
  Context A `{AbsValue A}.

  (** Абстрактная семантика выражений. *)

  Fixpoint aeval (e : exp) (S : astate A) : A :=
    match e with
    | Var x => get x S
    | Const n => aconst n
    | Unop op e => aunop op (aeval e S)
    | Binop op e1 e2 => abinop op (aeval e1 S) (aeval e2 S)
    end.

  (** Абстрактная семантика выражений аппроксимирует конкретную
      семантику выражений. *)

  Lemma aeval_sound : forall s S e,
    s ∈ γ S -> eval e s ∈ γ (aeval e S).
  Proof.
  Admitted.

  (** Абстрактная семантика команд. *)

  Fixpoint aceval (c : com) (S : astate A) : astate A :=
    match c with
    | Skip       => S
    | x ::= e    => set x (aeval e S) S
    | c1 ;; c2   => aceval c2 (aceval c1 S)
    | If e c1 c2 => aceval c1 S ∨ aceval c2 S
    | While e c  => postfixpoint (fun X => S ∨ aceval c X)
    end.

  (** ** Задание 2

      Докажите, что абстрактная семантика комманд аппроксимирует конкретную
      семантику команд. *)

  Theorem aceval_sound : forall c s s' S,
    s ∈ γ S -> ceval c s s' -> s' ∈ γ (aceval c S).
  Proof.
  Admitted.
End Analysis.

(** * Распространение констант (constant propagation) *)

(** Определите абстрактный домен для распространения констант. *)

Inductive flatZ : Type := Bot | Just (n : Z) | Top.

Instance flatZLatticeOp : LatticeOp flatZ.
Admitted.

Instance flatZConcretization : Concretization flatZ Z.
Admitted.

Instance flatZAbsValue : AbsValue flatZ.
Admitted.

(** Программа:
<<
    x := 1; y := 10; z := x + y;
    if x > 0 then
      y := x + z; x := 0
    else
      y := 12
>>
*)

Definition prog : com :=
  "x" ::= Const 1 ;; "y" ::= Const 10 ;;
  "z" ::= Binop Oplus (Var "x") (Var "y") ;;
  If (Binop Olt (Const 0) (Var "x") )
    ("y" ::= Binop Oplus (Var "x") (Var "z") ;; "x" ::= Const 0)
    ("y" ::= Const 12).

Compute
  let S := aceval flatZ prog ⊤ in
  (get "x" S, get "y" S, get "z" S).

(** Результат анализа:
<<
  = (Top, Just 12, Just 11)
>>
[x] неизвестно, [y] = 11, and [z] = 12.
*)
