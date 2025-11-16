From Stdlib Require Import FMaps Lia String ZArith.
From AbsInt Require Import Imp.

Local Open Scope Z_scope.
Generalizable Variables A C.

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

  γ_mon  : forall (a b : A), a ≤? b = true -> γ a ⊆ γ b;
  γ_join : forall (a b : A), γ a ∪ γ b ⊆ γ (a ∨ b);
  γ_bot  : forall (c : C), ~ c ∈ γ ⊥;
  γ_top  : forall (c : C), c ∈ γ ⊤;
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
  aunop  : unop -> A -> A;
  abinop : binop -> A -> A -> A;

  γ_aconst : forall (n : Z), n ∈ γ (aconst n);
  γ_aunop  : forall (n : Z) (a : A) (op : unop),
    n ∈ γ a -> eval_unop op n ∈ γ (aunop op a);
  γ_abinop : forall (m n : Z) (a b : A) (op : binop),
    m ∈ γ a -> n ∈ γ b -> eval_binop op m n ∈ γ (abinop op a b);
}.

(** * Абстрактное состояние *)

(** Тип строк является типом с разрешимым равенством. *)

Module StringDec <: DecidableType.
  Definition t := string.
  Definition eq (x y : t) := x = y.

  Definition eq_refl  := @eq_refl t.
  Definition eq_sym   := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition eq_dec   := string_dec.
End StringDec.

(** Конечные отображения на строках определяются с помощью модулей из
    стандартной библиотеки. *)

Module StringMap := FMapWeakList.Make(StringDec).
Module SMFact    := FMapFacts.WFacts(StringMap).
Module SMProp    := FMapFacts.WProperties(StringMap).

Section AbsState.
  Context V `{AbsValue V}.

  (** Абстрактное состояние - это конечное отображение переменных в абстрактные
      значения. Абстрактное состояние должно быть решеткой, в частности иметь ⊥,
      соответвующий пустому множеству конкрекных состояний. Чтобы добавить ⊥
      используем option. *)

  Definition astate := option (StringMap.t V).

  (** Получение абстрактных значений переменных. *)

  Definition getm (x : string) (m : StringMap.t V) : V :=
    match StringMap.find x m with
    | Some v => v
    | None   => ⊤
    end.

  Definition get (x : string) (a : astate) : V :=
    match a with
    | Some m => getm x m
    | None   => ⊥
    end.

  (** Присваивание переменным абстрактных значений. *)

  Definition set (x : string) (v : V) (a : astate) : astate :=
    match a with
    | Some m => Some (StringMap.add x v m)
    | None   => None
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

  Fixpoint iter (n : nat) (a : A) : A :=
    match n with
    | O => ⊤
    | S n' => let a' := f a in
              if a' ≤? a then a else iter n' a'
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
  Context V `{AbsValue V}.

  (** Абстрактная семантика выражений. *)

  Fixpoint aeval (e : exp) (a : astate V) : V :=
    match e with
    | Var x => get x a
    | Const n => aconst n
    | Unop op e => aunop op (aeval e a)
    | Binop op e1 e2 => abinop op (aeval e1 a) (aeval e2 a)
    end.

  (** Абстрактная семантика выражений аппроксимирует конкретную
      семантику выражений. *)

  Lemma aeval_sound : forall (s : state) (a : astate V) (e : exp),
    s ∈ γ a -> eval e s ∈ γ (aeval e a).
  Proof.
  Admitted.

  (** Абстрактная семантика команд. *)

  Fixpoint aceval (c : com) (a : astate V) : astate V :=
    match c with
    | Skip       => a
    | x ::= e    => set x (aeval e a) a
    | c1 ;; c2   => aceval c2 (aceval c1 a)
    | If e c1 c2 => aceval c1 a ∨ aceval c2 a
    | While e c  => postfixpoint (fun X => a ∨ aceval c X)
    end.

  (** ** Задание 2

      Докажите, что абстрактная семантика комманд аппроксимирует конкретную
      семантику команд. *)

  Theorem aceval_sound : forall (c : com) (s s' : state) (a : astate V),
    s ∈ γ a -> ceval c s s' -> s' ∈ γ (aceval c a).
  Proof.
  Admitted.
End Analysis.

(** * Распространение констант (constant propagation) *)

(** ** Задание 3

    Определите абстрактный домен для распространения констант. *)

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

Definition prog1 : com :=
  "x" ::= Const 1 ;; "y" ::= Const 10 ;;
  "z" ::= Binop Oplus (Var "x") (Var "y") ;;
  If (Binop Olt (Const 0) (Var "x") )
    ("y" ::= Binop Oplus (Var "x") (Var "z") ;; "x" ::= Const 0)
    ("y" ::= Const 12).

Compute
  let a := aceval flatZ prog1 ⊤ in
  (get "x" a, get "y" a, get "z" a).

(** Результат анализа:
<<
  = (Top, Just 12, Just 11)
>>
  [x] неизвестно, [y] = 12, and [z] = 11.
*)


(** * Интервалы *)

(** ** Задание 4

    Определите абстрактный домен интервалов. *)

(** Будем хранить интервал [a, b] в виде пары (-a, b). Это позволяет избежать
    расмотрения отдельно значений +∞ и -∞, оставив только +∞. *)

Inductive ZInf := Fin (n : Z) | Inf.
Coercion Fin : Z >-> ZInf.

Record Interval := {
  low  : ZInf;
  high : ZInf;
}.

Instance IntervalLatticeOp : LatticeOp Interval.
Admitted.

Instance IntervalConcretization : Concretization Interval Z.
Admitted.

Instance IntervalAbsValue : AbsValue Interval.
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

Compute
  let a := aceval Interval prog1 ⊤ in
  (get "x" a, get "y" a, get "z" a).

(** Результат анализа:
<<
  = ({| low := 0; high := 1 |}, {| low := -12; high := 12 |}, {| low := -11; high := 11 |})
>>
  [x] ∈ [0, 1], [y] ∈ [12, 12], and [z] ∈ [11, 11].
*)

(** * Анализ условий *)

(** Программа:
<<
    x := 0;
    while x < 10 do
      x := x + 1
>> *)

Definition prog2 : com :=
  "x" ::= Const 0 ;;
  While (Binop Olt (Var "x") (Const 10))
    ("x" ::= Binop Oplus (Var "x") (Const 1)).

Compute
  let a := aceval Interval prog2 ⊤ in
  get "x" a.

(** Результат анализа:
<<
  = {| low := Inf; high := Inf |}
>>
  [x] ∈ [-∞, +∞]
*)

(** Но при выходе из цикла должно выполняться условие [x] ∈ [10, +∞]. Наш анализ
    не может это обнаружить, потому что в опредлении функции [aceval] мы
    игнорируем значения логических выражений в if и while. *)

(** ** Задание 5

    Реализуйте анализ условий и докажите его корректность (создайте файл
    AbsIntCond.v, скопировав файл AbsInt.v, внесите необходимые изменения) *)
