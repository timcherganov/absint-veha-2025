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
  γ_aunop  : forall (n : Z) (a : A) (op : unop), n ∈ γ a -> eval_unop op n ∈ γ (aunop op a);
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
  Instance astateLatticeOp : LatticeOp astate := {
    ble a b :=
      match a, b with
      | None, _      => true
      | _   , None   => false
      | _   , Some n => 
        SMProp.for_all (fun x v => (get x a) ≤? v) n
      end;
    join a b :=
      let join_aux u v :=
        match u, v with
        | Some u, Some v => Some (u ∨ v)
        | _     , _      => None
        end in
      match a, b with
      | None  , _    => b
      | _     , None => a
      | Some m, Some n => Some (StringMap.map2 join_aux m n)
      end;
    bot := None;
    top := Some (StringMap.empty V);
  }.

  (** Покажите, что на абстактном состоянии определено отображение
      конкретизации, индуцированное отображением конкретизации на абстрактных
      значениях. *)

  #[global, refine]
  Instance astateConcretization : Concretization astate state := {
    γ a := fun s => forall x : string, s x ∈ γ (get x a);
  }.
  Proof.
  - intros [m|] [n|] Hmn s Hs x.
    + specialize Hs with x.
      unfold get, getm in *.
      destruct (StringMap.find x n) as [v|] eqn:Hv.
      2: apply γ_top.
      apply StringMap.find_2 in Hv.
      simpl in Hmn.
      rewrite SMProp.for_all_iff in Hmn.
      eauto using γ_mon.
      solve_proper.   
    + easy.
    + specialize Hs with x.
      now apply γ_bot in Hs.
    + easy.
  - intros [m|] [n|] s [Hm | Hn] x.
    + simpl; unfold getm.
      rewrite SMFact.map2_1bis by easy.
      specialize Hm with x; unfold get, getm in Hm.
      destruct (StringMap.find x m) as [u|].
      2: apply γ_top.
      destruct (StringMap.find x n) as [v|].
      * eauto using γ_join.
      * apply γ_top.
    + simpl; unfold getm.
      rewrite SMFact.map2_1bis by easy.
      specialize Hn with x; unfold get, getm in Hn.
      destruct (StringMap.find x m) as [u|].
      2: apply γ_top.
      destruct (StringMap.find x n) as [v|].
      * eauto using γ_join.
      * apply γ_top.
    + easy.
    + specialize Hn with x.
      now apply γ_bot in Hn.
    + specialize Hm with x.
      now apply γ_bot in Hm.
    + easy.
    + easy.
    + easy.
  - intros s Hs.
    specialize Hs with ""%string.
    now apply γ_bot in Hs.
  - intros s x; simpl.
    unfold getm; simpl.
    apply γ_top.
  Defined.
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
    unfold postfixpoint.
    generalize niter as n, ⊥.
    induction n; intros; simpl in *.
    - apply γ_top.
    - destruct (_ ≤? _) eqn:?; eauto using γ_mon.
  Qed.
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
    induction e; eauto using γ_aconst, γ_aunop, γ_abinop.
  Qed.

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
    induction c; intros s s' a Hsa Hss'.
    - inversion Hss'; subst; eauto.
    - inversion Hss'; subst; simpl.
      intros y.
      destruct a as [m|]; simpl in *.
      + unfold getm.
        rewrite SMFact.add_o.
        unfold update, StringMap.E.eq_dec.
        destruct (string_dec x y); eauto using aeval_sound.
      + specialize Hsa with ""%string.
        now apply γ_bot in Hsa.
    - inversion Hss'; subst; eauto.
    - inversion Hss'; subst.
      apply γ_join.
      destruct (Z.eq_dec (eval e s) 0); eauto.
    - set (f := fun X => a ∨ aceval c X).
      set (π := postfixpoint f).
      assert (Hπ : γ (f π) ⊆ γ π) by (apply postfixpoint_sound).
      assert (forall c' s1 s2,
              ceval c' s1 s2 -> c' = While e c -> s1 ∈ γ π -> s2 ∈ γ π).
      { intros c' s1 s2 H12.
        induction H12 as [| | | | ? ? ? ? ? ? ? ? ? IH |]; intros Ecc' Hγ.
        all: inversion Ecc'; subst.
        - apply IH, Hπ, γ_join; eauto.
        - eauto. }
      eauto using γ_join, postfixpoint_sound.
  Qed.
End Analysis.

(** * Распространение констант (constant propagation) *)

(** ** Задание 3

    Определите абстрактный домен для распространения констант. *)

Inductive flatZ : Type := Bot | Just (n : Z) | Top.

Instance flatZLatticeOp : LatticeOp flatZ :=
{
  ble x y := 
    match x, y with
    | Bot   , _      => true
    | _     , Top    => true
    | Just m, Just n => m =? n
    | _     , _      => false
    end;
  join x y :=
    match x, y with
    | Bot   , _      => y
    | _     , Bot    => x
    | Top   , _      => Top
    | _     , Top    => Top
    | Just m, Just n => if Z.eq_dec m n then x else Top
    end;
  bot := Bot;
  top := Top;
}.

#[refine]
Instance flatZConcretization : Concretization flatZ Z :=
{
  γ x := fun n =>
    match x with
    | Bot    => False
    | Just m => n = m
    | Top    => True
    end;
}.
Proof.
  - intros [| |] [| |]; simpl.
    5: intros E; rewrite Z.eqb_eq in E; congruence.
    all: easy.
  - intros [|m|] [|n|] ? [H | H]; simpl.
    all: now try rewrite H; try  destruct (Z.eq_dec m n).
  - easy.
  - easy.
Defined.

#[refine]
Instance flatZAbsValue : AbsValue flatZ :=
{
  aconst := Just;
  aunop op :=
    let lift1 (op : Z -> Z) : flatZ -> flatZ := fun x =>
      match x with
      | Bot    => Bot
      | Just n => Just (op n)
      | Top    => Top
      end
    in lift1 (eval_unop op);
  abinop op := 
    let lift2 (op : Z -> Z -> Z) : flatZ -> flatZ -> flatZ := fun x y =>
      match x, y with
      | Bot    , _     => Bot
      | _      , Bot   => Bot
      | Just m, Just n => Just (op m n)
      | _      , _     => Top
      end
    in lift2 (eval_binop op)
}.
Proof.
  - easy.
  - intros ? [| |] [|]; simpl; congruence.
  - intros ? ? [| |] [| |] [| | |]; simpl; congruence.
Defined.

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

(** Будем хранить интервал [a, b] в виде пары (-a, b).
Это позволяет избежать расмотрения отдельно значений +∞ и -∞, оставив только +∞. *)

Inductive ZInf := Fin (n : Z) | Inf.
Coercion Fin : Z >-> ZInf.

Record Interval := {
  low  : ZInf;
  high : ZInf;
}.

Definition ZInf_isempty (x : Interval) : bool :=
  match x with
  | {| low := Fin a; high := Fin b |} => if Z_le_dec (-a) b then false else true
  | _ => false
  end.

Instance IntervalLatticeOp : LatticeOp Interval :=
{
  ble x y :=
     let ZInf_ble (m n : ZInf) : bool :=
      match m, n with
      | _, Inf => true
      | Inf, _ => false
      | Fin m, Fin n => if Z_le_dec m n then true else false
      end
    in ZInf_isempty x || (ZInf_ble (low x) (low y) && ZInf_ble (high x) (high y));
  join x y :=
    let ZInf_max (m n : ZInf) : ZInf :=
      match m, n with
      | Fin m, Fin n => Z.max m n
      | _, _ => Inf
      end
    in {| low := ZInf_max (low x) (low y); high := ZInf_max (high x) (high y)|};
  bot := {| low := 0; high := -1 |};
  top := {| low := Inf; high := Inf |};
}.

#[refine]
Instance IntervalConcretization : Concretization Interval Z :=
{
  γ x :=
    let ZInf_γ (n : ZInf) := fun m =>
      match n with
      | Fin n => m <= n
      | Inf   => True
      end  
    in fun n => (-n) ∈ ZInf_γ (low x) /\ n ∈ ZInf_γ (high x);
}.
Proof.
  - intros [a b] [c d] Habcd n; simpl in *.
    apply orb_prop in Habcd as [Hab | Habcd].
    + destruct a as [a|], b as [b|], c as [c|], d as [d|].
      all: try destruct (Z_le_dec (-a) b); lia.
    + apply andb_prop in Habcd as [Hac Hbd].
      destruct a as [a|], b as [b|], c as [c|], d as [d|].
      all: try destruct (Z_le_dec a c); try destruct (Z_le_dec b d); lia.
  - intros [[|] [|]] [[|] [|]]; simpl; lia.
  - simpl; lia.
  - easy.
Defined.

#[refine]
Instance IntervalAbsValue : AbsValue Interval :=
{
  aconst n := {| low := -n; high := n |};
  aunop op x :=
    match op with
    | Oopp => {| low := high x; high := low x |}
    | _    => if ZInf_isempty x then ⊥ else {| low := 0; high := 1 |}
    end;
  abinop op x y :=
    let ZInf_add (m n : ZInf) : ZInf :=
      match m, n with
      | Fin m, Fin n => m + n
      | _    , _     => Inf
      end
    in
      if ZInf_isempty x || ZInf_isempty y
      then ⊥
      else
        match op with
        | Oplus => {| low := ZInf_add (low x) (low y); high := ZInf_add (high x) (high y) |} 
        | _     => {| low := 0; high := 1 |}
        end
}.
Proof.
  - simpl; lia.
  - intros n [a b] [|] Hnab.
    + destruct a, b; simpl in *; lia.
    + destruct a as [a|], b as [b|], n; simpl in *.
      all: try destruct (Z_le_dec (-a) b); simpl; lia.
  - intros m n [a b] [c d] [| | |] Hmab Hncd; simpl in *.
    + destruct a as [a|], b as [b|], c as [c|], d as [d|].
      all: try destruct (Z_le_dec (-a) b); try destruct (Z_le_dec (-c) d); simpl; lia.
    + destruct a as [a|], b as [b|], c as [c|], d as [d|].
      all: try destruct (Z_le_dec (-a) b); try destruct (Z_le_dec (-c) d); simpl.
      all: destruct (m =? n); simpl; lia.
    + destruct a as [a|], b as [b|], c as [c|], d as [d|].
      all: try destruct (Z_le_dec (-a) b); try destruct (Z_le_dec (-c) d); simpl.
      all: destruct (m <? n); simpl; lia.
    + destruct a as [a|], b as [b|], c as [c|], d as [d|].
      all: try destruct (Z_le_dec (-a) b); try destruct (Z_le_dec (-c) d); simpl.
      all: destruct m, n; simpl; lia.
Defined.

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
  [x] ∈ [0; 1], [y] ∈ [12; 12], and [z] ∈ [11; 11].
*)


(** Программа:
<<
    x := 0;
    while x < 10
      do x := x + 1
    end
>>
*)

Definition prog2 : com :=
  "x" ::= Const 0 ;;
  While (Binop Olt (Var "x") (Const 10))
    ("x" ::= Binop Oplus (Var "x") (Const 1)).

Compute
  let a := aceval Interval prog2 ⊤ in
  (get "x" a).

(** Результат анализа:
<<
  = {| low := Inf; high := Inf |}
>>
  [x] неизвестно
*)

(** С другой стороны, при выходе из цикла должно выполняться условие [x] ∈ [10; +∞].
  Наш анализ не может это обнаружить,
  потому что в опредлении функции aceval мы игнорируем значения логических выражений в if и while. *)

(** ** Задание 5

    Реализуйте анализ условий и докажите его корректность
    (создайте файл AbsIntCond.v, скопировав файл AbsInt.v, внесите необходимые изменения) *)
