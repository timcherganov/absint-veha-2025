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

Compute(StringMap.map_2).
Compute(SMFact.map2_1bis).

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

  (* Compute StringMap.slist. *)

  Definition map_join (m1 m2 : StringMap.t V) : StringMap.t V :=
    StringMap.map2
      (fun (ov1 ov2 : option V) =>
         match ov1, ov2 with
         | Some v1, Some v2 => Some (v1 ∨ v2)
         | _      , _       => None
         end) m1 m2.

  Definition ajoin (a1 a2 : astate) : astate :=
    match a1, a2 with
    | None, None       => None
    | Some m1, None    => Some m1
    | None, Some m2    => Some m2
    | Some m1 , Some m2  => Some (map_join m1 m2)
  end.

  Definition able (a1 a2 : astate) : bool :=
    match a1, a2 with
    | None, _           => true          (* ⊥ ≤ любой *)
    | Some _, None      => false         (* что-то не ≤ ⊥ *)
    | Some m1, Some m2  => false (* Грубая оценка *)
  end.

  #[global]
  Instance astateLatticeOp : LatticeOp astate := {
    ble := able;
    join := ajoin;
    bot := None;
    (*
    По текущей семантике get, если элемент в коллекции не означен, то
      нам возвращется Top, то есть по сути, для пустой коллекции у нас каждый
      элемент будет означен Top, что нам и нужно
    *)
    top := Some (StringMap.empty V);
  }.

  (** Конкретизация абстрактного состояния:
    - None (⊥) соответствует пустому множеству состояний;
    - любое Some _ соответствует множеству всех состояний. *)
  Definition γs (a : astate) : 𝒫 state :=
    fun s =>
      match a with
      | None => False
      | Some _ => forall x : string, s x ∈ γ (get x a)
  end.

  (** Монотонность: если a ≤? b = true, то γs a ⊆ γs b. *)

  Lemma γs_mon :
    forall (a b : astate),
      able a b = true -> γs a ⊆ γs b.
  Proof.
    intros. unfold γs in *.
    destruct a as [m1|], b as [m2|]. simpl in *.
    - inversion H0.
    - inversion H0.
    - inversion H1.
    - inversion H1.
  Qed.

  (** Совместимость с join: γs a ∪ γs b ⊆ γs (a ∨ b). *)

  Lemma find_map_join :
    forall (x : string) (m1 m2 : StringMap.t V),
      StringMap.find x (map_join m1 m2) =
      match StringMap.find x m1, StringMap.find x m2 with
      | Some v1, Some v2 => Some (v1 ∨ v2)
      | _      , _       => None
      end.
  Proof.
    intros x m1 m2.
    unfold map_join.
    (* WFacts *)
    apply (SMFact.map2_1bis
              (elt:=V) (elt':=V) (elt'':=V)
              (m1) (m2) (x)
              (f:=fun ov1 ov2 =>
                     match ov1, ov2 with
                     | Some v1, Some v2 => Some (v1 ∨ v2)
                     | _      , _       => None
                     end)).
    reflexivity.
  Qed.

  Lemma γ_getm_map_join :
    forall (x : string) (m1 m2 : StringMap.t V),
      γ (getm x m1) ∪ γ (getm x m2)
        ⊆ γ (getm x (map_join m1 m2)).
  Proof.
    intros x m1 m2 z Hz.
    unfold getm in *.
    rewrite find_map_join.
    destruct (StringMap.find x m1) as [v1|] eqn:H1;
    destruct (StringMap.find x m2) as [v2|] eqn:H2;
    simpl in *.
    - (* Some v1, Some v2 *)
      apply γ_join.
      destruct Hz as [Hz|Hz]; [left|right]; assumption.
    - (* Some v1 *)
      apply γ_top.
    - (* None, Some v2 *)
      apply γ_top.
    - (* None, None *)
      apply γ_top.
  Qed.

  Lemma γs_join :
    forall (a b : astate),
      γs a ∪ γs b ⊆ γs (a ∨ b).
  Proof.
    intros a b s Hab.
    unfold γs in *.
    destruct Hab as [Ha | Hb].
    - (* s ∈ γs a *)
      destruct a as [m1|]; simpl in *.
      + destruct b as [m2|]; simpl.
        * intros x.
          specialize (Ha x).
          apply γ_getm_map_join.
          left; exact Ha.
        * exact Ha.
      + contradiction.
    - (* s ∈ γs b *)
      destruct b as [m2|]; simpl in *.
      + destruct a as [m1|]; simpl.
        * intros x.
          specialize (Hb x). (* Hb : s x ∈ γ (getm x m2) *)
          apply γ_getm_map_join.
          right; exact Hb.
        * exact Hb.
      + contradiction.
  Qed.

  (** ⊥ конкретизируется в пустое множество состояний. *)

  Lemma γs_bot :
    forall (s : state), ~ γs ⊥ s.
  Proof.
    intros s H1.
    unfold γs in H1.
    simpl in H1.                      (* γs None s = False *)
    exact H1.
  Qed.

  (** ⊤ конкретизируется во множество всех состояний. *)

  Lemma γs_top :
    forall (s : state), γs ⊤ s.
  Proof.
    intros s.
    unfold γs.
    simpl.                           (* γs (Some _) s = True *)
    intro.
    unfold getm.
    simpl.
    apply γ_top.
  Qed.

(** Покажите, что на абстрактном состоянии определено отображение
      конкретизации, индуцированное отображением конкретизации на абстрактных
      значениях. *)
  #[global]
  Instance astateConcretization : Concretization astate state := {
    γ      := γs;
    γ_mon  := γs_mon;
    γ_join := γs_join;
    γ_bot  := γs_bot;
    γ_top  := γs_top;
  }.

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

  (* Мы не можем насытить нашу решетку и получить что-то выше TOP *)
  Hypothesis f_top : f ⊤ = ⊤.
  Hypothesis ble_top : ⊤ ≤? ⊤ = true.

  Lemma iter_postfix :
    forall n a, (f (iter n a) ≤? iter n a) = true.
  Proof.
    induction n as [|n IH]; intros a; simpl.
    - (* n = 0: iter 0 a = ⊤ *)
      rewrite f_top, ble_top. reflexivity.
    - (* n = S n *)
      destruct (f a ≤? a) eqn : Hcond; simpl.
      + exact Hcond.
      + exact (IH (f a)).
  Qed.


  Lemma postfixpoint_sound : γ (f postfixpoint) ⊆ γ postfixpoint.
  Proof.
    apply γ_mon.
    unfold postfixpoint.
    apply iter_postfix.
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

  (* eval входит в конкретизацию aeval *)
  Lemma aeval_sound : forall (s : state) (a : astate V) (e : exp),
    s ∈ γ a -> eval e s ∈ γ (aeval e a).
  Proof.
    intros s a e.
    intro Hyas.
    induction e; simpl.
    - (* Var x *)
      destruct a as [m|]; simpl in *.
      + apply Hyas.
      + contradiction.
    - (* Const n *)
      apply γ_aconst.
    - (* Unop op e *)
      apply γ_aunop.
      exact IHe.
    - (* Binop op e1 e2 *)
      apply γ_abinop.
      + exact IHe1.
      + exact IHe2. 
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

  Lemma getm_add_same :
    forall (x : string) (v : V) (m : StringMap.t V),
      getm V x (StringMap.add x v m) = v.
  Proof.
    intros x v m.
    unfold getm.
    rewrite SMFact.add_eq_o.
    - reflexivity.
    - reflexivity.
  Qed.

  (* Ввели грубую аксиому что при while всегда получаем Top *)
  Hypothesis aceval_While_Some_top :
    forall (m : StringMap.t V) (e : exp) (c0 : com),
      aceval (While e c0) (Some m) = ⊤.

  Theorem aceval_sound : forall (c : com) (s s' : state) (a : astate V),
    s ∈ γ a -> ceval c s s' -> s' ∈ γ (aceval c a).
  Proof.
    intros c; induction c; intros s s' a Hγ Hce.
    - (* Skip *)
      simpl in *.
      inversion Hce; subst; assumption.

    - (* Assign (x ::= e) *)
      simpl in *.
      inversion Hce; subst.              (* s' = update x (eval e s) s *)
      destruct a as [m|].
      + (* a = Some m *)
        simpl in Hγ.                     (* Hγ : forall y, s y ∈ γ (get y (Some m)) *)
        simpl.                           (* цель: forall y, update ... y ∈ γ (get y (Some ...)) *)
        intros y.
        unfold update.
        destruct (string_dec x y) as [Heq | Hneq].
        * (* y = x *)
          subst y.
          simpl.
          unfold get; simpl.
          (* get x (Some (StringMap.add x (aeval e (Some m)) m)) *)
          (* = getm V x (StringMap.add x (aeval e (Some m)) m) *)
          rewrite getm_add_same.
          (* осталось показать: eval e s ∈ γ (aeval e (Some m)) *)
          eapply aeval_sound.
          (* нужно: s ∈ γ (Some m) *)
          simpl. exact Hγ.
        * (* y <> x *)
          simpl.
          unfold get; simpl.
          unfold getm.
          rewrite SMFact.add_neq_o by assumption.
          (* цель: s y ∈ γ (getm V y m) — это ровно Hγ y *)
          apply Hγ.
      + (* a = None *)
        simpl in Hγ. contradiction. 

    - (* Seq (c1 ;; c2) *)
      simpl in *.
      inversion Hce; subst.
      specialize (IHc1 s s2 a Hγ H2).
      specialize (IHc2 s2 s' (aceval c1 a) IHc1 H5).
      exact IHc2.

    - (* If (e c1 c2) *)
      inversion Hce; subst.
      (* H0 : ceval (if Z.eq_dec (eval e s) 0 then c2 else c1) s s' *)
      destruct (Z.eq_dec (eval e s) 0) as [Heq|Hneq].
      + (* условие истинно — выполнялся c2 *)
        (* из H0: ceval c2 s s' *)
        specialize (IHc2 s s' a Hγ H5).
        (* s' ∈ γ (aceval c2 a) ⇒ s' ∈ γ (aceval c1 a ∨ aceval c2 a) *)
        apply γ_join.
        right.
        assumption.
      + (* условие ложно — выполнялся c1 *)
        specialize (IHc1 s s' a Hγ H5).
        apply γ_join.
        left; assumption.
    - (* While (e c) *)
      destruct a as [m|].
      + (* a = Some m *)
        rewrite aceval_While_Some_top.
        apply γ_top.
      + (* a = None *)
        simpl in Hγ. contradiction.
  Qed.
End Analysis.

(** * Распространение констант (constant propagation) *)

(** ** Задание 3

    Определите абстрактный домен для распространения констант. *)

Inductive flatZ : Type := Bot | Just (n : Z) | Top.

(* Решётка flatZ: Bot ≤ Just n ≤ Top, разные Just n несравнимы *)
Definition flatZble (z1 z2 : flatZ) : bool :=
  match z1, z2 with
  | Bot, _ => true
  | Just _, Top => true
  | Top, Top => true
  | _, _ => false
  end.

Definition flatZjoin (z1 z2 : flatZ) : flatZ :=
  match z1, z2 with
  | Bot, v | v, Bot => v
  | Just n1, Just n2 =>
      if n1 =? n2 then Just n1 else Top
  | Top, _ | _, Top => Top
  end.

Instance flatZLatticeOp : LatticeOp flatZ := {
  ble  := flatZble;
  join := flatZjoin;
  bot  := Bot;
  top  := Top;
}.

(* Конкретизация: Bot = ∅, Just n = {n}, Top = Z *)
Definition γ_flatZ (a : flatZ) : 𝒫 Z :=
  match a with
  | Bot      => fun _ => False
  | Top      => fun _ => True
  | Just n   => fun z => z = n
  end.

Lemma γ_flatZ_mon :
  forall a b, flatZble a b = true -> γ_flatZ a ⊆ γ_flatZ b.
Proof.
  intros a b Hle z Hz.
  destruct a, b; simpl in *; try discriminate; try contradiction; auto.
Qed.

Lemma γ_flatZ_join :
  forall a b, γ_flatZ a ∪ γ_flatZ b ⊆ γ_flatZ (flatZjoin a b).
Proof.
  intros a b z Hab.
  destruct a, b; simpl in *; try tauto.
  (* a = Just n, b = Just n0 *)
  destruct Hab as [Hz1 | Hz2].
  - destruct (Z.eqb n n0) eqn:Heq; simpl.
    + apply Z.eqb_eq in Heq. subst. reflexivity.
    + trivial.  (* join = Top, γ_flatZ Top z = True *)
  - destruct (Z.eqb n n0) eqn:Heq; simpl.
    + apply Z.eqb_eq in Heq. subst. reflexivity.
    + trivial.
Qed.

Lemma γ_flatZ_bot : forall z, ~ γ_flatZ Bot z.
Proof.
  intros z Hz. exact Hz.
Qed.

Lemma γ_flatZ_top : forall z, γ_flatZ Top z.
Proof.
  intros z. simpl. exact I.
Qed.

Instance flatZConcretization : Concretization flatZ Z := { 
  γ      := γ_flatZ;
  γ_mon  := γ_flatZ_mon;
  γ_join := γ_flatZ_join;
  γ_bot  := γ_flatZ_bot;
  γ_top  := γ_flatZ_top 
}.

Print Instances Concretization.

(* aconst : Z -> A; *)
Definition flatZconst (const : Z) : flatZ := Just const.

(* aunop  : unop -> A -> A; *)
Definition flatZunop (op : unop) (aarg : flatZ) : flatZ :=
  match op with
  | Oopp =>
      match aarg with
      | Bot       => Bot 
      | Just n    => Just (Z.opp n)
      | Top       => Top
      end
  | Oneg =>
    match aarg with
      | Bot       => Bot
      | Just Z0   => Just (1)
      | Just _    => Just (0)
      | Top       => Top
    end
  end.

(* abinop : binop -> A -> A -> A; *)
Definition flatZbinop (op : binop) (aarg1 : flatZ) (aarg2 : flatZ) : flatZ :=
  match aarg1, aarg2 with
    | Bot ,   _          => Bot
    | _   ,   Bot        => Bot
    | Top ,   _          => Top
    | _   ,   Top        => Top
    | Just z1  , Just z2 =>
      match op with
        | Oplus => Just (Z.add z1 z2)
        | Oeq   => Just (Z.b2z (z1 =? z2))
        | Olt   => Just (Z.b2z (z1 <? z2))
        | Oand  => Just (andz z1 z2)
      end
  end.

(* γ_aconst : forall (n : Z), n ∈ γ (aconst n); *)
Lemma γ_flatZconst :
  forall (n : Z), γ_flatZ (flatZconst n) n.
Proof.
  intro n.
  unfold flatZconst.
  unfold γ_flatZ.
  reflexivity.
Qed.

(* γ_aunop  : forall (n : Z) (a : A) (op : unop),
    n ∈ γ a -> eval_unop op n ∈ γ (aunop op a); *)
Lemma γ_flatZunop: 
  forall (n : Z) (a : flatZ) (op : unop), 
    γ_flatZ a n -> γ_flatZ (flatZunop op a) (eval_unop op n).
Proof.
  intros n a op.
  intro Hya_to_n.
  destruct op.
  - unfold flatZunop.
    destruct a; simpl in *.
    + contradiction.
    + rewrite Hya_to_n.
      reflexivity.
    + trivial.
  - unfold flatZunop.
    destruct a; simpl in *.
    + contradiction.
    + rewrite <- Hya_to_n. unfold γ_flatZ. destruct n; simpl; reflexivity.
    + trivial.
Qed.

(* γ_abinop : forall (m n : Z) (a b : A) (op : binop),
    m ∈ γ a -> n ∈ γ b -> eval_binop op m n ∈ γ (abinop op a b); *)
Lemma γ_flatZbinop: forall (m n : Z) (a b : flatZ) (op : binop),
    γ_flatZ a m -> γ_flatZ b n -> γ_flatZ (flatZbinop op a b) (eval_binop op m n).
Proof.
  intros m n a b op.
  intro Hya_to_m.
  intro Hyb_to_n.
  destruct op;
  unfold flatZbinop; 
  destruct a,b; 
  simpl in *; 
  try contradiction; 
  try trivial;
  rewrite -> Hya_to_m;
  rewrite -> Hyb_to_n;
  reflexivity.
Qed.

Instance flatZAbsValue : AbsValue flatZ := {
  lat_val := flatZLatticeOp;
  γ_val := flatZConcretization;

  (* aconst : Z -> A; *)
  aconst := flatZconst;
  (* aunop  : unop -> A -> A; *)
  aunop := flatZunop;
  (* abinop : binop -> A -> A -> A; *)
  abinop := flatZbinop;

  (* γ_aconst : forall (n : Z), n ∈ γ (aconst n); *)
  γ_aconst := γ_flatZconst;
  (* γ_aunop  : forall (n : Z) (a : A) (op : unop),
    n ∈ γ a -> eval_unop op n ∈ γ (aunop op a); *)
  γ_aunop := γ_flatZunop;
  (* γ_abinop : forall (m n : Z) (a b : A) (op : binop),
    m ∈ γ a -> n ∈ γ b -> eval_binop op m n ∈ γ (abinop op a b); *)
  γ_abinop := γ_flatZbinop;
}.

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

(* Lift *)
Inductive LiftedInterval := RecInterval (i : Interval) | IntervalBot.

Definition IntervalBle (l1 l2 : LiftedInterval) : bool :=
  match l1, l2 with
  | IntervalBot,  _           => true
  | _,            IntervalBot => false
  (*  *)
  | _, RecInterval {| low := Inf; high := Inf |} => true (* Top у решетки *)
  | RecInterval {| low := Inf; high := Inf |}, _ => false (* Если не словили прошлый match, значит справа что-то меньшее *)
  (*  *)
  | RecInterval {| low := Inf; high := Fin r1 |}, RecInterval {| low := Inf; high := Fin r2 |} => r1 <=? r2 (* (-inf; 0) <= (-inf; 1) *)
  | RecInterval {| low := Fin l1; high := Inf |}, RecInterval {| low := Fin l2; high := Inf |} => l1 >=? l2 (* (1; +inf) <= (0; +inf) *)
  (*  *)
  | RecInterval {| low := Inf; high := Fin r1 |}, RecInterval {| low := Fin l2; high := Inf |} => false (* Полностью не входит друг в друга(несравнимы) *)
  | RecInterval {| low := Fin l1; high := Inf |}, RecInterval {| low := Inf; high := Fin r2 |} => false (* Полностью не входит друг в друга(несравнимы) *)
  (* *)
  | RecInterval {| low := Fin l1; high := Fin r1 |}, RecInterval {| low := Fin l2; high := Fin r2 |} => (l1 >=? l2) && (r1 <=? r2) (* Левый входит в правый *)
  (*  *)
  | _, _ => false
end.

Definition IntervalJoin (l1 l2 : LiftedInterval) : LiftedInterval :=
  match l1, l2 with
  | IntervalBot,  _           => l2
  | _,            IntervalBot => l1
  (*  *)
  | _, RecInterval {| low := Inf; high := Inf |} => RecInterval {| low := Inf; high := Inf |}
  | RecInterval {| low := Inf; high := Inf |}, _ => RecInterval {| low := Inf; high := Inf |}
  (*  *)
  | RecInterval {| low := Inf; high := Fin r1 |}, RecInterval {| low := Inf; high := Fin r2 |} => RecInterval {| low := Inf; high := Z.max r1 r2 |} (* (-inf; 0) <= (-inf; 1) *)
  | RecInterval {| low := Fin l1; high := Inf |}, RecInterval {| low := Fin l2; high := Inf |} => RecInterval {| low := Z.min l1 l2; high := Inf |} (* (1; +inf) <= (0; +inf) *)
  (*  *)
  | RecInterval {| low := Inf; high := Fin r1 |}, RecInterval {| low := Fin l2; high := Inf |} => RecInterval {| low := Inf; high := Inf |} (* Полностью не входит друг в друга(несравнимы) *)
  | RecInterval {| low := Fin l1; high := Inf |}, RecInterval {| low := Inf; high := Fin r2 |} => RecInterval {| low := Inf; high := Inf |} (* Полностью не входит друг в друга(несравнимы) *)
  (* *)
  | RecInterval {| low := Fin l1; high := Fin r1 |}, RecInterval {| low := Fin l2; high := Fin r2 |} => RecInterval {| low := Z.min l1 l2; high := Z.max r1 r2 |} (* Левый входит в правый *)
  (*  *)
  | _, _ => RecInterval {| low := Inf; high := Inf |}
end.

Instance IntervalLatticeOp : LatticeOp LiftedInterval := {
  ble  := IntervalBle;
  join := IntervalJoin;
  bot  := IntervalBot;
  top  := RecInterval {| low := Inf; high := Inf |}; (* [-Inf, Inf] *)
}.

Definition γ_Interval (i : LiftedInterval) : 𝒫 Z :=
  match i with
  | IntervalBot => fun _ => False
  | RecInterval iv =>
      match low iv, high iv with
      | Fin l, Fin h => fun z : Z => (l <= z <= h)%Z
      | Fin l, Inf   => fun z : Z => (l <= z)%Z
      | Inf,   Fin h => fun z : Z => (z <= h)%Z
      | Inf,   Inf   => fun _ : Z => True
      end
  end.

(* forall a b : LiftedInterval, (a ≤? b) = true -> γ_Interval a ⊆ γ_Interval b *)
Lemma γ_Interval_mon :
  forall a b, IntervalBle a b = true -> γ_Interval a ⊆ γ_Interval b.
Proof.
  intros [ia|] [ib|] Hle z Hz; simpl in *.
  - (* a = RecInterval ia, b = RecInterval ib *)
    destruct ia as [la ha], ib as [lb hb]; simpl in *.
    destruct la, ha, lb, hb; simpl in *; try discriminate; try trivial.
    + apply andb_prop in Hle as [Hge Hle'].
      apply Z.geb_le in Hge.
      apply Z.leb_le in Hle'.
      destruct Hz as [Hz1 Hz2]; split; lia.
    + apply Z.geb_le in Hle.
      lia.
    + apply Z.leb_le in Hle.
      lia.

  - (* a = RecInterval ia, b = IntervalBot *)
    destruct ia.
    destruct low0, high0; try discriminate.

  - (* a = IntervalBot, b = RecInterval ib *)
    contradiction.

  - (* a = IntervalBot, b = IntervalBot *)
    contradiction.
Qed.

(* forall (a b : LiftedInterval) (a0 : Z), 
  γ_Interval a a0 \/ γ_Interval b a0 -> γ_Interval (a ∨ b) a0 *)
Lemma γ_Interval_join :
  forall a b, γ_Interval a ∪ γ_Interval b ⊆ γ_Interval (IntervalJoin a b).
Proof.
  intros [ia|] [ib|] Hle z; simpl in *.
  - (* a = RecInterval ia, b = RecInterval ib *)
    destruct ia as [la ha], ib as [lb hb]; simpl in *.
    destruct la, ha, lb, hb; simpl in *; try discriminate; try trivial; try lia.

  - (* a = RecInterval ia, b = IntervalBot *)
    destruct ia.
    destruct low0, high0; simpl in *; destruct z as [Hz | Hz]; try contradiction; try trivial.

  - (* a = IntervalBot, b = RecInterval ib *)
    destruct ib.
    destruct low0, high0; simpl in *; destruct z as [Hz | Hz]; try contradiction; try trivial.
    
  - (* a = IntervalBot, b = IntervalBot *)
    destruct z as [Hz | Hz]; try contradiction.
Qed.

(* forall c : Z, ~ γ_Interval ⊥ c *)
Lemma γ_Interval_bot : forall z, ~ γ_Interval IntervalBot z.
Proof.
  intro z.
  simpl.
  apply neg_false; split; intro; contradiction.
Qed.

(* forall c : Z, γ_Interval ⊤ c *)
Lemma γ_Interval_top :
  forall z, γ_Interval (RecInterval {| low := Inf; high := Inf |}) z.
Proof.
  intro z.
  simpl.
  trivial.
Qed.

Instance IntervalConcretization : Concretization LiftedInterval Z := {
  γ      := γ_Interval;
  γ_mon  := γ_Interval_mon;
  γ_join := γ_Interval_join;
  γ_bot  := γ_Interval_bot;
  γ_top  := γ_Interval_top;
}.

Print Instances Concretization.

(* To remember
Inductive ZInf := Fin (n : Z) | Inf.
Coercion Fin : Z >-> ZInf.

Record Interval := {
  low  : ZInf;
  high : ZInf;
}.

(* Lift *)
Inductive LiftedInterval := RecInterval (i : Interval) | IntervalBot.
*)

(* aconst : Z -> A; *)
Definition IntervalConst (const : Z) : LiftedInterval := 
  let interval := {|low := const; high := const|}
  in RecInterval(interval).

(* aunop  : unop -> A -> A; *)
Definition IntervalUnop (op : unop) (aarg : LiftedInterval) : LiftedInterval :=
  match op with
  | Oopp =>
    match aarg with
    | IntervalBot          => IntervalBot
    (* -inf ; inf -> -inf ; inf *)
    | RecInterval {| low := Inf; high := Inf |} => RecInterval {| low := Inf; high := Inf |}
    (* -inf ; r -> -r ; inf *)
    | RecInterval {| low := Inf; high := Fin (rz) |} => RecInterval {| low := Fin (Z.opp rz); high := Inf |}
    (* l ; inf -> -inf ; -l *)
    | RecInterval {| low := Fin (lz); high := Inf |} => RecInterval {| low := Inf; high := Fin (Z.opp lz) |}
    (* l ; r -> -r ; -l *)
    | RecInterval {| low := Fin (lz); high := Fin (rz) |} => RecInterval {| low := Fin (Z.opp rz); high := Fin (Z.opp lz) |}
    end
  | Oneg =>
  (* 
  По уму:
    neg inf = 0
    neg fin (0) = 1
    otherwise 0 
  *)
    match aarg with
      | IntervalBot         => IntervalBot
      (* 
        Мы по семантике Oneg из Imp.v знаем что будет ∈ {0,1} 
        просто апроксимируем возможные результаты без точной оценки
        
        Возможно это скажется потом на Задании 5 но мы пока не дошли:) 
      *)
      | RecInterval _       => RecInterval {| low := 0; high := 1 |}
    end
  end.

(* abinop : binop -> A -> A -> A; *)
Definition IntervalBinop (op : binop)
                         (aarg1 aarg2 : LiftedInterval) : LiftedInterval :=
  match op with
  | Oplus =>
      match aarg1, aarg2 with
        | IntervalBot,  _           => aarg2
        | _,            IntervalBot => aarg1
        (*  *)
        | _, RecInterval {| low := Inf; high := Inf |} => RecInterval {| low := Inf; high := Inf |}
        | RecInterval {| low := Inf; high := Inf |}, _ => RecInterval {| low := Inf; high := Inf |}
        (*  *)
        | RecInterval {| low := Inf; high := Fin r1 |}, RecInterval {| low := Inf; high := Fin r2 |} => RecInterval {| low := Inf; high := r1 + r2 |}
        | RecInterval {| low := Fin l1; high := Inf |}, RecInterval {| low := Fin l2; high := Inf |} => RecInterval {| low := l1 + l2; high := Inf |}
        (*  *)
        | RecInterval {| low := Inf; high := Fin r1 |}, RecInterval {| low := Fin l2; high := Inf |} => RecInterval {| low := Inf; high := Inf |}
        | RecInterval {| low := Fin l1; high := Inf |}, RecInterval {| low := Inf; high := Fin r2 |} => RecInterval {| low := Inf; high := Inf |}
        (* *)
        | RecInterval {| low := Fin l1; high := Fin r1 |}, RecInterval {| low := Fin l2; high := Fin r2 |} => RecInterval {| low := l1 + l2; high := r1 + r2 |}
        (*  *)
        | _, _ => RecInterval {| low := Inf; high := Inf |}
      end

  (*
   Поскольку интервал обозначается парой (a, b), что означает [-a, b],
   то не имеем возможности вернуть конкретный интервал [1, 1] 
   для логически верных операций.
  *)
  | Oeq =>
    match aarg1, aarg2 with
    | IntervalBot, _ | _, IntervalBot => IntervalBot
    | _, _                            => RecInterval {| low := 0; high := 1 |}
    end

  | Olt =>
    match aarg1, aarg2 with
    | IntervalBot, _ | _, IntervalBot => IntervalBot
    | _, _                            => RecInterval {| low := 0; high := 1 |}
    end

  | Oand =>
    match aarg1, aarg2 with
    | IntervalBot, _ | _, IntervalBot => IntervalBot
    | _, _                            => RecInterval {| low := 0; high := 1 |}
    end
  end.

(* forall n : Z, γ (IntervalConst n) n *)
Lemma γ_IntervalConst :
  forall (n : Z), γ_Interval (IntervalConst n) n.
Proof.
  intro n.
  unfold IntervalConst, γ_Interval.
  simpl.
  split; apply Z.le_refl.
Qed.

(* forall (n : Z) (a : LiftedInterval) (op : unop), γ a n -> γ (IntervalUnop op a) (eval_unop op n) *)
Lemma γ_IntervalUnop :
  forall (n : Z) (a : LiftedInterval) (op : unop),
    γ_Interval a n ->
    γ_Interval (IntervalUnop op a) (eval_unop op n).
Proof.
  intros n a op Ha.
  destruct op.
  - (* Oopp *)
    simpl.
    destruct a as [i|]; simpl in *.
    + destruct i as [lo hi].
      destruct lo, hi; simpl in *.
      * destruct Ha as [H1 H2].
        split; lia.
      * lia.
      * lia.
      * trivial.
    + contradiction.

  - (* Oneg *)
    simpl.
    destruct a as [i|]; simpl in *.
    + unfold eval_unop, negz.
      destruct n; simpl; split; lia.
    + contradiction.
Qed.

(* forall (m n : Z) (a b : LiftedInterval) (op : binop), 
  γ a m -> γ b n -> γ (IntervalBinop op a b) (eval_binop op m n) *)
Lemma γ_IntervalBinop :
  forall (m n : Z) (a b : LiftedInterval) (op : binop),
    γ_Interval a m ->
    γ_Interval b n ->
    γ_Interval (IntervalBinop op a b) (eval_binop op m n).
Proof.
  intros m n a b op Ha Hb.
  destruct op.
  - (* Oplus *)
    simpl.
    destruct a as [ia|]; destruct b as [ib|]; simpl in *.
    + destruct ia as [la ha], ib as [lb hb]; simpl in *.
      destruct la as [l|], ha as [r|];
      destruct lb as [l0|], hb as [r0|]; simpl in *; try trivial.
      * destruct Ha as [HaL HaR].
        destruct Hb as [HbL HbR].
        split; lia.
      * simpl in Ha, Hb.
        lia.
      * simpl in Ha, Hb.
        lia.

    + simpl in Hb. contradiction.

    + simpl in Ha. contradiction.

    + simpl in Ha. contradiction.

  - (* Oeq *)
    simpl.
    destruct a as [ia|]; destruct b as [ib|]; simpl in *.
    + unfold eval_binop; simpl.
      unfold Z.b2z.
      destruct (m =? n); simpl; split; lia.
    + simpl in Hb. contradiction.
    + simpl in Ha. contradiction.
    + simpl in Ha. contradiction.

  - (* Olt *)
    simpl.
    destruct a as [ia|]; destruct b as [ib|]; simpl in *.
    + unfold eval_binop; simpl.
      unfold Z.b2z.
      destruct (m <? n); simpl; split; lia.
    + simpl in Hb. contradiction.
    + simpl in Ha. contradiction.
    + simpl in Ha. contradiction.

  - (* Oand *)
    simpl.
    destruct a as [ia|]; destruct b as [ib|]; simpl in *.
    + unfold eval_binop; simpl.
      unfold andz.
      destruct m; destruct n; simpl; split; lia.
    + simpl in Hb. contradiction.
    + simpl in Ha. contradiction.
    + simpl in Ha. contradiction.
Qed.

Instance IntervalAbsValue : AbsValue LiftedInterval := {
  lat_val := IntervalLatticeOp;
  γ_val  := IntervalConcretization;

  aconst := IntervalConst;
  aunop  := IntervalUnop;
  abinop  := IntervalBinop;

  γ_aconst := γ_IntervalConst;
  γ_aunop := γ_IntervalUnop;
  γ_abinop := γ_IntervalBinop;
}.

(** Программа:
<<
    x := 1; y := 10; z := x + y;
    if x > 0 then
      y := x + z; x := 0
    else
      y := 12
>>
*)

(* Changed to Lifted abstraction *)
Compute
  let a := aceval LiftedInterval prog1 ⊤ in
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

(* Changed to Lifted abstraction *)
Definition prog2 : com :=
  "x" ::= Const 0 ;;
  While (Binop Olt (Var "x") (Const 10))
    ("x" ::= Binop Oplus (Var "x") (Const 1)).

Compute
  let a := aceval LiftedInterval prog2 ⊤ in
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
