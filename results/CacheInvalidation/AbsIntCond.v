From Stdlib Require Import FMaps Lia String ZArith.
From AbsInt Require Import Imp.

Local Open Scope Z_scope.
Generalizable Variables A C.

(** * Интерфейс для абстрактных доменов *)

(** Операции на решетке. *)

Class LatticeOp A := {
  ble : A -> A -> bool;
  join : A -> A -> A;
  meet : A -> A -> A;
  bot : A;
  top : A;
}.

(** Нотация для операций решетки. *)

Infix "∨" := join (at level 50, no associativity).
Infix "∧" := meet (at level 50, no associativity).
Infix "≤?" := ble (at level 70, no associativity).
Notation "⊥" := bot.
Notation "⊤" := top.

(** Нотация для работы с подмножествами. *)

Notation "'𝒫' A" := (A -> Prop) (at level 0).
Notation "x ∈ X" := (X x) (at level 19, only parsing).
Notation "X ⊆ Y" := (forall a, X a -> Y a) (at level 20).
Notation "X ∪ Y" := (fun x => X x \/ Y x) (at level 19).
Notation "X ∩ Y" := (fun x => X x /\ Y x) (at level 19).

(** Отображение конкретизации - монотонное отображение из абстрактного
    домена в подмножества элементов конкретного домена. *)

Class Concretization A `{Alat : LatticeOp A} C := {
  γ : A -> 𝒫 C;

  γ_mon  : forall (a b : A), a ≤? b = true -> γ a ⊆ γ b;
  γ_join : forall (a b : A), γ a ∪ γ b ⊆ γ (a ∨ b);
  γ_meet : forall (a b : A), γ a ∩ γ b ⊆ γ (a ∧ b);
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

  alt : A -> A;
  age : A -> A;

  γ_aconst : forall (n : Z), n ∈ γ (aconst n);
  γ_aunop  : forall (n : Z) (a : A) (op : unop),
    n ∈ γ a -> eval_unop op n ∈ γ (aunop op a);
  γ_abinop : forall (m n : Z) (a b : A) (op : binop),
    m ∈ γ a -> n ∈ γ b -> eval_binop op m n ∈ γ (abinop op a b);
  γ_alt : forall (m n : Z) (a : A),
    m < n -> n ∈ γ a -> m ∈ γ (alt a);
  γ_age : forall (m n : Z) (a : A),
    m >= n -> n ∈ γ a -> m ∈ γ (age a);
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

  Check StringMap.fold.

  #[global]
  Instance astateLatticeOp : LatticeOp astate := {
    ble m1 m2 :=
      match m1, m2 with
      | None, _ => true
      | _, None => false 
      | Some m1', Some m2' => SMProp.for_all (fun k v => (getm k m1') ≤? v) m2'
      end;
    join m1 m2 :=
      match m1, m2 with
      | _, None => m1
      | None, _ => m2
      | Some m1', Some m2' => Some (StringMap.map2 (fun v1 v2 =>
        match v1, v2 with
        | None, _ => None
        | _, None => None
        | Some v1', Some v2' => Some (v1' ∨ v2')
        end) m1' m2')
      end;
    meet m1 m2 :=
      match m1, m2 with
      | _, None => None
      | None, _ => None
      | Some m1', Some m2' => Some (StringMap.map2 (fun v1 v2 =>
        match v1, v2 with
        | None, None => None
        | Some v1', None => Some v1'
        | None, Some v2' => Some v2'
        | Some v1', Some v2' => Some (v1' ∧ v2')
        end) m1' m2')
      end;
    bot := None;
    top := Some (StringMap.empty V);
  }.

  (** Покажите, что на абстактном состоянии определено отображение
      конкретизации, индуцированное отображением конкретизации на абстрактных
      значениях. *)
  Definition γ_astate (a : astate) : 𝒫 state :=
    fun st => forall x : string, (st x) ∈ (γ (get x a)).

  Lemma γ_astate_mon : forall (a b : astate), a ≤? b = true -> γ_astate a ⊆ γ_astate b.
    Proof.
      unfold γ_astate. intros a b Hab s Hs x.
      destruct a; destruct b; simpl in *; try discriminate.
      - unfold getm. destruct (StringMap.find x t0) eqn:Hfind.
        + rewrite SMProp.for_all_iff in Hab. 
          specialize Hab with x v.
          rewrite SMFact.find_mapsto_iff in Hab.
          apply Hab in Hfind.
          eapply γ_mon.
          * apply Hfind.
          * apply Hs.
          * intros k1 k2 Hk u w Huw. congruence.    
        + apply γ_top.
      - specialize Hs with ("any" : string). apply γ_bot in Hs. contradiction.
      - specialize Hs with ("any" : string). apply γ_bot in Hs. contradiction. 
    Qed. 

  Lemma γ_astate_join : forall (a b : astate), γ_astate a ∪ γ_astate b ⊆ γ_astate (a ∨ b).
  Proof.
    intros a b s Hab x.
    destruct a; destruct b; simpl in *.
    - unfold getm. rewrite SMFact.map2_1bis. 2:{ reflexivity. }
      unfold γ_astate in Hab. simpl in Hab. unfold getm in Hab.
      destruct Hab as [Hab | Hab]; specialize (Hab x); destruct (StringMap.find x t) eqn:Ht; destruct (StringMap.find x t0) eqn:Ht0;
      try apply γ_top; apply γ_join; auto. 
    - destruct Hab as [Ha | Hb].
      + apply Ha. 
      + exfalso. eapply γ_bot. apply Hb with (x := "any" : string).
    - destruct Hab as [Ha | Hb].
      + exfalso. eapply γ_bot. apply Ha with (x := "any" : string).
      + apply Hb.
    - destruct Hab as [Hab | Hab]; exfalso; eapply γ_bot; apply Hab with (x := "any" : string).
  Qed.

  Lemma γ_astate_meet : forall (a b : astate), γ_astate a ∩ γ_astate b ⊆ γ_astate (a ∧ b).
  Proof.
    intros a b s Hab. destruct a; destruct b; simpl in *.
    - intros x. 
      destruct Hab as [Ha Hb]. specialize (Ha x). specialize (Hb x).
      unfold get in *. unfold getm in *. 
      rewrite SMFact.map2_1bis. 2:{ reflexivity. }
      destruct (StringMap.find x t) eqn:Ht; destruct (StringMap.find x t0) eqn:Ht0;
      try apply γ_top; try apply γ_meet; auto.
    - exfalso. eapply γ_bot. apply Hab with (x := "any" : string).
    - exfalso. eapply γ_bot. apply Hab with (x := "any" : string).
    - exfalso. eapply γ_bot. apply Hab with (x := "any" : string).
  Qed.
    
  Lemma γ_astate_bot : forall (s : state), ~ s ∈ γ_astate ⊥.
  Proof.
    unfold γ_astate. intros s Hs. eapply γ_bot.
    specialize Hs with ("any" : string). apply Hs.
  Qed.

  Lemma γ_astate_top : forall (s : state), s ∈ γ_astate ⊤.
  Proof.
    unfold γ_astate. intros s x.
    apply γ_top.
  Qed.

  #[global]
  Instance astateConcretization : Concretization astate state := {
    γ := γ_astate;

    γ_mon := γ_astate_mon;
    γ_join := γ_astate_join;
    γ_meet := γ_astate_meet;
    γ_bot := γ_astate_bot;
    γ_top := γ_astate_top;
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

  Lemma postfixpoint_sound :
    γ (f postfixpoint) ⊆ γ postfixpoint.
  Proof.
   unfold postfixpoint. generalize dependent ⊥. generalize dependent niter.
   induction n as [|n Hn].
   - simpl. intro a. intros c Hc. apply γ_top.
   - simpl. intro a. destruct (f a ≤? a) eqn:Hh.
     + apply γ_mon. assumption.
     + apply Hn.
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
    intros s a. induction e; simpl.
    - intros Ha. unfold γ_astate in Ha. apply Ha. 
    - intros Ha. apply γ_aconst.
    - intros Ha. apply γ_aunop. apply IHe. assumption.
    - intros Ha. apply γ_abinop; [apply IHe1 | apply IHe2]; assumption.
  Qed.

  (* Уточнение абстрактного состояния условиями *)
  (* Здесь реализован примитивный анализ, который понимает только
     конъюнкции и (не)равенства с переменной на левой стороне. *)
  Fixpoint assume_true (e : exp) (a : astate V) : astate V :=
    match e with
    | Binop Olt (Var x) e => set x (get x a ∧ alt (aeval e a)) a
    | Binop Oeq (Var x) e => set x (get x a ∧ aeval e a) a
    | Binop Oand e1 e2 => assume_true e1 a ∧ assume_true e2 a
    | _ => a
    end.

  Fixpoint assume_false (e : exp) (a : astate V) : astate V :=
    match e with
    | Binop Olt (Var x) e => set x (get x a ∧ age (aeval e a)) a
    | Binop Oand e1 e2 => assume_false e1 a ∨ assume_false e2 a
    | _ => a
    end.

  (** Абстрактная семантика команд. *)

  Fixpoint aceval (c : com) (a : astate V) : astate V :=
    match c with
    | Skip       => a
    | x ::= e    => set x (aeval e a) a
    | c1 ;; c2   => aceval c2 (aceval c1 a)
    | If e c1 c2 => aceval c1 (assume_true e a) ∨ aceval c2 (assume_false e a)
    | While e c  => assume_false e (postfixpoint (fun X => a ∨ assume_true e (aceval c X)))
    end.

  (** ** Задание 2

      Докажите, что абстрактная семантика комманд аппроксимирует конкретную
      семантику команд. *)

  Lemma get_set_eq : forall (t: StringMap.t V) (k x : string) (v : V),
    x = k -> get k (set x v (Some t)) = v.
  Proof.
    intros t k x v Heq.
    simpl. unfold getm. rewrite SMFact.add_eq_o; auto.
  Qed.
    
  Lemma get_set_neq : forall (a : astate V) (k x : string) (v : V),
    x <> k -> get k (set x v a) = get k a.
  Proof.
    intros a k x v Hneq.
    destruct a eqn:Ha.
    - simpl. unfold getm. rewrite SMFact.add_neq_o; auto.
    - reflexivity.
  Qed.

  Lemma b2z_zero : forall (b : bool), Z.b2z b = 0 <-> b = false.
  Proof.
    split; intros Heq; destruct b; auto; inversion Heq.
  Qed.

  Lemma b2z_nonzero : forall (b : bool), Z.b2z b <> 0 <-> b = true.
  Proof.
    split; intros Heq; destruct b; simpl; auto; inversion Heq.
    intros Hcontra. inversion Hcontra.
  Qed.

  Lemma lt_false : forall (a b : Z),
    (a <? b) = false -> a >= b.
  Proof. lia. Qed.

  Lemma lt_true : forall (a b : Z), 
    (a <? b) = true -> a < b.
  Proof. lia. Qed.
  
  Lemma andz_true : forall (a b : Z),
    andz a b <> 0 -> a <> 0 /\ b <> 0.
  Proof. intros a b Hab. destruct a; destruct b; split; simpl in *; auto;
    intros Hcontra; inversion Hcontra.
  Qed.

  Lemma andz_false : forall (a b : Z),
    andz a b = 0 -> a = 0 \/ b = 0.
  Proof. intros a b Hab. destruct a; destruct b; simpl in *; auto; inversion Hab.
  Qed.

  Lemma assume_false_sound : forall (s : state) (a : astate V) (e : exp),
    eval e s = 0 -> γ a s -> γ (assume_false e a) s.
  Proof.
    intros s a e. generalize dependent s. generalize dependent a.
    induction e; auto.
    intros a s Hzero Has.
    destruct op; auto.
    destruct e1; auto.
    - intros y. specialize (Has y) as Hasy.
      unfold assume_false. fold assume_false.
      simpl. unfold get in *. unfold getm in *.
      destruct a eqn:Ha; try assumption.
      simpl. destruct (string_dec x y) eqn:Hdeqeq; subst.
      + simpl. rewrite SMFact.add_eq_o; try assumption.
        destruct (StringMap.find y t) eqn:Hfind; apply γ_meet; subst; split; auto.
        * apply γ_age with (n := eval e2 s). simpl in Hzero. 
          -- rewrite b2z_zero in Hzero. lia.
          -- apply aeval_sound. auto.
        * apply γ_age with (n := eval e2 s). simpl in Hzero. 
          -- rewrite b2z_zero in Hzero. lia.
          -- apply aeval_sound. auto.
        * reflexivity.
      + simpl. rewrite SMFact.add_neq_o; try assumption.
    - unfold assume_false. fold assume_false.
      apply γ_join.
      simpl in Hzero. apply andz_false in Hzero.
      destruct Hzero; auto.
  Qed. 
    
  Lemma assume_true_sound : forall (s : state) (a : astate V) (e : exp),
    eval e s <> 0 -> γ a s -> γ (assume_true e a) s.
  Proof.
    intros s a e. generalize dependent s. generalize dependent a.
    induction e; auto.
    destruct op; auto.
    - destruct e1; auto. intros a s Hnonzero Has y.
      unfold assume_true. simpl. specialize (Has y) as Hasy.
      unfold get in *. unfold getm in *. unfold set in *.
      destruct a eqn:Ha. 2:{ apply γ_bot in Hasy. contradiction. }
      destruct (string_dec x y) eqn:Hxy; subst.
      + rewrite SMFact.add_eq_o; try reflexivity.
        apply γ_meet. split; try assumption.
        simpl in Hnonzero.
        rewrite b2z_nonzero in Hnonzero.
        rewrite Z.eqb_eq in Hnonzero.
        rewrite Hnonzero.
        apply aeval_sound.
        assumption.
      + rewrite SMFact.add_neq_o; try assumption.
    - destruct e1; auto. intros a s Hnonzero Has y.
      unfold assume_true. simpl. specialize (Has y) as Hasy.
      unfold get in *; unfold getm in *. unfold set in *.
      destruct a eqn:Ha. 2:{ apply γ_bot in Hasy. contradiction. }
      destruct (string_dec x y) eqn:Hxy; subst.
      + rewrite SMFact.add_eq_o; try reflexivity.
        simpl in Hnonzero.
        rewrite b2z_nonzero in Hnonzero.
        apply lt_true in Hnonzero.
        apply γ_meet.
        split; try assumption; apply (γ_alt _ _ _ Hnonzero);
        apply aeval_sound; assumption.
      + rewrite SMFact.add_neq_o; try assumption.
    - intros a s Hand Has. unfold assume_true. fold assume_true.
      apply γ_meet.
      apply andz_true in Hand. destruct Hand as [He1 He2].
      specialize (IHe1 _ _ He1 Has).
      specialize (IHe2 _ _ He2 Has).
      auto.
  Qed.

  Theorem aceval_sound : forall (c : com) (s s' : state) (a : astate V),
    s ∈ γ a -> ceval c s s' -> s' ∈ γ (aceval c a).
  Proof.
    intros c. intros s s' a Has Hceval. generalize dependent a. induction Hceval.
    - intros a Ha. assumption.
    - intros a Hs k. simpl. unfold update.
      destruct (string_dec x k) as [Heq | Hneq] eqn:Hdeceq.
      + destruct a.
         * rewrite (get_set_eq _ _ _ _ Heq).
          apply aeval_sound. assumption.
         * subst. exfalso. eapply γ_bot. apply Hs.
      + rewrite (get_set_neq _ _ _ _ Hneq). auto.
    - intros a Ha. apply IHHceval2. apply IHHceval1. assumption.
    - intros a Ha. apply γ_join. fold aceval.
      destruct (eval e s1) eqn:Heval; simpl in IHHceval.
      + right. apply IHHceval. apply assume_false_sound; assumption.
      + left. apply IHHceval. apply assume_true_sound; try assumption.
        intros Heq. rewrite Heq in Heval. inversion Heval.
      + left. apply IHHceval. apply assume_true_sound; try assumption.
        intros Heq. rewrite Heq in Heval. inversion Heval.
    - (* EWhileTrue *)
      (* Я пытался, но довести до конца этот случай так и не вышло. *)
      admit.
    - intros a Ha. unfold aceval; fold aceval. apply assume_false_sound; try assumption.
      apply postfixpoint_sound. apply γ_join. auto. 
  Admitted.
End Analysis.

(** * Распространение констант (constant propagation) *)

(** ** Задание 3

    Определите абстрактный домен для распространения констант. *)

Inductive flatZ : Type := Bot | Just (n : Z) | Top.

Instance flatZLatticeOp : LatticeOp flatZ := {
  ble a b :=
    match a, b with
    | Bot, _ => true
    | _, Top => true
    | Just n, Just m => n =? m
    | _, _ => false
    end;
  join a b :=
    match a, b with
    | Bot, x => x
    | x, Bot => x
    | Just n, Just m => if n =? m then Just n else Top
    | _, _ => Top
    end;
  meet a b :=
    match a, b with
    | Bot, _ => Bot
    | _, Bot => Bot
    | Top, x => x
    | x, Top => x
    | Just n, Just m => if n =? m then Just n else Bot
    end;
  bot := Bot;
  top := Top;
}.

Definition γ_flatZ (a : flatZ) : 𝒫 Z :=
  match a with
  | Bot     => fun _ => False
  | Just n  => fun m => m = n
  | Top     => fun _ => True
  end.

Lemma γ_flatZ_mon : forall (a b : flatZ), a ≤? b = true -> γ_flatZ a ⊆ γ_flatZ b.
Proof.
  intros a b Hab m Hm.
  destruct a; destruct b; try apply Z.eqb_eq in Hab; simpl in *; inversion Hab; try contradiction; try congruence; auto.
Qed.

Lemma γ_flatZ_join : forall (a b : flatZ), γ_flatZ a ∪ γ_flatZ b ⊆ γ_flatZ (a ∨ b).
Proof.
  intros a b m Hm.
  destruct Hm as [Ha | Hb]; destruct a; destruct b; simpl in *; try contradiction; try congruence; auto;
  destruct (n =? n0) eqn:Hnn0; simpl; auto.
  apply Z.eqb_eq in Hnn0. congruence.
Qed.

Lemma eqb_refl : forall (n : Z), n =? n = true.
Proof. intros n. lia. Qed.

Lemma γ_flatZ_meet : forall (a b : flatZ), γ_flatZ a ∩ γ_flatZ b ⊆ γ_flatZ (a ∧ b).
Proof.
  intros a b m Hm. simpl in *. destruct Hm as [Ha Hb].
  destruct a; destruct b; simpl in *; subst; try contradiction; try reflexivity;
  rewrite eqb_refl. reflexivity.
Qed.
     
Lemma γ_flatZ_bot : forall (n : Z), ~ n ∈ γ_flatZ bot.
Proof.
  intros n Hn. contradiction.
Qed.

Lemma γ_flatZ_top : forall (n : Z), n ∈ γ_flatZ top.
Proof.
  intros n. simpl. auto.
Qed.

Instance flatZConcretization : Concretization flatZ Z := {
  γ a := γ_flatZ a;
  
  γ_mon := γ_flatZ_mon;
  γ_join := γ_flatZ_join;
  γ_meet := γ_flatZ_meet;
  γ_bot := γ_flatZ_bot;
  γ_top := γ_flatZ_top;
}.

Definition aconst_flatZ (n : Z) : flatZ := Just n.

Definition aunop_flatZ (op: unop) (a : flatZ) : flatZ :=
  match op, a with
  | Oopp, Just n => Just (Z.opp n)
  | Oneg, Just n => Just (negz n)
  | _, _ => Top
  end.

Definition abinop_flatZ (op : binop) (a b : flatZ) : flatZ :=
  match op, a, b with
  | Oplus, Just n, Just m => Just (Z.add n m)
  | Oeq, Just n, Just m => Just (Z.b2z (n =? m))
  | Olt, Just n, Just m => Just (Z.b2z (n <? m))
  | Oand, Just n, Just m => Just (andz n m)
  | _, _, _ => Top
  end.

Definition alt_flatZ (a : flatZ) : flatZ := Top.

Definition age_flatZ (a : flatZ) : flatZ := Top.

Lemma γ_alt_flatZ : forall (m n : Z) (a : flatZ),
    m < n -> n ∈ γ a -> m ∈ γ (alt_flatZ a).
Proof. simpl. auto. Qed. 
  
Lemma γ_age_flatZ : forall (m n : Z) (a : flatZ),
    m >= n -> n ∈ γ a -> m ∈ γ (age_flatZ a).
Proof. simpl. auto. Qed.

Lemma γ_aconstr_flatZ : forall (n : Z), n ∈ γ_flatZ (aconst_flatZ n).
Proof.
  intros n. reflexivity.
Qed.

Lemma γ_aunop_flatZ : forall (n : Z) (a : flatZ) (op : unop),
  n ∈ γ_flatZ a -> eval_unop op n ∈ γ_flatZ (aunop_flatZ op a).
Proof.
  intros n a op Hn.
  destruct a; destruct op; simpl in *; try contradiction; try congruence.
Qed.

Lemma γ_abinop_flatZ : forall (m n : Z) (a b : flatZ) (op : binop),
  m ∈ γ_flatZ a -> n ∈ γ_flatZ b -> eval_binop op m n ∈ γ_flatZ (abinop_flatZ op a b).
Proof.
  intros m n a b op Hm Hn.
  destruct a; destruct b; destruct op; simpl in *; try contradiction; try congruence.
Qed.


Instance flatZAbsValue : AbsValue flatZ := {
  lat_val := flatZLatticeOp;
  γ_val := flatZConcretization;

  aconst := aconst_flatZ;
  aunop := aunop_flatZ;
  abinop := abinop_flatZ;

  alt := alt_flatZ;
  age := age_flatZ;

  γ_aconst := γ_aconstr_flatZ;
  γ_aunop := γ_aunop_flatZ;
  γ_abinop := γ_abinop_flatZ;

  γ_alt := γ_alt_flatZ;
  γ_age := γ_age_flatZ;
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

Definition ZInf_le (a b : ZInf) : bool :=
  match a, b with
  | _, Inf => true
  | Inf, _ => false
  | Fin n1, Fin n2 => n1 <=? n2
  end.

Definition ZInf_max (a b : ZInf) : ZInf :=
  match a, b with
  | Inf, _ => Inf
  | _, Inf => Inf
  | Fin n1, Fin n2 => Fin (Z.max n1 n2)
  end.

Definition ZInf_min (a b : ZInf) : ZInf :=
  match a, b with
  | Inf, x => x
  | x, Inf => x
  | Fin n1, Fin n2 => Fin (Z.min n1 n2)
  end.

Definition ZInf_add (a b : ZInf) : ZInf :=
  match a, b with
  | Inf, _ => Inf
  | _, Inf => Inf
  | Fin n, Fin m => Fin (n + m)
  end.

Definition Interval_point (i : Interval) : option Z :=
  match (low i), (high i) with
  | Inf, _ => None
  | _, Inf => None
  | Fin n, Fin m => if n =? m then Some n else None
  end.

Definition Interval_union (i1 i2 : Interval) : Interval :=
  {| low  := ZInf_max (low i1) (low i2);
     high := ZInf_max (high i1) (high i2);
  |}.

Definition Interval_subinterval (i1 i2 : Interval) : bool :=
  ZInf_le (low i1) (low i2) && ZInf_le (high i1) (high i2).

Definition Interval_intersects (i1 i2 : Interval) : bool :=
  (* start of i2 is inside i1 *)
  let c1 :=
    match low i1, low i2 with
    | Inf, Inf => true
    | Inf, Fin m => ZInf_le (Fin (-m)) (high i1)
    | Fin n, Inf => false
    | Fin n, Fin m => (m <=? n) && ZInf_le (Fin (-m)) (high i1)
    end
  (* start of i1 is inside i2 *)
  in let c2 :=
    match low i1, low i2 with
    | Inf, Inf => true
    | Inf, Fin m => false
    | Fin n, Inf => ZInf_le (Fin (-n)) (high i2)
    | Fin n, Fin m => (n <=? m) && ZInf_le (Fin (-n)) (high i2)
    end
  in c1 || c2.

Definition Interval_point_matched (i1 i2 : Interval) : bool :=
  match Interval_point i1, Interval_point i2 with
  | None, _ => false
  | _, None => false
  | Some n, Some m => n =? m
  end.

Definition Interval_truthy (i : Interval) : bool :=
  match Interval_point i with
  | Some n => negb (n =? 0)
  | None => true
  end.

Definition Interval_falsy (i : Interval) : bool :=
  let falsy_low :=
    match low i with
    | Inf => true
    | Fin n => n >=? 0
    end
  in let falsy_high :=
    match high i with
    | Inf => true
    | Fin n => n >=? 0
    end
  in falsy_low && falsy_high.

Definition Interval_intersection (i1 i2 : Interval) : Interval :=
  {| low := ZInf_min (low i1) (low i2);
     high := ZInf_min (high i1) (high i2);
  |}.

Instance IntervalLatticeOp : LatticeOp Interval := {
  ble := Interval_subinterval;
  join := Interval_union;
  meet := Interval_intersection;
  bot := {| low := -1; high := -1 |};
  top := {| low := Inf; high := Inf |};
}.

Definition γ_interval (i : Interval) : 𝒫 Z :=
  fun n =>
    let lowb :=
      match low i with
      | Inf     => True
      | Fin nl  => -nl <= n
      end in
    let highb :=
      match high i with
      | Inf     => True
      | Fin nh  => n <= nh
      end in
    lowb /\ highb.

Lemma γ_interval_mon : forall (a b : Interval), a ≤? b = true -> γ_interval a ⊆ γ_interval b.
Proof.
  intros a b Hab n Hn.
  unfold γ_interval.
  destruct Hn as [Hlow Hhigh]; simpl in Hab;
  destruct (low a) eqn: Hlowa; destruct (low b) eqn:Hlowb; destruct (high a) eqn:Hhigha; destruct (high b) eqn:Hhighb;
  try split; simpl in *; auto;
  unfold Interval_subinterval in Hab; rewrite Hlowa in Hab; rewrite Hlowb in Hab; rewrite Hhigha in Hab; rewrite Hhighb in Hab;
  unfold ZInf_le in Hab; rewrite andb_true_iff in Hab; repeat rewrite Z.leb_le in Hab; destruct Hab as [Hblelow Hblehigh];
  lia.
Qed. 

Lemma γ_interval_join : forall (a b : Interval), γ_interval a ∪ γ_interval b ⊆ γ_interval (a ∨ b).
Proof.
  intros a b k Hk. unfold γ_interval in *. simpl. unfold ZInf_max.
  destruct (low a); destruct (high a); destruct (low b); destruct (high b); lia.
Qed.

Lemma γ_interval_meet : forall (a b : Interval), γ_interval a ∩ γ_interval b ⊆ γ_interval (a ∧ b).
Proof.
  intros a b k Hab. destruct Hab as [Ha Hb]. unfold γ_interval in *. simpl. unfold ZInf_min.
  destruct (low a); destruct (high a); destruct (low b); destruct (high b); lia.
Qed.

Lemma γ_interval_bot : forall (n : Z), ~ n ∈ γ_interval bot.
Proof.
  intros n. unfold γ_interval. simpl. lia.
Qed.

Lemma γ_interval_top : forall (n : Z), n ∈ γ_interval top.
Proof.
  intros n. unfold γ_interval. simpl. lia.
Qed.

Instance IntervalConcretization : Concretization Interval Z := {
  γ := γ_interval;

  γ_mon := γ_interval_mon;
  γ_join := γ_interval_join;
  γ_meet := γ_interval_meet;
  γ_bot := γ_interval_bot;
  γ_top := γ_interval_top;
}.

Definition aconst_interval (n : Z) : Interval := {|
  low := -n;
  high := n;
|}.

Definition aunop_interval (op: unop) (a : Interval) : Interval :=
  match op, a with
  | Oopp, i => {| low := (high i); high := (low i) |}
  | Oneg, i =>
      match low i, high i with
      | Inf, Inf => {| low := 0; high := 1 |}
      | Inf, Fin n => if n >=? 0 then {| low := 0; high := 1 |} else {| low := 0; high := 0 |}
      | Fin n, Inf => if n >=? 0 then {| low := 0; high := 1 |} else {| low := 0; high := 0 |}
      | Fin n, Fin m => if -n >? m then bot
                        else if (n =? 0) && (m =? 0) then {| low := 1; high := 1 |}
                        else if (n >=? 0) && (m >=? 0) then {| low := 0; high := 1 |}
                        else {| low := 0; high := 0 |}
      end
  end.

Definition abinop_interval (op : binop) (a b : Interval) : Interval :=
  match op with
  | Oplus => {| low := ZInf_add (low a) (low b); high := ZInf_add (high a) (high b); |}
  | Oeq => {| low := Z.b2z (Interval_point_matched a b); high := Z.b2z (Interval_intersects a b) |}
  | Olt =>
      {| 
        low := Z.b2z (
          match high a, low b with
          | Inf, _ => false
          | _, Inf => false
          | Fin n, Fin m => (-n) <? m
          end); 
        high := Z.b2z (
          match low a, high b with
          | Inf, _ => true
          | _, Inf => true
          | Fin n, Fin m => (-n) <? m
          end
        )
      |}
  | Oand => {| low := Z.b2z (negb (Interval_falsy a || Interval_falsy b)); high := Z.b2z (Interval_truthy a && Interval_truthy b)|}
  end.

Definition alt_interval (i : Interval) : Interval :=
  {| low := Inf; high := high i |}.

Definition age_interval (i : Interval) : Interval :=
  {| low := low i; high := Inf |}.

Lemma γ_aconstr_interval : forall (n : Z), n ∈ γ_interval (aconst_interval n).
Proof.
  intros n. unfold aconst_interval. unfold γ_interval. simpl. lia.
Qed.

Lemma γ_aunop_interval : forall (n : Z) (a : Interval) (op : unop),
  n ∈ γ_interval a -> eval_unop op n ∈ γ_interval (aunop_interval op a).
Proof.
  intros n a op. unfold γ_interval. destruct op; simpl; destruct (low a); destruct (high a); simpl;
  try lia; eauto.
  - intros H.
    destruct n; unfold negz;
    destruct (-n0 >? n1) eqn:H1; destruct (n0 =? 0) eqn:H2; destruct (n1 =? 0) eqn:H3;
    destruct (n0 >=? 0) eqn:H4; destruct (n1 >=? 0) eqn:H5; simpl; lia.
  - intros H.
    destruct n; unfold negz; destruct (n0 >=? 0) eqn:H1; simpl; lia.
  - intros H.
    destruct n; unfold negz; destruct (n0 >=? 0) eqn:H1; simpl; lia.
  - intros H.
    destruct n; unfold negz; simpl; lia.
Qed. 

Lemma γ_abinop_interval : forall (m n : Z) (a b : Interval) (op : binop),
  m ∈ γ_interval a -> n ∈ γ_interval b -> eval_binop op m n ∈ γ_interval (abinop_interval op a b).
Proof.
  intros m n a b op Hm Hn.
  unfold γ_interval in *. destruct op eqn:Hop; simpl.
  - unfold ZInf_add.
    destruct (low a) eqn:H1; destruct (low b) eqn:H2;
    destruct (high a) eqn:H3; destruct (high b) eqn:H4; lia.
  - unfold Z.b2z. unfold Interval_point_matched. unfold Interval_point.
    unfold Interval_intersects. unfold ZInf_le.
    destruct (low a) eqn:H1; destruct (low b) eqn:H2;
    destruct (high a) eqn:H3; destruct (high b) eqn:H4;
    destruct (m =? n) eqn:H5; try destruct (n1 <=? n0) eqn:H6; 
    try destruct (- n1 <=? n2) eqn:H7; try destruct (n0 <=? n1) eqn:H8;
    try destruct (- n0 <=? n3) eqn:H9; try destruct (n0 =? n2) eqn:H10;
    try destruct (n1 =? n3) eqn:H11; try destruct (n4 =? m0) eqn:H12;
    try destruct (n0 =? n1) eqn:H13;
    try destruct (-n0 <=? n2) eqn:H14;
    try destruct (-n0 <=? n1) eqn:H15;
    simpl;
    lia.
  - unfold Z.b2z.
    destruct (low a) eqn:H1; destruct (low b) eqn:H2;
    destruct (high a) eqn:H3; destruct (high b) eqn:H4; 
    destruct (m <? n) eqn:H5;
    try destruct (-n2 <? n1) eqn:H6;
    try destruct (-n0 <? n3) eqn:H7;
    try destruct (-n0 <? n2) eqn:H8;
    try destruct (-n0 <? n1) eqn:H9;
    try destruct (-n1 <? n0) eqn:H10;
    lia.
  - unfold Z.b2z. unfold Interval_falsy. unfold Interval_truthy. unfold andz.
    unfold Interval_point. unfold negb.
    destruct (low a) eqn:H1; destruct (low b) eqn:H2;
    destruct (high a) eqn:H3; destruct (high b) eqn:H4;
    destruct m eqn:Hmcase; destruct n eqn:Hncase;
    try destruct (n0 >=? 0) eqn:H5; simpl; try lia;
    try destruct (n2 >=? 0) eqn:H6; simpl; try lia;
    try destruct (n1 >=? 0) eqn:H7; simpl; try lia;
    try destruct (n3 >=? 0) eqn:H8; simpl; try lia;
    try destruct (n0 =? n2) eqn:H9; simpl; try lia;
    try destruct (n1 =? n3) eqn:H10; simpl; try lia;
    try destruct (n0 =? 0) eqn:H11; simpl; try lia;
    try destruct (n1 =? 0) eqn:H12; simpl; try lia;
    try destruct (n1 =? n2) eqn:H13; simpl; try lia;
    try destruct (n1 =? 0) eqn:H14; simpl; try lia;
    try destruct (n0 =? n1) eqn:H15; simpl; try lia;
    rewrite H11; simpl; lia.
Qed.

Lemma γ_alt_interval : forall (m n : Z) (a : Interval),
    m < n -> n ∈ γ a -> m ∈ γ (alt_interval a).
Proof.
  intros m n a Hlt Ha. simpl in *. unfold γ_interval in *.
  unfold alt_interval. simpl. split; auto.
  destruct (high a); try lia.
Qed.
  
Lemma γ_age_interval : forall (m n : Z) (a : Interval),
    m >= n -> n ∈ γ a -> m ∈ γ (age_interval a).
Proof.
  intros m n a Hlt Ha. simpl in *. unfold γ_interval in *.
  unfold alt_interval. simpl. split; auto.
  destruct (low a); try lia.
Qed.

Instance IntervalAbsValue : AbsValue Interval := {
  lat_val := IntervalLatticeOp;
  γ_val := IntervalConcretization;

  aconst := aconst_interval;
  aunop := aunop_interval;
  abinop := abinop_interval;

  alt := alt_interval;
  age := age_interval;

  γ_aconst := γ_aconstr_interval;
  γ_aunop := γ_aunop_interval;
  γ_abinop := γ_abinop_interval;
  
  γ_alt := γ_alt_interval;
  γ_age := γ_age_interval;
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
