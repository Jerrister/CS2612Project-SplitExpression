Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.Classical_Prop.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import compcert.lib.Integers.
Require Import PL.SyntaxInCoq.
Require Import PL.DenotationalSemantics. Import BWFix Sets_CPO.
Require Import PL.PracticalDenotations. Import KTFix Sets_CL.
Import Lang_While DntSem_While1 DntSem_While2.
Import EDenote CDenote.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

Module Lang_WhileDS.
Import Lang_WhileD.

(* 重新定义Binop, Uniop 和 Comp? *)
Print var_name.
Print string.

Definition Svar_name : Type := nat.

Inductive CV : Type :=
  | SEConst (n : Z): CV
  | SEvar (x : Svar_name): CV.


Inductive Sexpr : Type :=
  | SEConstOrVar (cv: CV): Sexpr
  | SEBinop (op: binop) (cv1 cv2: CV): Sexpr
  | SEUnop (op: unop) (cv: CV): Sexpr
  | SEDeref (cv: CV): Sexpr
  | SEAddrOf (cv: CV): Sexpr.

(** 程序语句的语法树不变。*)

Inductive Scom : Type :=
  | SCSkip: Scom
  | SCAsgnVar (x: Svar_name) (e: Sexpr): Scom
  | SCAsgnDeref (cv1 cv2: CV): Scom (* CAsgnDeref (cv1 cv2: CV) (offset: EConst): com *)
  | SCIf (e: Sexpr) (l1 l2: Scomlist): Scom (* condition 需要时怎么样的形式？ *)
  | SCWhile (pre : Scomlist) (e: Sexpr) (body: Scomlist): Scom
with Scomlist : Type :=
  | nil 
  | cons (c : Scom) (l : Scomlist).

Notation "x :: l" := (cons x l).
Notation "[]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).


Check SCSkip :: nil : Scomlist.
Check [SCSkip, SCSkip] : Scomlist.

Fixpoint length (l:Scomlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1: Scomlist) (l2: Scomlist) : Scomlist :=
    match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
    end.

Notation "x ++ y" := (app x y).



End Lang_WhileDS.


Module DntSem_WhileD_Split.
Import Lang_WhileDS
       Lang_WhileD
       DntSem_WhileD2 EDenote CDenote
       BWFix KTFix Sets_CPO Sets_CL.

Definition genSEConst (n : Z) : Sexpr :=
    (SEConstOrVar (SEConst n)).

Class Names : Type :=
{
    name2Sname : var_name -> Svar_name;
    nat2Sname : nat -> Svar_name
}.

Class NamesProperty1 {NameX : Names} : Prop :=
{
    trans_prop1 : forall (x : var_name) (y : var_name) , (x = y) <-> (name2Sname x = name2Sname y);
    trans_prop2 : forall (x : nat) (y : nat) , (x = y) <-> (nat2Sname x = nat2Sname y);
    trans_prop3 : forall (x : var_name) (y : nat) , name2Sname x <> nat2Sname y
}.

Lemma name_trans_prop1 {NameX: Names} {NPX : NamesProperty1}:
    forall (x : var_name) (y : var_name) , (x = y) <-> (name2Sname x = name2Sname y).
Proof.
    intros.
    pose proof trans_prop1 x y.
    tauto.
Qed.

Lemma name_trans_prop2 {NameX: Names} {NPX : NamesProperty1}:
    forall (x : nat) (y : nat) , (x = y) <-> (nat2Sname x = nat2Sname y).
Proof.
    intros.
    pose proof trans_prop2 x y.
    tauto.
Qed.

Lemma name_trans_prop3 {NameX: Names} {NPX : NamesProperty1}:
    forall (x : var_name) (y : nat) , (name2Sname x <> nat2Sname y).
Proof.
    intros.
    pose proof trans_prop3 x y.
    tauto.
Qed.

Definition genSEVar {NameX : Names} (x : var_name) : Sexpr:=
    (SEConstOrVar (SEvar (name2Sname x))).

Fixpoint expr2coml
    (e : expr)
    (RET : Svar_name) :
    Scomlist :=
    match e with
    | EConst n =>
        [(SCAsgnVar RET (genSEConst n))]
    | EVar x =>
        [(SCAsgnVar RET (genSEVar x))]
    | EBinop op e1 e2 =>
    (* append s_e(e1) s_e(e2) (ret = r1 + r2) *)
        match e1, e2 with
        | EConst c1, EConst c2 =>
            [(SCAsgnVar RET (SEBinop op (genSEConst c1) (genSEConst c2)))]
        | EConst c, EVar v =>
            [(SCAsgnVar RET (SEBinop op (genSEConst c) (genSEVar v)))]
        | EVar v, EConst c =>
            [(SCAsgnVar RET (SEBinop op (genSEVar v) (genSEConst c)))]
        | EVar v1, EVar v2 =>
            [(SCAsgnVar RET (SEBinop op (genSEVar v1) (genSEVar v2)))]
        | EConst c, _ =>
            [(SCAsgnVar x0 (SEBinop op (genSEConst c) (genSEConst c2)))]
        | _, _ =>
            CAsgnVar X e
        end
    | EUnop op e =>
        []
    | EDeref e =>
        []
    | EAddrOf e =>
        []
    end.
with expr2coml_e
    (e : expr)
    (RET : var_name) :
    Sexpr := 
    match e with
    | EConst n =>
        (genSEConst n)
    | EVar x =>
        (genSEVar x)
    | EBinop op e1 e2 =>
        match e1, e2 with
        | EConst c1, EConst c2 =>
            (SEBinop op (genSEConst c1) (genSEConst c2))
        | EConst c, EVar v =>
            (SEBinop op (genSEConst c) (genSEVar v))
        | EVar v, EConst c =>
            (SEBinop op (genSEVar v) (genSEConst c))
        | EVar v1, EVar v2 =>
            (SEBinop op (genSEVar v1) (genSEVar v2))
        | EConst c, _ =>
            cons (SCAsgnVar x0 (SEBinop op (genSEConst c1) (genSEConst c2)))
        | _, _ =>
            CAsgnVar X e
        end
    | EUnop op e =>
        nil
    | EDeref e =>
        nil
    | EAddrOf e =>
        nil
    end.

(* Fixpoint split_expression_AsgnVar 
    (X : var_name)
    (e : expr) :
    com := 
    match e with
    | EConst n =>
        CAsgnVar X e
    | EVar x =>
        CAsgnVar X e
    | EBinop op e1 e2 =>
        match e1, e2 with
        | EConst c1, EConst c2 =>
            CAsgnVar X e
        | EConst c, EVar v =>
            CAsgnVar X e
        | EVar v, EConst c =>
            CAsgnVar X e
        | EVar v1, EVar v2 =>
            CAsgnVar X e
        | EConst c, _ =>
            CSeq (split_expression_AsgnVar (X1: var_name) e2) (CAsgnVar X (EBinop op e1 X1))
        | _, _ =>
            CAsgnVar X e
        end
    | EUnop op e =>
        CSkip
    | EDeref e =>
        CSkip
    | EAddrOf e =>
        CSkip
    end.

Definition split_expression_AsgnDeref 
    (e1 : expr)
    (e2 : expr) :
    com := 
    CSkip.

Definition split_expression_If
    (e : expr)
    (c1 : com)
    (c2 : com) :
    com :=
        CSkip
    .

Definition split_expression_While 
    (e : expr)
    (c : com) :
    com := 
    CSkip.




    
Fixpoint split_expression
    (e : expr) :
    com :=
    match c with
    | CSkip =>
        CSkip
    | CAsgnVar X e =>
        split_expression_AsgnVar X e 
    | CAsgnDeref e1 e2 =>
        split_expression_AsgnDeref e1 e2
    | CSeq c1 c2 =>
        CSeq (split_expression c1) (split_expression c2)
    | CIf e c1 c2 =>
        split_expression_If e c1 c2
    | CWhile e c =>
        split_expression_While e c
    end.

Theorem split_expression_refine :
    forall c : com,
    [[ (split_expression c) ]] ⊆ [[ c ]].
Admitted. *)


End DntSem_WhileD_Split.