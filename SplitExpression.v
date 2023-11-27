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
  | SEVar (x : Svar_name): CV.


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

(* Fixpoint nat2Z (n : nat) : Z :=
    match n with
    | O => 0
    | S N => (1 + (nat2Z N))
    end.

Example test : nat2Z 15%nat = 15.
Proof.
    unfold nat2Z.
    lia.
Qed. *)

Definition nat_add (a : nat) (b : nat) : nat :=
    Nat.iter a S b.

End Lang_WhileDS.


Module DntSem_WhileDS.
Import Lang_WhileDS
       Lang_WhileD
       DntSem_WhileD2 EDenote CDenote
       BWFix KTFix Sets_CPO Sets_CL.

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

Definition genSEConst (n : Z) : CV :=
    (SEConst n).

Definition genSEVar {NameX : Names} (x : var_name) : CV:=
    (SEVar (name2Sname x)).

Definition genSEVar_n {NameX : Names} (vcnt :nat) : CV :=
    SEVar (nat2Sname vcnt).

Definition genSECV {NameX : Names} (vcnt :nat) : Sexpr :=
    SEConstOrVar (SEVar (nat2Sname vcnt)).

Fixpoint expr2coml {NameX : Names}
    (e : expr)
    (RET : Svar_name)
    (vcnt : nat) :
    Scomlist :=
    (* [(SCAsgnVar RET (expr2coml_e e RET vcnt))] ++ (expr2coml_l e RET vcnt) *)
    match e with
    | EConst n =>
        [(SCAsgnVar RET (SEConstOrVar (genSEConst n)))]
    | EVar x =>
        [(SCAsgnVar RET (SEConstOrVar (genSEVar x)))]
    | EBinop op e1 e2 =>
        match e1, e2 with
        | EConst c1, EConst c2 =>
            [(SCAsgnVar RET (SEBinop op (SEConst c1) (SEConst c2)))]
        | EConst c, EVar v =>
            [(SCAsgnVar RET (SEBinop op (SEConst c) (genSEVar v)))]
        | EVar v, EConst c =>
            [(SCAsgnVar RET (SEBinop op (genSEVar v) (SEConst c)))]
        | EVar v1, EVar v2 =>
            [(SCAsgnVar RET (SEBinop op (genSEVar v1) (genSEVar v2)))]
        | EConst c, _ =>
            (expr2coml e2 (nat2Sname vcnt) (S vcnt)) 
            ++ [(SCAsgnVar RET (SEBinop op (SEConst c) (genSEVar_n vcnt)))]
        | EVar v, _ =>
            (expr2coml e2 (nat2Sname vcnt) (S vcnt)) 
            ++ [(SCAsgnVar RET (SEBinop op (genSEVar v) (genSEVar_n vcnt)))]        
        | _ , EConst c =>
            (expr2coml e1 (nat2Sname vcnt) (S vcnt)) 
            ++ [(SCAsgnVar RET (SEBinop op (genSEVar_n vcnt) (SEConst c)))]
        | _ , EVar v =>
            (expr2coml e1 (nat2Sname vcnt) (S vcnt)) 
            ++ [(SCAsgnVar RET (SEBinop op (genSEVar_n vcnt) (genSEVar v)))]
        | _, _ =>
            (expr2coml e1 (nat2Sname vcnt) (S vcnt)) 
            ++ (expr2coml e2 
                (nat2Sname (nat_add vcnt (length (expr2coml e1 (nat2Sname vcnt) (S vcnt))))) 
                (S (nat_add vcnt (length (expr2coml e1 (nat2Sname vcnt) (S vcnt)))))) 
            ++ [(SCAsgnVar RET (SEBinop op (genSEVar_n vcnt)
                        (genSEVar_n (nat_add vcnt (length (expr2coml e1 (nat2Sname vcnt) (S vcnt)))))))]
        end
    | EUnop op e =>
        []
    | EDeref e =>
        []
    | EAddrOf e =>
        []
    end.


Fixpoint expr2coml_e {NameX : Names}
    (e : expr)
    (RET : Svar_name)
    (vcnt : nat) :
    Sexpr := 
    match e with
    | EConst n =>
        SEConstOrVar (genSEConst n)
    | EVar x =>
        SEConstOrVar (genSEVar x)
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
            (SEBinop op (genSEConst c) (genSEVar_n vcnt))
        | _, _ =>
            SEConstOrVar (genSEConst 0)
        end
    | EUnop op e =>
        SEConstOrVar (genSEConst 0)
    | EDeref e =>
        SEConstOrVar (genSEConst 0)
    | EAddrOf e =>
        SEConstOrVar (genSEConst 0)
    end
with expr2coml_l {NameX : Names}
    (e : expr)
    (RET : Svar_name)
    (vcnt : nat) :
    Scomlist := 
    match e with
    | EConst n =>
        []
    | EVar x =>
        []
    | EBinop op e1 e2 =>
        match e1, e2 with
        | EConst c1, EConst c2 =>
            []
        | EConst c, EVar v =>
            []
        | EVar v, EConst c =>
            []
        | EVar v1, EVar v2 =>
            []
        | EConst c, _ =>
            (* expr2coml e2 (nat2Sname vcnt) (S vcnt) *)
            []
        | _, _ =>
            []
        end
    | EUnop op e =>
        []
    | EDeref e =>
        []
    | EAddrOf e =>
        []
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


End DntSem_WhileDS.