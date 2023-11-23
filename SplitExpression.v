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

Module DntSem_WhileD_Split.
Import Lang_While.
Import Lang_WhileD
       DntSem_WhileD2 EDenote CDenote
       BWFix KTFix Sets_CPO Sets_CL.

Print expr.

Definition add_var
    :
    var_name X

Fixpoint split_expression_AsgnVar 
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
    (c : com) :
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
Admitted.


End DntSem_WhileD_Split.