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

(* 拆分后的语法 *)
Inductive CV : Type :=
  | SEConst (n : Z): CV
  | SEVar (x : var_name): CV.


Inductive Sexpr : Type :=
  | SEConstOrVar (cv: CV): Sexpr
  | SEBinop (op: binop) (cv1 cv2: CV): Sexpr
  | SEUnop (op: unop) (cv: CV): Sexpr
  | SEDeref (cv: CV): Sexpr
  | SEAddrOf (cv: CV): Sexpr.

Inductive Scom : Type :=
  | SCSkip: Scom
  | SCAsgnVar (x: var_name) (e: Sexpr): Scom
  | SCAsgnDeref (cv1 cv2: CV): Scom (* CAsgnDeref (cv1 cv2: CV) (offset: EConst): com *)
  | SCIf (pre : Scomlist) (e: Sexpr) (l1 l2: Scomlist): Scom (* condition 需要时怎么样的形式？ *)
  | SCWhile (pre : Scomlist) (e: Sexpr) (body: Scomlist): Scom
with Scomlist : Type :=
  | nil 
  | cons (c : Scom) (l : Scomlist).

Notation "x :: l" := (cons x l).
Notation "[]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).


(* Check SCSkip :: nil : Scomlist.
Check [SCSkip, SCSkip] : Scomlist. *)

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

Definition nat_add (a : nat) (b : nat) : nat :=
    Nat.iter a S b.

Module DntSem_WhileDS.
Import Lang_WhileDS
       Lang_WhileD
       DntSem_WhileD1
       EDenote.

(* 拆分后的语义 *)
Definition Seval_r_cv (cv: CV): EDenote :=
    match cv with
    | SEConst n =>
      const_sem n
    | SEVar X =>
      var_sem_r X
    end.

Definition Seval_l_cv (cv: CV): EDenote :=
    match cv with
    | SEConst n =>
        {| nrm := ∅; err := Sets.full; |}
    | SEVar X =>
        var_sem_l X
    end.

Definition Seval_r (e: Sexpr): EDenote :=
    match e with
    | SEConstOrVar cv =>
        Seval_r_cv cv
    | SEBinop op cv1 cv2 =>
        binop_sem op (Seval_r_cv cv1) (Seval_r_cv cv2)
    | SEUnop op cv1 =>
        unop_sem op (Seval_r_cv cv1)
    | SEDeref cv1 =>
        deref_sem_r (Seval_r_cv cv1)
    | SEAddrOf cv1 =>
        Seval_l_cv cv1
    end.

Definition Seval_l (e: Sexpr): EDenote :=
    match e with
    | SEConstOrVar (SEVar X) =>
        var_sem_l X
    | SEDeref cv =>
        Seval_r_cv cv
    | _ =>
        {| nrm := ∅; err := Sets.full; |}
    end.

Import CDenote.

Fixpoint Seval_com (c: Scom): CDenote :=
    match c with
    | SCSkip =>
        skip_sem
    | SCAsgnVar X e =>
        asgn_var_sem X (Seval_r e)
    | SCAsgnDeref cv1 cv2 =>
        asgn_deref_sem (Seval_r_cv cv1) (Seval_r_cv cv2)
    | SCIf pre e cl1 cl2 =>
        seq_sem (Seval_comlist pre) (if_sem (Seval_r e) (Seval_comlist cl1) (Seval_comlist cl2))
    | SCWhile pre e body =>
        seq_sem (Seval_comlist pre) (while_sem (Seval_r e) (Seval_comlist body))
    end
with Seval_comlist (cl : Scomlist) : CDenote :=
    match cl with
    | [] => skip_sem
    | c :: l => seq_sem (Seval_com c) (Seval_comlist l)
    end.

End DntSem_WhileDS.

Import DntSem_WhileDS.
Import DntSem_WhileD1.
Import Lang_WhileDS.
Import Lang_WhileD.


(* 表达式拆分过程 *)
Class Names : Type :=
{
    name2Sname : var_name -> var_name;
    nat2Sname : nat -> var_name
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



Definition genSEVar {NameX : Names} (x : var_name) : CV:=
    SEVar (name2Sname x).

Definition genSEVar_n {NameX : Names} (vcnt :nat) : CV :=
    SEVar (nat2Sname vcnt).

Definition genSECV {NameX : Names} (vcnt :nat) : Sexpr :=
    SEConstOrVar (SEVar (nat2Sname vcnt)).


(* 注意：暂时没有考虑短路求值 *)

Fixpoint expr2coml {NameX : Names}
    (e : expr)
    (RET : var_name)
    (vcnt : nat) :
    Scomlist :=
    match e with
    | EConst n =>
        [(SCAsgnVar RET (SEConstOrVar (SEConst n)))]
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
                (nat2Sname (nat_add (S vcnt) (length (expr2coml e1 (nat2Sname vcnt) (S vcnt))))) 
                (S (nat_add (S vcnt) (length (expr2coml e1 (nat2Sname vcnt) (S vcnt)))))) 
            ++ [(SCAsgnVar RET (SEBinop op (genSEVar_n vcnt)
                        (genSEVar_n (nat_add (S vcnt) (length (expr2coml e1 (nat2Sname vcnt) (S vcnt)))))))]
        end
    | EUnop op e =>
        match e with
        | EConst c =>
            [(SCAsgnVar RET (SEUnop op (SEConst c)))]
        | EVar v =>
            [(SCAsgnVar RET (SEUnop op (genSEVar v)))]
        | _ =>
            (expr2coml e (nat2Sname vcnt) (S vcnt)) 
            ++ [(SCAsgnVar RET (SEUnop op (genSEVar_n vcnt)))]
        end
    | EDeref e =>
        match e with
        | EConst c =>
            [(SCAsgnVar RET (SEDeref (SEConst c)))]
        | EVar v =>
            [(SCAsgnVar RET (SEDeref (genSEVar v)))]
        | _ =>
            (expr2coml e (nat2Sname vcnt) (S vcnt)) 
            ++ [(SCAsgnVar RET (SEDeref (genSEVar_n vcnt)))]
        end
    | EAddrOf e =>
        match e with
        | EConst c =>
            [(SCAsgnVar RET (SEAddrOf (SEConst c)))]
        | EVar v =>
            [(SCAsgnVar RET (SEAddrOf (genSEVar v)))]
        | _ =>
            (expr2coml e (nat2Sname vcnt) (S vcnt)) 
            ++ [(SCAsgnVar RET (SEAddrOf (genSEVar_n vcnt)))]
        end
    end.


Definition expr2coml_e {NameX : Names}
    (e : expr)
    (RET : var_name)
    (vcnt : nat) :
    Sexpr := 
    match e with
    | EConst n =>
        SEConstOrVar (SEConst n)
    | EVar x =>
        SEConstOrVar (genSEVar x)
    | EBinop op e1 e2 =>
        match e1, e2 with
        | EConst c1, EConst c2 =>
            SEBinop op (SEConst c1) (SEConst c2)
        | EConst c, EVar v =>
            SEBinop op (SEConst c) (genSEVar v)
        | EVar v, EConst c =>
            SEBinop op (genSEVar v) (SEConst c)
        | EVar v1, EVar v2 =>
            SEBinop op (genSEVar v1) (genSEVar v2)
        | EConst c, _ =>
            SEBinop op (SEConst c) (genSEVar_n vcnt)
        | EVar v, _ =>
            SEBinop op (genSEVar v) (genSEVar_n vcnt)   
        | _ , EConst c =>
            SEBinop op (genSEVar_n vcnt) (SEConst c)
        | _ , EVar v =>
            SEBinop op (genSEVar_n vcnt) (genSEVar v)
        | _, _ =>
            SEBinop op (genSEVar_n vcnt)
            (genSEVar_n (nat_add (S vcnt) (length (expr2coml e1 (nat2Sname vcnt) (S vcnt)))))
        end
    | EUnop op e =>
        match e with
        | EConst c =>
            SEUnop op (SEConst c)
        | EVar v =>
            SEUnop op (genSEVar v)
        | _ =>
            SEUnop op (genSEVar_n vcnt)
        end
    | EDeref e =>
        match e with
        | EConst c =>
            SEDeref (SEConst c)
        | EVar v =>
            SEDeref (genSEVar v)
        | _ =>
            SEDeref (genSEVar_n vcnt)
        end
    | EAddrOf e =>
        match e with
        | EConst c =>
            SEAddrOf (SEConst c)
        | EVar v =>
            SEAddrOf (genSEVar v)
        | _ =>
            SEAddrOf (genSEVar_n vcnt)
        end
    end.

Definition expr2coml_l {NameX : Names}
    (e : expr)
    (RET : var_name)
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
            (expr2coml e2 (nat2Sname vcnt) (S vcnt)) 
        | EVar v, _ =>
            (expr2coml e2 (nat2Sname vcnt) (S vcnt))      
        | _ , EConst c =>
            (expr2coml e1 (nat2Sname vcnt) (S vcnt)) 
        | _ , EVar v =>
            (expr2coml e1 (nat2Sname vcnt) (S vcnt)) 
        | _, _ =>
            (expr2coml e1 (nat2Sname vcnt) (S vcnt)) 
            ++ (expr2coml e2 
                (nat2Sname (nat_add (S vcnt) (length (expr2coml e1 (nat2Sname vcnt) (S vcnt))))) 
                (S (nat_add (S vcnt) (length (expr2coml e1 (nat2Sname vcnt) (S vcnt)))))) 
        end
    | EUnop op e =>
        match e with
        | EConst c =>
            []
        | EVar v =>
            []
        | _ =>
            (expr2coml e (nat2Sname vcnt) (S vcnt)) 
        end
    | EDeref e =>
        match e with
        | EConst c =>
            []
        | EVar v =>
            []
        | _ =>
            (expr2coml e (nat2Sname vcnt) (S vcnt)) 
        end
    | EAddrOf e =>
        match e with
        | EConst c =>
            []
        | EVar v =>
            []
        | _ =>
            (expr2coml e (nat2Sname vcnt) (S vcnt)) 
        end
    end.

(* 程序语句经过表达式拆分变换 *)

Fixpoint com2comlist
    (c : Scom)
    (vcnt : nat):
    Scomlist :=
    []
with comlist2comlist
    (c : Scomlist)
    (vcnt : nat):
    Scomlist :=
    [].


(* 定义精化关系 *)

(* 证明精化关系 *)
