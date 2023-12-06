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
Require Import PL.EquivAndRefine.
Import Lang_While DntSem_While1 DntSem_While2.
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
  | SCAsgnDeref (cv1 cv2: CV): Scom 
  | SCIf (pre : Scomlist) (e: Sexpr) (l1 l2: Scomlist): Scom 
  | SCWhile (pre : Scomlist) (e: Sexpr) (body: Scomlist): Scom
with Scomlist : Type :=
  | nil 
  | cons (c : Scom) (l : Scomlist).

Notation "x :: l" := (cons x l).
Notation "[]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).


(* Check SCSkip :: nil : Scomlist.
Check [SCSkip, SCSkip] : Scomlist. *)

Definition nat_add (a : nat) (b : nat) : nat :=
    Nat.iter a S b.

Fixpoint length (l:Scomlist) : nat :=
    match l with
    | nil => O
    | h :: t => 
        match h with
        | SCIf pre e c1 c2 => (nat_add (nat_add (nat_add (length pre) (length c1)) (length c2)) (length t))
        | SCWhile pre e c => (nat_add (nat_add (length pre) (length c)) (length t))
        | _ => (S (length t))
        end
    end.

Fixpoint app (l1: Scomlist) (l2: Scomlist) : Scomlist :=
    match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
    end.

Notation "x ++ y" := (app x y).

End Lang_WhileDS.

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

(* 在if, while和短路求值的情形可能存在问题 *)

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


Import DntSem_WhileD1.
Import Lang_WhileD.
Import DntSem_WhileDS.
Import Lang_WhileDS.
Import CDenote.
Import EDenote.

Definition getval (s : state) (x : var_name): option val :=
    s.(mem) (s.(env) x).

(* 表达式拆分过程 *)
Class Names : Type :=
{
    name2Sname : var_name -> var_name;
    nat2Sname : nat -> var_name;
    name_trans : state -> state;
}.

Class NamesProperty {NameX : Names} : Prop :=
{
    trans_prop1 : forall (x : var_name) (y : var_name) , (x = y) <-> (name2Sname x = name2Sname y);
    trans_prop2 : forall (x : nat) (y : nat) , (x = y) <-> (nat2Sname x = nat2Sname y);
    trans_prop3 : forall (x : var_name) (y : nat) , name2Sname x <> nat2Sname y;
    trans_prop4 : forall (s : state), 
        (forall (x : var_name), s.(env) x = (name_trans s).(env) (name2Sname x))
        /\ (forall (a : int64), s.(mem) a = (name_trans s).(mem) a);
}.

Definition genSEVar {NameX : Names} (x : var_name) : CV:=
    SEVar (name2Sname x).

Definition genSEVar_n {NameX : Names} (vcnt :nat) : CV :=
    SEVar (nat2Sname vcnt).

Definition genSECV {NameX : Names} (vcnt :nat) : Sexpr :=
    SEConstOrVar (SEVar (nat2Sname vcnt)).


Definition ex2se {NameX : Names}
    (e : expr)
    (vcnt : nat) :
    Sexpr := 
    match e with
    | EConst n =>
        SEConstOrVar (SEConst n)
    | EVar x =>
        SEConstOrVar (genSEVar x)
    | EBinop op e1 e2 =>
        match op with
        | OAnd =>
            genSECV vcnt
        | OOr =>
            genSECV vcnt
        | _ =>
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
                SEBinop op (genSEVar_n vcnt) (genSEVar_n (S vcnt))
            end
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

Fixpoint ex2pre {NameX : Names}
    (e : expr)
    (vcnt : nat) :
    Scomlist := 
    match e with
    | EConst n =>
        []
    | EVar x =>
        []
    | EBinop op e1 e2 =>
    match op with
        | OAnd =>
            [(SCIf (ex2pre e1 (S vcnt)) 
                (ex2se e1 (S vcnt)) 
                ((ex2pre e2 (nat_add (S vcnt) (length (ex2pre e1 (S vcnt)))))
                ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e2 (nat_add (S vcnt) (length (ex2pre e1 (S vcnt))))))])
                [(SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S vcnt)))])]
        | OOr =>
            [(SCIf (ex2pre e1 (S vcnt)) 
                (ex2se e1 (S vcnt)) 
                [(SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S vcnt)))]
                ((ex2pre e2 (nat_add (S vcnt) (length (ex2pre e1 (S vcnt)))))
                ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e2 (nat_add (S vcnt) (length (ex2pre e1 (S vcnt))))))]))]
        | _ =>
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
                (ex2pre e2 (S vcnt)) 
                ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e2 (S vcnt)))]
            | EVar v, _ =>
                (ex2pre e2 (S vcnt)) 
                ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e2 (S vcnt)))]
            | _ , EConst c =>
                (ex2pre e1 (S vcnt)) 
                ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S vcnt)))]
            | _ , EVar v =>
                (ex2pre e1 (S vcnt)) 
                ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S vcnt)))]
            | _, _ =>
                (ex2pre e1 (S (S vcnt))) 
                ++ (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))
                ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S vcnt)))] 
                ++ [(SCAsgnVar (nat2Sname (S vcnt)) 
                    (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))))]
            end
        end
    | EUnop op e =>
        match e with
        | EConst c =>
            []
        | EVar v =>
            []
        | _ =>
            (ex2pre e (S vcnt)) 
            ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt)))]
        end
    | EDeref e =>
        match e with
        | EConst c =>
            []
        | EVar v =>
            []
        | _ =>
            (ex2pre e (S vcnt)) 
            ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt)))] 
        end
    | EAddrOf e =>
        match e with
        | EConst c =>
            []
        | EVar v =>
            []
        | _ =>
            (ex2pre e (S vcnt)) 
            ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt)))]
        end
    end.
    
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
        match op with
        | OAnd =>
            [(SCIf (expr2coml_l e1 (nat2Sname vcnt) (S vcnt)) (expr2coml_e e1 (nat2Sname vcnt) (S vcnt)) 
                (expr2coml e2 RET (nat_add (S vcnt) (length (expr2coml_l e1 (nat2Sname vcnt) (S vcnt)))))
                [(SCAsgnVar RET (genSECV vcnt))])]
        | OOr =>
            [(SCIf (expr2coml_l e1 (nat2Sname vcnt) (S vcnt)) (expr2coml_e e1 (nat2Sname vcnt) (S vcnt)) 
                [(SCAsgnVar RET (genSECV vcnt))]
                (expr2coml e2 RET (nat_add (S vcnt) (length (expr2coml_l e1 (nat2Sname vcnt) (S vcnt))))))]
        | _ =>
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
    end
with expr2coml_e {NameX : Names}
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
        match op with
        | OAnd =>
            SEConstOrVar (SEVar RET)
        | OOr =>
            SEConstOrVar (SEVar RET)
        | _ =>
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
    end
with expr2coml_l {NameX : Names}
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
    match op with
        | OAnd =>
            [(SCIf (expr2coml_l e1 (nat2Sname vcnt) (S vcnt)) (expr2coml_e e1 (nat2Sname vcnt) (S vcnt)) 
                (expr2coml e2 RET (nat_add (S vcnt) (length (expr2coml_l e1 (nat2Sname vcnt) (S vcnt)))))
                [(SCAsgnVar RET (genSECV vcnt))])]
        | OOr =>
            [(SCIf (expr2coml_l e1 (nat2Sname vcnt) (S vcnt)) (expr2coml_e e1 (nat2Sname vcnt) (S vcnt)) 
                [(SCAsgnVar RET (genSECV vcnt))]
                (expr2coml e2 RET (nat_add (S vcnt) (length (expr2coml_l e1 (nat2Sname vcnt) (S vcnt))))))]
        | _ =>
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

Fixpoint  com2comlist {NameX : Names}
    (c : com)
    (vcnt : nat):
    Scomlist :=
    match c with
    | CSkip =>
        []
    | CAsgnVar X e =>
        (expr2coml e (name2Sname X) vcnt)
    | CAsgnDeref e1 e2 =>
        match e1, e2 with
        | EConst c1, EConst c2 =>
            [(SCAsgnDeref (SEConst c1) (SEConst c2))]
        | EConst c, EVar v =>
            [(SCAsgnDeref (SEConst c) (genSEVar v))]
        | EVar v, EConst c =>
            [(SCAsgnDeref (genSEVar v) (SEConst c))]
        | EVar v1, EVar v2 =>
            [(SCAsgnDeref (genSEVar v1) (genSEVar v2))]
        | EConst c, _ =>
            (expr2coml e2 (nat2Sname vcnt) (S vcnt))
            ++ [(SCAsgnDeref (SEConst c) (genSEVar_n vcnt))]
        | EVar v, _ =>
            (expr2coml e2 (nat2Sname vcnt) (S vcnt))
            ++ [(SCAsgnDeref (genSEVar v) (genSEVar_n vcnt))]   
        | _ , EConst c =>
            (expr2coml e1 (nat2Sname vcnt) (S vcnt))
            ++ [(SCAsgnDeref (genSEVar_n vcnt) (SEConst c))]
        | _ , EVar v =>
            (expr2coml e1 (nat2Sname vcnt) (S vcnt))
            ++ [(SCAsgnDeref (genSEVar_n vcnt) (genSEVar v))] 
        | _, _ =>
            (expr2coml e1 (nat2Sname vcnt) (S vcnt)) 
            ++ (expr2coml e2 
                (nat2Sname (nat_add (S vcnt) (length (expr2coml e1 (nat2Sname vcnt) (S vcnt))))) 
                (S (nat_add (S vcnt) (length (expr2coml e1 (nat2Sname vcnt) (S vcnt)))))) 
            ++ [(SCAsgnDeref (genSEVar_n vcnt)
                        (genSEVar_n (nat_add (S vcnt) (length (expr2coml e1 (nat2Sname vcnt) (S vcnt))))))]
        end
    | CSeq c1 c2 =>
        (com2comlist c1 vcnt) ++ (com2comlist c2 (nat_add vcnt (length (com2comlist c1 vcnt))))
    | CIf e c1 c2 =>
        [(SCIf (expr2coml_l e (nat2Sname vcnt) (S vcnt)) 
            (expr2coml_e e (nat2Sname vcnt) (S vcnt)) 
            (com2comlist c1 (nat_add (S vcnt) (length (expr2coml_l e (nat2Sname vcnt) (S vcnt))))) 
            (com2comlist c2 (nat_add (nat_add (S vcnt) (length (expr2coml_l e (nat2Sname vcnt) (S vcnt))))
                (length (com2comlist c1 (nat_add (S vcnt) (length (expr2coml_l e (nat2Sname vcnt) (S vcnt)))))))))]
    | CWhile e c =>
        [(SCWhile (expr2coml_l e (nat2Sname vcnt) (S vcnt)) 
        (expr2coml_e e (nat2Sname vcnt) (S vcnt)) 
        (com2comlist c (nat_add (S vcnt) (length (expr2coml_l e (nat2Sname vcnt) (S vcnt))))))]
    end.


(* 定义精化关系 *)

Lemma name_trans_prop_env {NameX : Names} {NPX : NamesProperty} :
    forall (s1 s2: state) (x : var_name), 
    name_trans s1 = s2 ->
    s2.(env) (name2Sname x) = s1.(env) x.
Proof.
    intros.
    pose proof trans_prop4 s1.
    destruct H0.
    pose proof H0 x.
    rewrite H2.
    rewrite H.
    tauto.
Qed.

Lemma name_trans_prop_mem {NameX : Names} {NPX : NamesProperty} :
    forall (s1 s2: state) (a : int64), 
    name_trans s1 = s2 ->
    s2.(mem) a = s1.(mem) a.
Proof.
    intros.
    pose proof trans_prop4 s1.
    destruct H0.
    pose proof H1 a.
    rewrite H2.
    rewrite H.
    tauto.
Qed.

Lemma expr2coml_l_deref {NameX : Names}:
    forall (e : expr) (RET : var_name) (vcnt : nat), 
    (expr2coml_l (EDeref e) RET vcnt) = (expr2coml e (nat2Sname vcnt) (S vcnt)).
Proof.
    intros.
    unfold expr2coml_l, expr2coml.
    simpl.
    reflexivity.
Qed.




Definition Serefine_nrm_l {NameX : Names} (cl : Scomlist) (se : Sexpr) (e : expr): Prop :=
    forall (s1 s2 : state) (x : var_name),

        (Seval_comlist cl).(nrm) (name_trans s1) s2 ->
        (Seval_l se).(nrm) s2 ⊆ ((eval_l e).(nrm) ∪ ((eval_l e).(err) × int64)) s1.

Print expr.

Lemma Split_Serefine_nrm_l {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr) (RET : var_name) (vcnt : nat), 
    Serefine_nrm_l (expr2coml_l e RET vcnt) (expr2coml_e e RET vcnt) e.
Proof.
    unfold Serefine_nrm_l.
    induction e.
    + intros.
      simpl.
      sets_unfold.
      right.
      tauto.
    + intros.
      simpl.
      unfold Seval_comlist, expr2coml_l, skip_sem, CDenote.nrm in H.
      sets_unfold in H.
      pose proof name_trans_prop_env s1 s2 x H.
      rewrite H0.
      sets_unfold.
      intros.
      left.
      tauto.
    + intros; sets_unfold; intros; simpl; sets_unfold; tauto.
    + intros; sets_unfold; intros; simpl; sets_unfold; tauto.
    + intros.
      simpl.
      sets_unfold.
      intros a.
      destruct e; simpl; intros.
      - tauto.
      - left.
        unfold Seval_comlist, expr2coml_l, skip_sem, CDenote.nrm in H.
        sets_unfold in H.
        pose proof name_trans_prop_env s1 s2 x0 H.
        unfold deref_sem_nrm.
        unfold deref_sem_nrm in H0; destruct H0.
        exists x1.
        pose proof name_trans_prop_mem s1 s2 x1 H.
        rewrite <- H1.
        rewrite <- H2.
        tauto.
      - unfold deref_sem_nrm in H0.
        destruct H0.
        destruct H0.
        admit. (* 这里需要用到：从name_tran s1 到 s2，程序状态如何变化 *)
      - admit.
      - admit.
      - admit.
    + intros; sets_unfold; intros; simpl; sets_unfold; tauto.
Admitted.



Record Serefine {NameX : Names} (cl : Scomlist) (se : Sexpr) (e : expr): Prop := {
    nrm_Serefine:
    forall (s1 s2 : state) (x : var_name),
        (Seval_comlist cl).(nrm) (name_trans s1) s2 ->
        (((Seval_l se).(nrm) s2 ⊆ ((eval_l e).(nrm) ∪ ((eval_l e).(err) × int64)) s1)
        /\ ((Seval_r se).(nrm) s2 ⊆ ((eval_r e).(nrm) ∪ ((eval_r e).(err) × int64)) s1));
    err_Serefine:
        (Seval_comlist cl).(err) ⊆ (eval_l e).(err) /\
        (Seval_comlist cl).(err) ⊆ (eval_r e).(err) /\
        (forall (s1 s2 : state), (Seval_comlist cl).(nrm) (name_trans s1) s2 ->
            (Seval_l se).(err) s2 ⊆ ((eval_l e).(err) s1
            /\ (Seval_r se).(err) s2 ⊆ ((eval_r e).(err) s1)));
    }.

(* 证明精化关系 *)
Theorem Split_expr_erefine {NameX : Names} {NPX : NamesProperty}: 
    forall (e : expr) (RET : var_name) (vcnt: nat), 
    Serefine (expr2coml_l e RET vcnt) (expr2coml_e e RET vcnt) e.
Proof.
    intros.
    split.
    + induction e; sets_unfold.
      - simpl; split; intros.
        -- right.
           tauto.
        -- intros.
           left.
           tauto.
      - simpl; split;
        intros; unfold expr2coml_l, Seval_comlist in H;
        unfold skip_sem in H;
        unfold CDenote.nrm in H;
        sets_unfold in H.
        --  left.
            pose proof name_trans_prop_env s1 s2 x H.
            rewrite <- H0.
            rewrite <- H1.
            tauto.
        --  left.
            unfold deref_sem_nrm.
            unfold deref_sem_nrm in H0.
            destruct H0.
            destruct H0.
            exists x1.
            split.
            pose proof name_trans_prop_env s1 s2 x H.
            rewrite <- H2.
            apply H0.
            pose proof name_trans_prop_mem s1 s2 x1 H.
            rewrite <- H2.
            apply H1.
      - split.
        --  intros.
            simpl.
            sets_unfold.
            tauto.
        --  intros. 
            simpl.
            admit.
      - split.
        --  intros.
            simpl.
            sets_unfold.
            tauto.
        --  intros.
            left.
            simpl.
            unfold Seval_r in H0.
            unfold expr2coml_e in H0.
            induction e.
            --- unfold Seval_r_cv in H0.
                simpl.
                destruct op.
                * simpl.
                  unfold not_sem_nrm.
                  unfold unop_sem, not_sem, not_sem_nrm, const_sem, EDenote.nrm in H0.
                  destruct H0.
                  exists x0.
                  tauto.
                * simpl.
                  unfold neg_sem_nrm.
                  unfold unop_sem, neg_sem, neg_sem_nrm, const_sem, EDenote.nrm in H0.
                  destruct H0.
                  exists x0.
                  tauto.
            --- unfold genSEVar, Seval_r_cv in H0.
                simpl.
                destruct op.
                * simpl.
                  unfold not_sem_nrm.
                  unfold unop_sem, not_sem, not_sem_nrm, var_sem_r, EDenote.nrm in H0.
                  destruct H0.
                  exists x0.
                  tauto.
                * simpl.
                  unfold neg_sem_nrm.
                  unfold unop_sem, neg_sem, neg_sem_nrm, var_sem_r, EDenote.nrm in H0.
                  destruct H0.
                  exists x0.
                  tauto.


               


Qed.



Record Screfine (cl : Scomlist) (c : com): Prop := {
    nrm_crefine:
        (Seval_comlist cl).(nrm) ⊆ (eval_com c).(nrm) ∪ ((eval_com c).(err) × state);
    err_crefine:
        (Seval_comlist cl).(err) ⊆ (eval_com c).(err);
}.