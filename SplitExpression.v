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
(* Require Import PL.EquivAndRefine. *)
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





(* Module EDenote.

Record EDenote: Type := {
  nrm: state -> int64 -> Prop;
  err: state -> Prop;
}.

End EDenote.

Import EDenote. *)

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
Notation "x '.(nrm)'" := (CDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (CDenote.err x)
  (at level 1, only printing).

Notation "x '.(inf)'" := (CDenote.inf x)
  (at level 1).
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

Notation "x '.(nrm)'" := (CDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (CDenote.err x)
  (at level 1, only printing).

Notation "x '.(inf)'" := (CDenote.inf x)
  (at level 1).

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
  
(* 程序语句经过表达式拆分变换 *)

Fixpoint  com2comlist {NameX : Names}
    (c : com)
    (vcnt : nat):
    Scomlist :=
    match c with
    | CSkip =>
        []
    | CAsgnVar X e =>
        (ex2pre e vcnt) 
        ++ [(SCAsgnVar (name2Sname X) (ex2se e vcnt))]
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
            (ex2pre e2 (S vcnt))
            ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e2 (S vcnt)))]
            ++ [(SCAsgnDeref (SEConst c) (genSEVar_n vcnt))]
        | EVar v, _ =>
            (ex2pre e2 (S vcnt))
            ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e2 (S vcnt)))]
            ++ [(SCAsgnDeref (genSEVar v) (genSEVar_n vcnt))]   
        | _ , EConst c =>
            (ex2pre e1 (S vcnt))
            ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S vcnt)))]
            ++ [(SCAsgnDeref (genSEVar_n vcnt) (SEConst c))]
        | _ , EVar v =>
            (ex2pre e1 (S vcnt))
            ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S vcnt)))]
            ++ [(SCAsgnDeref (genSEVar_n vcnt) (genSEVar v))] 
        | _, _ =>
            (ex2pre e1 (S (S vcnt)))
            ++ (ex2pre e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))
            ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt))))]
            ++ [(SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt)))))))]
            ++ [(SCAsgnDeref (genSEVar_n vcnt) (genSEVar_n (S vcnt)))]
        end
    | CSeq c1 c2 =>
        (com2comlist c1 vcnt) ++ (com2comlist c2 (nat_add vcnt (length (com2comlist c1 vcnt))))
    | CIf e c1 c2 =>
        [(SCIf (ex2pre e vcnt)
            (ex2se e vcnt)
            (com2comlist c1 (nat_add vcnt (length (ex2pre e vcnt)))) 
            (com2comlist c2 (nat_add (nat_add vcnt (length (ex2pre e vcnt)))
                (length (com2comlist c1 (nat_add vcnt (length (ex2pre e vcnt))))))))]
    | CWhile e c =>
        [(SCWhile (ex2pre e vcnt) 
        (ex2se e vcnt) 
        (com2comlist c (nat_add vcnt (length (ex2pre e vcnt)))))]
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

(* Lemma name_trans_prop_expr {NameX : Names} {NPX : NamesProperty}: 
    forall (esem : EDenote) (s1 s2 : state), 
    name_trans s1 = s2 ->
    esem.(nrm) s1 = esem.(nrm) s2.
Proof.
    intros.
    
    
Qed. *)


(* Lemma ex2pre_binop {NameX : Names}:
    forall (vcnt : nat) (e1 e2 : expr) (op : binop),
    match op with
        | OAnd =>
        ex2pre (EBinop op e1 e2) vcnt =
            [(SCIf (ex2pre e1 (S vcnt)) 
                (ex2se e1 (S vcnt)) 
                ((ex2pre e2 (nat_add (S vcnt) (length (ex2pre e1 (S vcnt)))))
                ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e2 (nat_add (S vcnt) (length (ex2pre e1 (S vcnt))))))])
                [(SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S vcnt)))])]
        | OOr =>
        ex2pre (EBinop op e1 e2) vcnt =
            [(SCIf (ex2pre e1 (S vcnt)) 
                (ex2se e1 (S vcnt)) 
                [(SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S vcnt)))]
                ((ex2pre e2 (nat_add (S vcnt) (length (ex2pre e1 (S vcnt)))))
                ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e2 (nat_add (S vcnt) (length (ex2pre e1 (S vcnt))))))]))]
        | _ =>
            match e1, e2 with
            | EConst c1, EConst c2 =>
            ex2pre (EBinop op e1 e2) vcnt = []
            | EConst c, EVar v =>
            ex2pre (EBinop op e1 e2) vcnt = []
            | EVar v, EConst c =>
            ex2pre (EBinop op e1 e2) vcnt = []
            | EVar v1, EVar v2 =>
            ex2pre (EBinop op e1 e2) vcnt = []
            | EConst c, _ =>
            ex2pre (EBinop op e1 e2) vcnt =
                (ex2pre e2 (S vcnt)) 
                ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e2 (S vcnt)))]
            | EVar v, _ =>
            ex2pre (EBinop op e1 e2) vcnt =
                (ex2pre e2 (S vcnt)) 
                ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e2 (S vcnt)))]
            | _ , EConst c =>
            ex2pre (EBinop op e1 e2) vcnt =
                (ex2pre e1 (S vcnt)) 
                ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S vcnt)))]
            | _ , EVar v =>
            ex2pre (EBinop op e1 e2) vcnt =
                (ex2pre e1 (S vcnt)) 
                ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S vcnt)))]
            | _, _ =>
            ex2pre (EBinop op e1 e2) vcnt =
                (ex2pre e1 (S (S vcnt))) 
                ++ (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))
                ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S vcnt)))] 
                ++ [(SCAsgnVar (nat2Sname (S vcnt)) 
                    (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))))]
            end
        end.
Proof.
    intros.
    destruct op, e1, e2; simpl; reflexivity.
Qed. *)

Lemma ex2pre_unop {NameX : Names}:
    forall (vcnt : nat) (op : unop) (e : expr),
    match e with 
    | EConst c => (ex2pre (EUnop op e) vcnt) = []
    | EVar x => (ex2pre (EUnop op e) vcnt) = []
    | _ =>
        (ex2pre (EUnop op e) vcnt) 
        = (ex2pre e (S vcnt)) 
        ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt)))]
    end.
Proof.
    intros.
    destruct op, e; simpl; reflexivity.
Qed.

Lemma ex2pre_deref {NameX : Names}:
    forall (vcnt : nat) (e : expr),
    match e with 
    | EConst c => (ex2pre (EDeref e) vcnt) = []
    | EVar x => (ex2pre (EDeref e) vcnt) = []
    | _ =>
        (ex2pre (EDeref e) vcnt) 
        = (ex2pre e (S vcnt)) 
        ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt)))]
    end.
Proof.
    intros.
    destruct e; simpl; reflexivity.
Qed.

Lemma ex2pre_addrof {NameX : Names}:
    forall (vcnt : nat) (e : expr),
    match e with 
    | EConst c => (ex2pre (EAddrOf e) vcnt) = []
    | EVar x => (ex2pre (EAddrOf e) vcnt) = []
    | _ =>
        (ex2pre (EAddrOf e) vcnt) 
        = (ex2pre e (S vcnt)) 
        ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt)))]
    end.
Proof.
    intros.
    destruct e; simpl; reflexivity.
Qed.


Lemma eval_comlist_seq : forall (cl1 cl2 : Scomlist) (s1 s2 : state),
    (Seval_comlist (cl1 ++ cl2)).(nrm) s1 s2 
    <-> Rels.concat (Seval_comlist cl1).(nrm) (Seval_comlist cl2).(nrm) s1 s2.
Proof.
    induction cl1; intros.
    + simpl.
      sets_unfold.
      split; intros.
      - exists s1; tauto.
      - destruct H.
        destruct H.
        rewrite H.
        tauto.
    + simpl.
      sets_unfold.
      split; intros.
      - destruct H.
        destruct H.
        pose proof IHcl1 cl2 x s2.
        destruct H1.
        pose proof H1 H0.
        sets_unfold in H3.
        destruct H3.
        exists x0.
        split.
        exists x.
        tauto.
        tauto.
      - destruct H.
        destruct H.
        destruct H.
        exists x0.
        pose proof IHcl1 cl2 x0 s2.
        destruct H1.
        destruct H.
        sets_unfold in H2.
        assert (exists i : state,
        (Seval_comlist cl1).(nrm) x0 i /\
        (Seval_comlist cl2).(nrm) i s2).
        {
            exists x.
            tauto.
        }
        pose proof H2 H4.
        tauto.
Qed.

Lemma midstate_deref {NameX : Names}: forall (s1 : state) (s3 : state) (e : expr) (vcnt : nat),
    (Seval_comlist (ex2pre (EDeref e) vcnt)).(nrm) s1 s3
    -> match e with
    | EConst c => True
    | EVar x => True
    | _ =>
    exists (s2 : state), 
    (Seval_comlist (ex2pre e (S vcnt))).(nrm) s1 s2
    /\ (Seval_comlist 
        [(SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt)))]).(nrm) s2 s3
    end.
Proof.
    intros.
    pose proof ex2pre_deref vcnt e.
    destruct e.
    + tauto. 
    + tauto.
    + rewrite H0 in H.
      pose proof eval_comlist_seq 
      (ex2pre (EBinop op e1 e2) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EBinop op e1 e2) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.
    + rewrite H0 in H.
      pose proof eval_comlist_seq 
      (ex2pre (EUnop op e) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EUnop op e) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.
    + rewrite H0 in H.
      pose proof eval_comlist_seq 
      (ex2pre (EDeref e) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EDeref e) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.
    + rewrite H0 in H.
      pose proof eval_comlist_seq 
      (ex2pre (EAddrOf e) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EAddrOf e) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.  
Qed.

Lemma midstate_addrof {NameX : Names}: forall (s1 : state) (s3 : state) (e : expr) (vcnt : nat),
    (Seval_comlist (ex2pre (EAddrOf e) vcnt)).(nrm) s1 s3
    -> match e with
    | EConst c => True
    | EVar x => True
    | _ =>
    exists (s2 : state), 
    (Seval_comlist (ex2pre e (S vcnt))).(nrm) s1 s2
    /\ (Seval_comlist 
        [(SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt)))]).(nrm) s2 s3
    end.
Proof.
    intros.
    pose proof ex2pre_addrof vcnt e.
    destruct e.
    + tauto. 
    + tauto.
    + rewrite H0 in H.
      pose proof eval_comlist_seq 
      (ex2pre (EBinop op e1 e2) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EBinop op e1 e2) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.
    + rewrite H0 in H.
      pose proof eval_comlist_seq 
      (ex2pre (EUnop op e) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EUnop op e) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.
    + rewrite H0 in H.
      pose proof eval_comlist_seq 
      (ex2pre (EDeref e) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EDeref e) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.
    + rewrite H0 in H.
      pose proof eval_comlist_seq 
      (ex2pre (EAddrOf e) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EAddrOf e) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.  
Qed.

Lemma midstate_unop {NameX : Names}: 
    forall (op : unop) 
    (e : expr) (vcnt : nat) (s1 : state) (s3 : state),
    (Seval_comlist (ex2pre (EUnop op e) vcnt)).(nrm) s1 s3
    -> match e with
    | EConst c => True
    | EVar x => True
    | _ =>
    exists (s2 : state), 
    (Seval_comlist (ex2pre e (S vcnt))).(nrm) s1 s2
    /\ (Seval_comlist 
        [(SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt)))]).(nrm) s2 s3
    end.
Proof.
    intros.
    pose proof ex2pre_unop vcnt op e.
    destruct e.
    + tauto. 
    + tauto.
    + rewrite H0 in H.
      pose proof eval_comlist_seq 
      (ex2pre (EBinop op0 e1 e2) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EBinop op0 e1 e2) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.
    + rewrite H0 in H.
      pose proof eval_comlist_seq 
      (ex2pre (EUnop op0 e) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EUnop op0 e) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.
    + rewrite H0 in H.
      pose proof eval_comlist_seq 
      (ex2pre (EDeref e) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EDeref e) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.
    + rewrite H0 in H.
      pose proof eval_comlist_seq 
      (ex2pre (EAddrOf e) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EAddrOf e) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.  
Qed.

Lemma ex2se_prop {NameX : Names}: 
    forall (e : expr) (vcnt : nat) (s1 s2 : state),
    match e with
    | EConst c => True
    | EVar x => True
    | _ => (Seval_comlist
        [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))]).(nrm) (name_trans s1) s2
        -> (Seval_r (ex2se e (S vcnt))).(nrm) s2 = (eval_r e).(nrm) s1
            \/ (eval_r e).(err) s1
    end.
(* Admitted. *)
Proof.
    simpl.
    sets_unfold.
    unfold asgn_deref_sem_nrm.
    (* unfold ex2se. *)
    induction e.
    + tauto.
    + tauto.
    + admit.
    + intros.
      destruct H.
      destruct H.
      destruct H.
      destruct H.
      rewrite H0 in H.
      destruct H.
      destruct H.
      destruct H1.
      destruct H1.
      destruct H2.
      destruct H3.
      pose proof H3 (nat2Sname vcnt).
      rewrite H5 in H2.
      destruct e.

      

    
Admitted.

Definition Serefine_nrm {NameX : Names} (cl : Scomlist) (se : Sexpr) (e : expr): Prop :=
    forall (s1 s2 : state),
        (Seval_comlist cl).(nrm) (name_trans s1) s2 ->
        (Seval_r se).(nrm) s2 ⊆ ((eval_r e).(nrm) ∪ ((eval_r e).(err) × int64)) s1
        /\ (Seval_l se).(nrm) s2 ⊆ ((eval_l e).(nrm) ∪ ((eval_l e).(err) × int64)) s1.

Definition Serefine_err {NameX : Names} (cl : Scomlist) (se : Sexpr) (e : expr): Prop :=
    forall (s1 s2 : state),
        ((Seval_comlist cl).(err) (name_trans s1)
        \/ ((Seval_comlist cl).(nrm) (name_trans s1) s2
            /\ ((Seval_l se).(err) s2) \/ (Seval_r se).(err) s2))
        -> ((eval_l e).(err) s1 \/ (eval_r e).(err) s1).

Record Serefine {NameX : Names} (cl : Scomlist) (se : Sexpr) (e : expr): Prop := {
    nrm_Serefine:
        Serefine_nrm cl se e;
    err_Serefine:
        Serefine_err cl se e;
    }.


Lemma Split_Serefine_nrm {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr) (vcnt : nat), 
    Serefine_nrm (ex2pre e vcnt) (ex2se e vcnt) e.
Proof.
    unfold Serefine_nrm.
    sets_unfold.
    induction e.
    + intros.
      simpl.
      split.
      - intros.
        tauto.
      - tauto.
    + intros.
      simpl.
      unfold Seval_comlist, ex2pre, skip_sem, CDenote.nrm in H.
      sets_unfold in H.
      split.
      - unfold deref_sem_nrm.
        intros.
        destruct H0.
        left.
        pose proof name_trans_prop_env s1 s2 x H.
        pose proof name_trans_prop_mem s1 s2 x0 H.
        exists x0.
        rewrite <- H1.
        rewrite <- H2.
        tauto.
      - intros.
        left.
        pose proof name_trans_prop_env s1 s2 x H.
        rewrite <- H1.
        tauto.
    + intros.

      split.
      - intros.
        admit.
      - intros.
        simpl.
        sets_unfold.
        tauto.
    + sets_unfold.
      intros vcnt.
      pose proof ex2pre_unop vcnt op e.
      pose proof midstate_unop op e vcnt as HM.
      destruct e; intros; split; simpl.
      - unfold unop_sem, const_sem, EDenote.nrm.
        destruct op; simpl.
        --  unfold not_sem_nrm.
            intros.
            left.
            tauto.
        --  unfold neg_sem_nrm.
            intros.
            left.
            tauto.
      - sets_unfold.
        intros.
        tauto.
      - unfold unop_sem, var_sem_r, EDenote.nrm.
        destruct op; simpl; sets_unfold.
        --  unfold not_sem_nrm, deref_sem_nrm.
            left.
            destruct H1.
            destruct H1.
            destruct H1.
            destruct H1.
            rewrite H in H0.
            unfold Seval_comlist, CDenote.nrm, skip_sem in H0.
            sets_unfold in H0.
            exists x0.
            split.
            exists x1.
            split.
            pose proof name_trans_prop_env s1 s2 x H0.
            rewrite <- H1.
            rewrite <- H4.
            reflexivity.
            pose proof name_trans_prop_mem s1 s2 x1 H0.
            rewrite <- H4.
            rewrite H3.
            tauto.
            tauto.
        --  unfold neg_sem_nrm, deref_sem_nrm.
            left.
            destruct H1.
            destruct H1.
            destruct H1.
            destruct H1.
            rewrite H in H0.
            unfold Seval_comlist, CDenote.nrm, skip_sem in H0.
            sets_unfold in H0.
            exists x0.
            split.
            exists x1.
            split.
            pose proof name_trans_prop_env s1 s2 x H0.
            rewrite <- H1.
            rewrite <- H4.
            reflexivity.
            pose proof name_trans_prop_mem s1 s2 x1 H0.
            rewrite <- H4.
            rewrite H3.
            tauto.
            tauto.
      - sets_unfold.
        tauto.
      - intros.
        specialize (HM (name_trans s1) s2 H0).
        destruct HM.
        destruct H2.
        pose proof IHe (S vcnt) s1 x H2.
        destruct H4.
        unfold Seval_comlist, skip_sem, seq_sem, asgn_var_sem, 
        asgn_deref_sem, asgn_deref_sem_nrm, CDenote.nrm in H3.
        sets_unfold in H3.
        destruct H3.
        destruct H3.
        destruct H3.
        destruct H3.
        destruct H3.
        destruct H7.
        destruct H8.
        destruct H9.
        destruct H10.
        rewrite H6 in H11, H10, H9.

Admitted.

Lemma Split_Serefine_err {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr) (vcnt : nat), 
    Serefine_err (ex2pre e vcnt) (ex2se e vcnt) e.
Admitted.

Theorem Split_expr_erefine {NameX : Names} {NPX : NamesProperty}: 
    forall (e : expr) (vcnt: nat), 
    Serefine (ex2pre e vcnt) (ex2se e vcnt) e.
Proof.
    intros.
    split.
    apply Split_Serefine_nrm.
    apply Split_Serefine_err.
Qed.



(* 证明精化关系 *)
(* Theorem Split_expr_erefine {NameX : Names} {NPX : NamesProperty}: 
    forall (e : expr) (RET : var_name) (vcnt: nat), 
    Serefine (ex2pre e RET vcnt) (ex2se e RET vcnt) e.
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
        intros; unfold ex2pre, Seval_comlist in H;
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
            unfold ex2se in H0.
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
Admitted. *)

Definition Screfine_nrm {NameX : Names} (cl : Scomlist) (c : com): Prop :=
    forall (s1 s2 s3 : state),
        (Seval_comlist cl).(nrm) (name_trans s1) s3
        -> (eval_com c).(err) s1
            \/ ((eval_com c).(nrm) s1 s2 
                /\ (forall (x : var_name) (i : int64),
                    (s2.(env) x = i 
                        -> s3.(env) (name2Sname x) = i
                            /\ s2.(mem) i = s3.(mem) i))).

Definition Screfine_err {NameX : Names} (cl : Scomlist) (c : com): Prop :=
    forall (s1 : state),
        (Seval_comlist cl).(err) (name_trans s1) -> (eval_com c).(err) s1.

Definition Screfine_inf {NameX : Names} (cl : Scomlist) (c : com): Prop :=
    forall (s1 : state),
        (Seval_comlist cl).(inf) (name_trans s1) 
        -> (eval_com c).(inf) s1
            \/ (eval_com c).(err) s1.

Record Screfine {NameX : Names} (cl : Scomlist) (c : com): Prop := {
    nrm_crefine:
        Screfine_nrm cl c;
    err_crefine:
        Screfine_err cl c;
    inf_crefine:
        Screfine_inf cl c;
}.

Lemma Split_crefine_nrm {NameX : Names} {NPX : NamesProperty}: 
    forall (c : com) (vcnt : nat),
        Screfine_nrm (com2comlist c vcnt) c.
Admitted.

Lemma Split_crefine_err {NameX : Names} {NPX : NamesProperty}: 
    forall (c : com) (vcnt : nat),
        Screfine_err (com2comlist c vcnt) c.
Admitted.

Lemma Split_crefine_inf {NameX : Names} {NPX : NamesProperty}: 
    forall (c : com) (vcnt : nat),
        Screfine_inf (com2comlist c vcnt) c.
Admitted.

Theorem Split_expr_crefine {NameX : Names} {NPX : NamesProperty}: 
    forall (c : com) (vcnt : nat),
        Screfine (com2comlist c vcnt) c.
Proof.
    intros.
    split.
    apply Split_crefine_nrm.
    apply Split_crefine_err.
    apply Split_crefine_inf.
Qed.



