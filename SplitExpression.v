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
}.

Class NamesProperty {NameX : Names} : Prop :=
{
    trans_prop1 : forall (x : var_name) (y : var_name) , (x = y) <-> (name2Sname x = name2Sname y);
    trans_prop2 : forall (x : nat) (y : nat) , (x = y) <-> (nat2Sname x = nat2Sname y);
    trans_prop3 : forall (x : var_name) (y : nat) , name2Sname x <> nat2Sname y;
}.


Definition correspond {NameX : Names} (s ss : state) : Prop :=
    (forall (x : var_name) (i : int64), s.(env) x = i <-> ss.(env) (name2Sname x) = i)
    /\ (forall (a : int64) (v : val), s.(mem) a = Some v -> ss.(mem) a = Some v).

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


Lemma eval_comlist_seq_nrm : forall (cl1 cl2 : Scomlist) (s1 s2 : state),
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

Lemma eval_comlist_seq_err : forall (cl1 cl2 : Scomlist) (s1 : state),
    (Seval_comlist (cl1 ++ cl2)).(err) s1
    <-> ((Seval_comlist cl1).(err) s1 \/
        Rels.concat (Seval_comlist cl1).(nrm) (Seval_comlist cl2).(err) s1).
Proof.
Admitted.

Lemma midstate_deref_nrm {NameX : Names}: forall (e : expr) (vcnt : nat) (s1 : state) (s3 : state),
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
      pose proof eval_comlist_seq_nrm 
      (ex2pre (EBinop op e1 e2) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EBinop op e1 e2) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.
    + rewrite H0 in H.
      pose proof eval_comlist_seq_nrm 
      (ex2pre (EUnop op e) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EUnop op e) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.
    + rewrite H0 in H.
      pose proof eval_comlist_seq_nrm 
      (ex2pre (EDeref e) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EDeref e) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.
    + rewrite H0 in H.
      pose proof eval_comlist_seq_nrm 
      (ex2pre (EAddrOf e) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EAddrOf e) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.  
Qed.

(* Lemma midstate_deref_err {NameX : Names}: forall (e : expr) (vcnt : nat) (s1 : state),
    Rels.concat (Seval_comlist (ex2pre e (S vcnt))).(nrm)
    (Seval_comlist [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))]).(err) s1
    -> match e with
    | EConst c => True
    | EVar x => True
    | _ =>
    exists (s2 : state), 
    (Seval_comlist (ex2pre e (S vcnt))).(nrm) s1 s2
    /\ (Seval_comlist 
        [(SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt)))]).(err) s2
    end.
Admitted. *)

Lemma midstate_addrof {NameX : Names}: forall (e : expr) (vcnt : nat) (s1 : state) (s3 : state),
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
      pose proof eval_comlist_seq_nrm 
      (ex2pre (EBinop op e1 e2) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EBinop op e1 e2) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.
    + rewrite H0 in H.
      pose proof eval_comlist_seq_nrm 
      (ex2pre (EUnop op e) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EUnop op e) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.
    + rewrite H0 in H.
      pose proof eval_comlist_seq_nrm 
      (ex2pre (EDeref e) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EDeref e) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.  
    + rewrite H0 in H.
      pose proof eval_comlist_seq_nrm 
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
      pose proof eval_comlist_seq_nrm 
      (ex2pre (EBinop op0 e1 e2) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EBinop op0 e1 e2) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.
    + rewrite H0 in H.
      pose proof eval_comlist_seq_nrm 
      (ex2pre (EUnop op0 e) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EUnop op0 e) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.
    + rewrite H0 in H.
      pose proof eval_comlist_seq_nrm 
      (ex2pre (EDeref e) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EDeref e) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.
    + rewrite H0 in H.
      pose proof eval_comlist_seq_nrm 
      (ex2pre (EAddrOf e) (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se (EAddrOf e) (S vcnt))]
      s1 s3.
      destruct H1.
      pose proof H1 H.
      sets_unfold in H3.
      tauto.  
Qed.

Lemma some_val: forall (x y : int64), 
    Some (Vint x) = Some (Vint y) <-> x = y.
Proof.
    intros.
    split.
    + admit.
    + intros.
      rewrite H.
      reflexivity.
Admitted.

Ltac int64_lia :=
  change Int64.min_signed with (-9223372036854775808) in *;
  change Int64.max_signed with 9223372036854775807 in *;
  lia.

Lemma eval_single: forall (se : Sexpr) (s : state) (a b : int64),
    (Seval_r se).(nrm) s a /\ (Seval_r se).(nrm) s b -> a = b.
Proof.
    destruct se; simpl; intros s a b.
    + destruct cv; simpl.
      - intros.
        destruct H.
        destruct H.
        destruct H0.
        rewrite H.
        rewrite H0.
        tauto.
      - unfold deref_sem_nrm.
        intros.
        destruct H.
        destruct H.
        destruct H0.
        destruct H.
        destruct H0.
        rewrite H in H0.
        rewrite H0 in H1.
        rewrite H1 in H2.
        pose proof some_val a b.
        destruct H3.
        pose proof H3 H2.
        tauto.
    + destruct op; simpl.
      - unfold Seval_r_cv, or_sem_nrm, SC_or_compute_nrm, NonSC_compute_nrm, NonSC_or.
        destruct cv1, cv2; simpl; intros.
        --  destruct H.
            destruct H.
            destruct H.
            destruct H0.
            destruct H0.
            destruct H0.
            destruct H1, H2.
            * destruct H1.
              destruct H2.
              rewrite H4.
              rewrite H5.
              tauto.
            * destruct H2.
              destruct H4.
              assert (Int64.min_signed <= 0 <= Int64.max_signed).
              int64_lia.
              pose proof Int64.signed_repr 0 H5.
              destruct H.
              destruct H1.
              rewrite <- H0 in H.
              rewrite H in H1.
              rewrite H2 in H1.
              rewrite H6 in H1.
              tauto.
            * destruct H2.
              destruct H.
              destruct H1.
              assert (Int64.min_signed <= 0 <= Int64.max_signed).
              int64_lia.
              pose proof Int64.signed_repr 0 H7.
              rewrite H0 in H2.
              rewrite <- H in H2.
              rewrite H1 in H2.
              tauto.
            * admit.
      Admitted.



Lemma ex2se_prop {NameX : Names}: 
    forall (e : expr) (vcnt : nat) (s2 s3 : state),
    match e with
    | EConst c => True
    | EVar x => True
    | _ => (Seval_comlist
        [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))]).(nrm) s2 s3
        -> 
        forall (a : int64),
            (Seval_r (genSECV vcnt)).(nrm) s3 a <-> (Seval_r (ex2se e (S vcnt))).(nrm) s2 a
    end.
Proof.
    intros.
    unfold Seval_comlist, seq_sem, asgn_var_sem, asgn_deref_sem, asgn_deref_sem_nrm, skip_sem, CDenote.nrm.
    unfold var_sem_l.
    simpl.
    sets_unfold.
    pose proof eval_single (ex2se e (S vcnt)) as Hm.
    destruct e.
    + tauto.
    + tauto.
    + intros. destruct H as [x [H ?]]. destruct H. destruct H.
      destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
      rewrite H0 in H4, H5, H6.
      unfold deref_sem_nrm.
      pose proof H5 (nat2Sname vcnt).
      rewrite H in H1.
      rewrite H1.
      split.
      - intros.
        destruct H7.
        destruct H7.
        rewrite <- H7 in H8.
        rewrite H8 in H4.
        pose proof some_val a x1.
        destruct H9.
        pose proof H9 H4.
        rewrite <- H11 in H2.
        apply H2.
      - intros.
        exists x0.
        split.
        tauto.
        pose proof Hm s2 a x1.
        destruct H8.
        tauto.
        tauto.
    + intros. destruct H as [x [H ?]]. destruct H. destruct H.
      destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
      rewrite H0 in H4, H5, H6.
      unfold deref_sem_nrm.
      pose proof H5 (nat2Sname vcnt).
      rewrite H in H1.
      rewrite H1.
      split.
      - intros.
        destruct H7.
        destruct H7.
        rewrite <- H7 in H8.
        rewrite H8 in H4.
        pose proof some_val a x1.
        destruct H9.
        pose proof H9 H4.
        rewrite <- H11 in H2.
        apply H2.
      - intros.
        exists x0.
        split.
        tauto.
        pose proof Hm s2 a x1.
        destruct H8.
        tauto.
        tauto.
    + intros. destruct H as [x [H ?]]. destruct H. destruct H.
      destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
      rewrite H0 in H4, H5, H6.
      unfold deref_sem_nrm.
      pose proof H5 (nat2Sname vcnt).
      rewrite H in H1.
      rewrite H1.
      split.
      - intros.
        destruct H7.
        destruct H7.
        rewrite <- H7 in H8.
        rewrite H8 in H4.
        pose proof some_val a x1.
        destruct H9.
        pose proof H9 H4.
        rewrite <- H11 in H2.
        apply H2.
      - intros.
        exists x0.
        split.
        tauto.
        pose proof Hm s2 a x1.
        destruct H8.
        tauto.
        tauto.
    + intros. destruct H as [x [H ?]]. destruct H. destruct H.
      destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
      rewrite H0 in H4, H5, H6.
      unfold deref_sem_nrm.
      pose proof H5 (nat2Sname vcnt).
      rewrite H in H1.
      rewrite H1.
      split.
      - intros.
        destruct H7.
        destruct H7.
        rewrite <- H7 in H8.
        rewrite H8 in H4.
        pose proof some_val a x1.
        destruct H9.
        pose proof H9 H4.
        rewrite <- H11 in H2.
        apply H2.
      - intros.
        exists x0.
        split.
        tauto.
        pose proof Hm s2 a x1.
        destruct H8.
        tauto.
        tauto.
Qed.

Lemma ex2se_deref {NameX : Names}:
    forall (e : expr) (vcnt : nat),
    match e with
    | EConst c =>
        ex2se (EDeref e) vcnt = SEDeref (SEConst c)
    | EVar v =>
        ex2se (EDeref e) vcnt = SEDeref (genSEVar v)
    | _ =>
        ex2se (EDeref e) vcnt = SEDeref (genSEVar_n vcnt)
    end.
Proof.
    intros.
    unfold ex2se.
    destruct e; reflexivity.    
Qed.

Lemma mem_split : forall (s : state) (x : int64),
    (exists (v : val), s.(mem) x = Some v) \/ s.(mem) x = None.
Proof.
    intros.
    destruct (s.(mem) x).
    + left.
        exists v.
      tauto.
    + right.
      tauto.
Qed.


(* 需要拆成多个来证明， Induction *)
Lemma midstate_cor {NameX : Names} {NPX : NamesProperty} : forall (e : expr) (vcnt : nat) (s1 ss1 ss2 ss3 : state),
    correspond s1 ss1
    -> correspond s1 ss3
    -> (Seval_comlist (ex2pre e (S vcnt))).(nrm) ss1 ss2
    -> (Seval_comlist [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))]).(nrm) ss2 ss3
    -> correspond s1 ss2.
Proof.
    induction e.
    + simpl; sets_unfold.
      intros.
      rewrite H1 in H.
      tauto.
    + simpl; sets_unfold.
      intros.
      rewrite H1 in H.
      tauto.
    + intros.
      revert H2 H0.
      unfold Seval_comlist, seq_sem, asgn_var_sem, 
      skip_sem, asgn_deref_sem, asgn_deref_sem_nrm, CDenote.nrm,
      var_sem_l, EDenote.nrm, correspond.
      sets_unfold.
      intros.
      destruct H2.
      destruct H2.
      destruct H2.
      destruct H2.
      destruct H2.
      destruct H4.
      destruct H5.
      destruct H6.
      destruct H6.
      destruct H7.
      rewrite H3 in H6, H7.
      destruct H0.
      split.
      - intros.
        pose proof H0 x2 i.
        destruct H9.
        pose proof H6 (name2Sname x2).
        split. intros.
        pose proof H9 H12.
        rewrite H11.
        tauto.
        intros.
        rewrite H11 in H12.
        pose proof H10 H12.
        tauto.
      - intros.
        pose proof H8 a v H9.
        pose proof H6 (nat2Sname vcnt).
        rewrite H11 in H2.
        pose proof trans_prop3.
        admit.
        (* 需要用到midstate_binop *)
    + intros.
      
      revert H2 H0.
      unfold Seval_comlist, seq_sem, asgn_var_sem, 
      skip_sem, asgn_deref_sem, asgn_deref_sem_nrm, CDenote.nrm,
      var_sem_l, EDenote.nrm, correspond.
      sets_unfold.
      intros.
      destruct H2.
      destruct H2.
      destruct H2.
      destruct H2.
      destruct H2.
      destruct H4.
      destruct H5.
      destruct H6.
      destruct H6.
      destruct H7.
      rewrite H3 in H6, H7.
      destruct H0.
      split.
      - intros.
        pose proof H0 x2 i.
        destruct H9.
        pose proof H6 (name2Sname x2).
        split. intros.
        pose proof H9 H12.
        rewrite H11.
        tauto.
        intros.
        rewrite H11 in H12.
        pose proof H10 H12.
        tauto.
      - admit.
Admitted.


Lemma deref4 {NameX : Names} : forall (e : expr) (vcnt : nat) (s : state) (a : int64),
    (Seval_r (ex2se (EDeref e) vcnt)).(nrm) s a
    -> ex2se (EDeref e) vcnt = SEDeref (genSEVar_n vcnt)
    -> exists (x : int64), 
        (Seval_r (genSECV vcnt)).(nrm) s x.
Proof.
    intros.
    rewrite H0 in H.
    revert H.
    simpl.
    unfold deref_sem_nrm.
    intros.
    destruct H.
    destruct H.
    destruct H.
    exists x, x0.
    apply H.
Qed.


Lemma deref7{NameX : Names}:
    forall (e : expr) (vcnt : nat) (x a : int64) (s1 ss3 : state),
    correspond s1 ss3 ->
    ((eval_r e).(nrm) s1 x \/
    (eval_r e).(err) s1 /\ True)
    -> (Seval_r (genSECV vcnt)).(nrm) ss3 x
    -> (Seval_r (SEDeref (genSEVar_n vcnt))).(nrm) ss3 a
    -> (eval_r (EDeref e)).(nrm) s1 a
        \/ (eval_r (EDeref e)).(err) s1 /\ True.
Proof.
    unfold correspond.
    simpl.
    unfold deref_sem_nrm, deref_sem_err.
    sets_unfold.
    intros.
    destruct H.
    destruct H1.
    destruct H1.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H2.
    rewrite H2 in H1.
    rewrite H1 in H2, H6.
    rewrite H4 in H6.
    pose proof some_val x x1.
    destruct H7.
    pose proof H7 H6.
    rewrite <- H9 in H5.
    destruct H0.
    + pose proof mem_split s1 x.
      destruct H10.
      - destruct H10 as [v].
        pose proof H3 x v H10.
        rewrite H11 in H5.
        left.
        exists x.
        split.
        tauto.
        rewrite H5 in H10.
        tauto.
      - right.
        split.
        right.
        exists x.
        split.
        tauto.
        left.
        tauto.
        tauto.
    + destruct H0.
      right.
      split.
      left.
      tauto.
      tauto.
Qed.

Lemma deref_err_r: forall (e : expr) (s : state),
    (eval_r e).(err) s
    -> (eval_r (EDeref e)).(err) s.
Proof.
    unfold eval_r.
    intros.
    unfold deref_sem_r, EDenote.err.
    sets_unfold.
    tauto.
Qed.

Definition Serefine_nrm {NameX : Names} (cl : Scomlist) (se : Sexpr) (e : expr): Prop :=
    forall (s1 ss1 ss2 : state),
        (Seval_comlist cl).(nrm) ss1 ss2 ->
        correspond s1 ss1 ->
        correspond s1 ss2 ->
        (Seval_r se).(nrm) ss2 ⊆ ((eval_r e).(nrm) ∪ ((eval_r e).(err) × int64)) s1
        /\ (Seval_l se).(nrm) ss2 ⊆ ((eval_l e).(nrm) ∪ ((eval_l e).(err) × int64)) s1.

Definition Serefine_err1 {NameX : Names} (cl : Scomlist) (se : Sexpr) (e : expr): Prop :=
    forall (s1 ss1 : state),
        (correspond s1 ss1 
        -> (Seval_comlist cl).(err) ss1 
        -> ((eval_l e).(err) s1 \/ (eval_r e).(err) s1)).

Definition Serefine_err1S {NameX : Names} (cl : Scomlist) (se : Sexpr) (e : expr): Prop :=
    forall (s1 ss1 : state),
        (correspond s1 ss1 
        -> (Seval_comlist cl).(err) ss1 
        -> (eval_r e).(err) s1).

Definition Serefine_err2 {NameX : Names} (cl : Scomlist) (se : Sexpr) (e : expr): Prop :=
    forall (s1 ss1 ss2 : state),
        (correspond s1 ss1
        -> correspond s1 ss2
        -> (Seval_comlist cl).(nrm) ss1 ss2
        -> ((Seval_l se).(err) ss2 \/ (Seval_r se).(err) ss2)
        -> ((eval_l e).(err) s1 \/ (eval_r e).(err) s1)).

Definition Serefine_errS {NameX : Names} (cl : Scomlist) (se : Sexpr) (e : expr): Prop :=
    Serefine_err1S cl se e
    /\ Serefine_err2 cl se e.

Definition Serefine_err {NameX : Names} (cl : Scomlist) (se : Sexpr) (e : expr): Prop :=
    Serefine_err1 cl se e
    /\ Serefine_err2 cl se e.

Lemma strict {NameX : Names} : forall (cl : Scomlist) (se : Sexpr) (e : expr),
    Serefine_errS cl se e -> Serefine_err cl se e.
Proof.
    unfold Serefine_err, Serefine_errS, Serefine_err1, Serefine_err1S.
    intros.
    destruct H.
    split.
    intros.
    pose proof H s1 ss1 H1 H2.
    tauto.
    tauto.
Qed.


Record Serefine {NameX : Names} (cl : Scomlist) (se : Sexpr) (e : expr): Prop := {
    nrm_Serefine:
        Serefine_nrm cl se e;
    err_Serefine:
        Serefine_err cl se e;
    }.

Lemma Split_Serefine_nrm_deref {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr),
    (forall (vcnt : nat), Serefine_nrm (ex2pre e vcnt) (ex2se e vcnt) e)
    ->
    forall (vcnt : nat), Serefine_nrm (ex2pre (EDeref e) vcnt) (ex2se (EDeref e) vcnt) (EDeref e).
Proof.
    unfold Serefine_nrm.
    sets_unfold.
    intros e IHe vcnt s1 ss1 ss3 ? ? ?.
    split.
    + intros.
      pose proof midstate_deref_nrm e vcnt ss1 ss3 H as Hm.
      pose proof ex2se_prop e vcnt as Hp.
      pose proof ex2se_deref e vcnt as Hd.
      pose proof deref4 e vcnt ss3 a H2 as Hd4.
      pose proof deref7 e vcnt as H70.
      pose proof midstate_cor e as Hmc.
      destruct e.
      - revert H H0 H1 H2.
        unfold correspond.
        simpl.
        sets_unfold.
        unfold deref_sem_nrm.
        intros.
        destruct H2.
        pose proof mem_split s1 x.
        destruct H3.
        --  left.
            destruct H2.
            exists x.
            split.
            tauto.
            destruct H1.
            destruct H3 as [v].
            pose proof H5 x v H3.
            rewrite H3.
            rewrite H6 in H4.
            tauto.
        --  right.
            split.
            right.
            unfold deref_sem_err.
            exists x.
            split.
            destruct H2.
            tauto.
            left.
            tauto.
            tauto.
      - revert H H0 H1 H2.
        unfold correspond.
        simpl.
        sets_unfold.
        unfold deref_sem_nrm.
        intros.
        destruct H2.
        destruct H2.
        destruct H2.
        destruct H2.
        pose proof mem_split s1 x0.
        pose proof mem_split s1 x1.
        destruct H5, H6.
        --  left.
            destruct H1.
            exists x0.
            destruct H5.
            split.
            exists x1.
            split.
            pose proof H1 x x1.
            destruct H8.
            pose proof H9 H2.
            tauto.
            destruct H6.
            pose proof H7 x1 x3 H6.
            rewrite H6.
            rewrite <- H8.
            tauto.
            pose proof H7 x0 x2 H5.
            rewrite H5.
            rewrite <- H8.
            tauto.
        --  right.
            destruct H5.
            split.
            left.
            right.
            unfold deref_sem_err.
            exists x1.
            destruct H1.
            pose proof H1 x x1.
            destruct H8.
            pose proof H9 H2.
            split.
            tauto.
            left.
            tauto.
            tauto.
        --  right.
            destruct H6.
            destruct H1.
            split.
            right.
            unfold deref_sem_err.
            exists x0.
            split.
            exists x1.
            split.
            pose proof H1 x x1.
            destruct H8.
            pose proof H9 H2.
            tauto.
            pose proof H7 x1 x2 H6.
            rewrite H6.
            rewrite H8 in H4.
            tauto.
            left.
            tauto.
            tauto.
        --  right.
            split.
            left.
            right.
            unfold deref_sem_err.
            exists x1.
            destruct H1.
            pose proof H1 x x1.
            destruct H8.
            pose proof H9 H2.
            split.
            tauto.
            left.
            tauto.
            tauto. 
      - destruct Hm as [ss2].
        destruct H3.
        pose proof Hp ss2 ss3 H4. 
        pose proof Hd4 Hd as Hd4.
        destruct Hd4.
        pose proof H5 x.
        destruct H7.
        pose proof H7 H6.
        pose proof Hmc vcnt s1 ss1 ss2 ss3 H0 H1 H3 H4 as Hmc1.
        pose proof IHe (S vcnt) s1 ss1 ss2 H3 H0 Hmc1.
        destruct H10.
        pose proof H10 x H9.
        rewrite Hd in H2.
        pose proof H70 x a s1 ss3 as H70.
        tauto.
      - destruct Hm as [ss2].
        destruct H3.
        pose proof Hp ss2 ss3 H4. 
        pose proof Hd4 Hd as Hd4.
        destruct Hd4.
        pose proof H5 x.
        destruct H7.
        pose proof H7 H6.
        pose proof Hmc vcnt s1 ss1 ss2 ss3 H0 H1 H3 H4 as Hmc1.
        pose proof IHe (S vcnt) s1 ss1 ss2 H3 H0 Hmc1.
        destruct H10.
        pose proof H10 x H9.
        rewrite Hd in H2.
        pose proof H70 x a s1 ss3 as H70.
        tauto.
      - destruct Hm as [ss2].
        destruct H3.
        pose proof Hp ss2 ss3 H4. 
        pose proof Hd4 Hd as Hd4.
        destruct Hd4.
        pose proof H5 x.
        destruct H7.
        pose proof H7 H6.
        pose proof Hmc vcnt s1 ss1 ss2 ss3 H0 H1 H3 H4 as Hmc1.
        pose proof IHe (S vcnt) s1 ss1 ss2 H3 H0 Hmc1.
        destruct H10.
        pose proof H10 x H9.
        rewrite Hd in H2.
        pose proof H70 x a s1 ss3 as H70.
        tauto.
      - destruct Hm as [ss2].
        destruct H3.
        pose proof Hp ss2 ss3 H4. 
        pose proof Hd4 Hd as Hd4.
        destruct Hd4.
        pose proof H5 x.
        destruct H7.
        pose proof H7 H6.
        pose proof Hmc vcnt s1 ss1 ss2 ss3 H0 H1 H3 H4 as Hmc1.
        pose proof IHe (S vcnt) s1 ss1 ss2 H3 H0 Hmc1.
        destruct H10.
        pose proof H10 x H9.
        rewrite Hd in H2.
        pose proof H70 x a s1 ss3 as H70.
        tauto.
    + simpl.
      intros.
      pose proof ex2se_prop e vcnt as He.
      pose proof midstate_deref_nrm e vcnt ss1 ss3 H as Hm.
      pose proof midstate_cor e vcnt s1 as Hmc.
      destruct e.
      - tauto.
      - unfold deref_sem_nrm.
        revert H H0 H1.
        unfold correspond.
        simpl.
        sets_unfold.
        intros.
        destruct H2.
        destruct H2.
        destruct H1.
        pose proof H1 x x0.
        destruct H5.
        pose proof H6 H2.
        pose proof mem_split s1 x0.
        destruct H8.
        --  destruct H8.
            pose proof H4 x0 x1 H8.
            left.
            exists x0.
            split.
            tauto.
            rewrite H8.
            rewrite H9 in H3.
            tauto.
        --  right.
            split.
            right.
            unfold deref_sem_err.
            exists x0.
            split.
            apply H7.
            left.
            tauto.
            tauto.
      - destruct Hm as [ss2].
        destruct H3.
        pose proof Hmc ss1 ss2 ss3 H0 H1 H3 H4.
        pose proof IHe (S vcnt) s1 ss1 ss2 H3 H0 H5.
        destruct H6.
        pose proof He ss2 ss3 H4 a.
        destruct H8.
        assert ((Seval_l (SEDeref (genSEVar_n vcnt))).(nrm) ss3 a = (Seval_r (genSECV vcnt)).(nrm) ss3 a).
        {
            simpl.
            reflexivity.
        }
        rewrite H10 in H2.
        pose proof H8 H2.
        pose proof H6 a H11.
        tauto.
      - destruct Hm as [ss2].
        destruct H3.
        pose proof Hmc ss1 ss2 ss3 H0 H1 H3 H4.
        pose proof IHe (S vcnt) s1 ss1 ss2 H3 H0 H5.
        destruct H6.
        pose proof He ss2 ss3 H4 a.
        destruct H8.
        assert ((Seval_l (SEDeref (genSEVar_n vcnt))).(nrm) ss3 a = (Seval_r (genSECV vcnt)).(nrm) ss3 a).
        {
            simpl.
            reflexivity.
        }
        rewrite H10 in H2.
        pose proof H8 H2.
        pose proof H6 a H11.
        tauto.
      - destruct Hm as [ss2].
        destruct H3.
        pose proof Hmc ss1 ss2 ss3 H0 H1 H3 H4.
        pose proof IHe (S vcnt) s1 ss1 ss2 H3 H0 H5.
        destruct H6.
        pose proof He ss2 ss3 H4 a.
        destruct H8.
        assert ((Seval_l (SEDeref (genSEVar_n vcnt))).(nrm) ss3 a = (Seval_r (genSECV vcnt)).(nrm) ss3 a).
        {
            simpl.
            reflexivity.
        }
        rewrite H10 in H2.
        pose proof H8 H2.
        pose proof H6 a H11.
        tauto.
      - destruct Hm as [ss2].
        destruct H3.
        pose proof Hmc ss1 ss2 ss3 H0 H1 H3 H4.
        pose proof IHe (S vcnt) s1 ss1 ss2 H3 H0 H5.
        destruct H6.
        pose proof He ss2 ss3 H4 a.
        destruct H8.
        assert ((Seval_l (SEDeref (genSEVar_n vcnt))).(nrm) ss3 a = (Seval_r (genSECV vcnt)).(nrm) ss3 a).
        {
            simpl.
            reflexivity.
        }
        rewrite H10 in H2.
        pose proof H8 H2.
        pose proof H6 a H11.
        tauto.
Qed.


Lemma Split_Serefine_err1S_deref {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr),
    (forall (vcnt : nat), Serefine_errS (ex2pre e vcnt) (ex2se e vcnt) e)
    ->
    forall (vcnt : nat), Serefine_err1S (ex2pre (EDeref e) vcnt) (ex2se (EDeref e) vcnt) (EDeref e).
Proof.
    unfold Serefine_errS, Serefine_err1S, Serefine_err2.
    intros.
    pose proof H (S vcnt) as H.
    destruct H as [IH1 IH2].
    pose proof ex2pre_deref vcnt e as Hd.
    pose proof midstate_deref_nrm e vcnt as Hm.
    pose proof eval_comlist_seq_err (ex2pre e (S vcnt)) 
        [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))] ss1 as Hs.
    pose proof deref_err_r e s1 as Herr.
    destruct Hs as [Hs1 Hs2].
    destruct e.
    + admit.
    + admit.
    + rewrite Hd in H1.
      pose proof Hs1 H1 as H.
      destruct H.
      - pose proof IH1 s1 ss1 H0 H.
        apply Herr.
        tauto.
      - sets_unfold in H.
        destruct H as [ss2].
        destruct H.
Admitted.


Lemma Split_Serefine_nrm {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr) (vcnt : nat), 
    Serefine_nrm (ex2pre e vcnt) (ex2se e vcnt) e.
Proof.
    induction e.
    + admit.
    + admit.
    + admit.
    + admit.
    + apply Split_Serefine_nrm_deref; tauto.
    + admit.
Admitted.

Lemma Split_Serefine_errS {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr) (vcnt : nat), 
    Serefine_errS (ex2pre e vcnt) (ex2se e vcnt) e.
Proof.
    induction e.
    + admit.
    + admit.
    + admit.
    + admit.
    + revert IHe.
      unfold Serefine_errS, Serefine_err1S, Serefine_err2.
      intros.
      admit.
    + admit.
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

Definition Screfine_nrm {NameX : Names} (cl : Scomlist) (c : com): Prop :=
    forall (s1 s2 ss1 ss2 : state),
        correspond s1 ss1 ->
        (Seval_comlist cl).(nrm) ss1 ss2
        -> (eval_com c).(err) s1
            \/ ((eval_com c).(nrm) s1 s2 
                /\ correspond s2 ss2).

Definition Screfine_err {NameX : Names} (cl : Scomlist) (c : com): Prop :=
    forall (s1 ss1 : state),
    correspond s1 ss1 ->
        (Seval_comlist cl).(err) ss1 -> (eval_com c).(err) s1.

Definition Screfine_inf {NameX : Names} (cl : Scomlist) (c : com): Prop :=
    forall (s1 ss1 : state),
    correspond s1 ss1 ->
        (Seval_comlist cl).(inf) ss1 
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



