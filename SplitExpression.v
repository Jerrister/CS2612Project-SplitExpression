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
  | SCIf (e: Sexpr) (l1 l2: Scomlist): Scom 
  | SCWhile (e: Sexpr) (body: Scomlist): Scom
with Scomlist : Type :=
  | nil 
  | cons (c : Scom) (l : Scomlist).

Notation "x :: l" := (cons x l).
Notation "[]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Definition nat_add (a : nat) (b : nat) : nat :=
    (a + b)%nat.

Fixpoint length (l:Scomlist) : nat :=
    match l with
    | nil => O
    | h :: t => 
        match h with
        | SCIf e c1 c2 => (nat_add (nat_add (length c1) (length c2)) (length t))
        | SCWhile e c => (nat_add (length c) (length t))
        | _ => (S (length t))
        end
    end.

Fixpoint app (l1: Scomlist) (l2: Scomlist) : Scomlist :=
    match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
    end.

Notation "x ++ y" := (app x y).

(* nat加法的结合律 *)
Lemma nat_add_asso: forall (a b c : nat),
    nat_add (nat_add a b) c = nat_add a (nat_add b c).
Proof.
    induction a.
    + intros.
      simpl.
      reflexivity.
    + simpl.
      intros.
      pose proof IHa b c.
      rewrite H.
      reflexivity.
Qed.

(* 列表长度的加法律 *)
Lemma seq_length: forall (cl1 cl2 : Scomlist),
    length (cl1 ++ cl2) = nat_add (length cl1) (length cl2).
Proof.
    intros.
    induction cl1.
    + simpl.
      reflexivity.
    + simpl.
      destruct c; rewrite IHcl1; simpl.
      - tauto.
      - tauto.
      - tauto.
      - pose proof nat_add_asso (nat_add (length l1) (length l2)) (length cl1) (length cl2).
        rewrite <- H.
        reflexivity.
      - pose proof nat_add_asso (length body) (length cl1) (length cl2).
        rewrite <- H.
        reflexivity.
Qed.

(* 列表的结合律 *)
Lemma seq_asso: forall (cl1 cl2 cl3 : Scomlist),
    (cl1 ++ cl2) ++ cl3 = cl1 ++ cl2 ++ cl3.
Proof.
    induction cl1.
    + simpl.
      tauto.
    + intros.
      simpl.
      pose proof IHcl1 cl2 cl3.
      rewrite H.
      tauto.
Qed.



End Lang_WhileDS.

(* 表达式拆分语义 *)
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

Fixpoint Seval_com (c: Scom): CDenote :=
    match c with
    | SCSkip =>
        skip_sem
    | SCAsgnVar X e =>
        asgn_var_sem X (Seval_r e)
    | SCAsgnDeref cv1 cv2 =>
        asgn_deref_sem (Seval_r_cv cv1) (Seval_r_cv cv2)
    | SCIf e cl1 cl2 =>
        if_sem (Seval_r e) (Seval_comlist cl1) (Seval_comlist cl2)
    | SCWhile e body =>
        while_sem (Seval_r e) (Seval_comlist body)
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
    trans_prop2 : forall (x : nat) (y : nat) (s :state) , (x = y) <-> (s.(env) (nat2Sname x) = s.(env) (nat2Sname y));
    trans_prop3 : forall (x : var_name) (y : nat) , name2Sname x <> nat2Sname y;
}.

(* 状态空间映射定义 *)
Definition correspond {NameX : Names} (s ss : state) : Prop :=
    (forall (x : var_name) (i : int64), s.(env) x = i <-> ss.(env) (name2Sname x) = i)
    /\ (forall (a : int64) (v : val), s.(mem) a = Some v -> ss.(mem) a = Some v)
    /\ (forall (vcnt : nat), s.(mem) (ss.(env) (nat2Sname vcnt)) = None 
                            /\ ss.(mem) (ss.(env) (nat2Sname vcnt)) <> None).

(* 辅助定义：一个变量要么已定义要么未定义 *)
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

(* 性质1：若在对应拆分状态内变量未定义或不存在，则在原状态中该变量未定义或不存在 *)
Lemma correspond_prop0 {NameX: Names}: forall (s ss : state) (x : int64),
    correspond s ss
    -> ss.(mem) x = None \/ ss.(mem) x = Some Vuninit
    -> s.(mem) x = None \/ s.(mem) x = Some Vuninit.
Proof.
    unfold correspond.
    intros.
    destruct H as [? [? ?]].
    pose proof mem_split s x.
    destruct H3.
    destruct H3 as [v].
    pose proof H1 x v H3.
    rewrite H4 in H0.
    destruct H0.
    discriminate.
    right.
    rewrite H3.
    tauto.
    left.
    tauto.
Qed.

(* 经过辅助变量赋值不改变correspond关系 *)
Lemma correspond_prop1 {NameX : Names}: 
    forall (vcnt : nat) (se : Sexpr) (s1 ss1 ss2 : state),
        correspond s1 ss1
        -> (Seval_comlist [SCAsgnVar (nat2Sname vcnt) se]).(nrm) ss1 ss2
        -> correspond s1 ss2.
Proof.
    intros.
    revert H H0.
    simpl.
    unfold correspond, asgn_deref_sem_nrm.
    sets_unfold.
    intros.
    destruct H.
    destruct H1.
    destruct H0.
    destruct H0.
    rewrite H3 in H0.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H4.
    destruct H4.
    destruct H5.
    destruct H6.
    split.
    intros x0 i.
    split; intros; pose proof H x0 i as H; 
    destruct H as [H10 H11]; pose proof H6 (name2Sname x0).
    pose proof H10 H8.
    rewrite <- H.
    tauto.
    rewrite H8 in H.
    pose proof H11 H.
    tauto.
    split; intros.
    pose proof H1 a v H8.
    pose proof classic (ss1.(env) (nat2Sname vcnt) = a).
    destruct H10.
    pose proof H2 vcnt.
    destruct H11 as [H11 H20].
    rewrite H10 in H11.
    rewrite H8 in H11.
    discriminate.
    pose proof H7 a H10.
    rewrite <- H11.
    tauto.
    pose proof H6 (nat2Sname vcnt0).
    pose proof H2 vcnt0.
    rewrite <- H8.
    split.
    tauto.
    pose proof H6 (nat2Sname vcnt0).
    pose proof H7 (ss1.(env) (nat2Sname vcnt0)).
    pose proof classic (ss1.(env) (nat2Sname vcnt) = ss1.(env) (nat2Sname vcnt0)).
    destruct H12.
    rewrite H12 in H5.
    rewrite H5.
    discriminate.
    pose proof H11 H12.
    rewrite <- H13.
    tauto.
Qed.

(* 生成对应中间变量 *)
Definition genSEVar {NameX : Names} (x : var_name) : CV:=
    SEVar (name2Sname x).

Definition genSEVar_n {NameX : Names} (vcnt :nat) : CV :=
    SEVar (nat2Sname vcnt).

Definition genSECV {NameX : Names} (vcnt :nat) : Sexpr :=
    SEConstOrVar (SEVar (nat2Sname vcnt)).


(* 表达式拆分为pre与se *)
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
            SEBinop op (genSEVar_n vcnt) (genSEVar_n (S vcnt))
        end
    | EUnop op e =>
        SEUnop op (genSEVar_n vcnt)
    | EDeref e =>
        SEDeref (genSEVar_n vcnt)
    | EAddrOf e =>
        match e with
        | EVar v =>
            SEAddrOf (genSEVar v)
        | EDeref e0 =>
            genSECV vcnt
        | _ =>
            SEConstOrVar (SEConst 0)
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
            (ex2pre e1 (S (S vcnt))) ++
            [(SCAsgnVar (nat2Sname (S vcnt)) (ex2se e1 (S (S vcnt))))] ++
            [(SCIf (genSECV (S vcnt)) 
                ((ex2pre e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))
                ++ [(SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt)))))))]
                ++ [(SCIf (genSECV (S vcnt))
                      [(SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1)))]
                      [(SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0)))])])
                [(SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0)))])]
        | OOr =>
            (ex2pre e1 (S (S vcnt))) ++
            [(SCAsgnVar (nat2Sname (S vcnt)) (ex2se e1 (S (S vcnt))))] ++
            [(SCIf (genSECV (S vcnt)) 
                [(SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1)))]
                ((ex2pre e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))
                ++ [(SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt)))))))]
                ++ [(SCIf (genSECV (S vcnt))
                      [(SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1)))]
                      [(SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0)))])]))]
        | _ =>
            (ex2pre e1 (S (S vcnt))) 
            ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt))))] 
            ++ (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))
            ++ [(SCAsgnVar (nat2Sname (S vcnt)) 
                (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))))]
        end
    | EUnop op e =>
        (ex2pre e (S vcnt)) 
        ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt)))]
    | EDeref e =>
        (ex2pre e (S vcnt)) 
        ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt)))] 
    | EAddrOf e =>
        match e with
        | EDeref e0 =>
            (ex2pre e0 (S vcnt))
            ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e0 (S vcnt)))]
        | _ => 
            []
        end
    end.
  
(* 程序语句经过表达式拆分变换为pre和se *)

Fixpoint  com2pre {NameX : Names}
    (c : com)
    (vcnt : nat):
    Scomlist :=
    match c with
    | CSkip =>
        []
    | CAsgnVar X e =>
        (ex2pre e vcnt) 
    | CAsgnDeref e1 e2 =>
        (ex2pre e1 (S (S vcnt)))
      ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt))))]
        ++ (ex2pre e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))
        ++ [(SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt)))))))]
    | CSeq c1 c2 =>
        com2pre c1 vcnt
    | CIf e c1 c2 =>
        (ex2pre e vcnt)
    | CWhile e c =>
        (ex2pre e vcnt)
    end.

Fixpoint  com2sc {NameX : Names}
    (c : com)
    (vcnt : nat):
    Scomlist :=
    match c with
    | CSkip =>
        []
    | CAsgnVar X e =>
        [(SCAsgnVar (name2Sname X) (ex2se e vcnt))]
    | CAsgnDeref e1 e2 =>
        [(SCAsgnDeref (genSEVar_n vcnt) (genSEVar_n (S vcnt)))]
    | CSeq c1 c2 =>
        (com2sc c1 vcnt) 
        ++ (com2pre c2 (nat_add vcnt (nat_add (length (com2pre c1 vcnt)) (length (com2sc c1 vcnt)))))
        ++ (com2sc c2 (nat_add vcnt (nat_add (length (com2pre c1 vcnt)) (length (com2sc c1 vcnt)))))
    | CIf e c1 c2 =>
        [(SCIf (ex2se e vcnt)
            ((com2pre c1 (nat_add vcnt (length (ex2pre e vcnt))))
            ++ (com2sc c1 (nat_add vcnt (length (ex2pre e vcnt))))) 
            ((com2pre c2 (nat_add (nat_add vcnt (length (ex2pre e vcnt)))
                (nat_add (length (com2pre c1 (nat_add vcnt (length (ex2pre e vcnt)))))
                (length (com2sc c1 (nat_add vcnt (length (ex2pre e vcnt))))))))
            ++ (com2sc c2 (nat_add (nat_add vcnt (length (ex2pre e vcnt)))
                (nat_add (length (com2pre c1 (nat_add vcnt (length (ex2pre e vcnt)))))
                (length (com2sc c1 (nat_add vcnt (length (ex2pre e vcnt))))))))))]
    | CWhile e c =>
        [(SCWhile (ex2se e vcnt) 
        ((com2pre c (nat_add vcnt (length (ex2pre e vcnt))))
        ++ (com2sc c (nat_add vcnt (length (ex2pre e vcnt))))
        ++ (ex2pre e vcnt)))]
    end.

Definition  com2comlist {NameX : Names}
    (c : com)
    (vcnt : nat):
    Scomlist := 
    (com2pre c vcnt) ++ (com2sc c vcnt).

Lemma ex2pre_binop {NameX : Names}:
    forall (vcnt : nat) (e1 e2 : expr) (op : binop),
    match op with
        | OAnd =>
          ex2pre (EBinop op e1 e2) vcnt =
            (ex2pre e1 (S (S vcnt))) ++
            [(SCAsgnVar (nat2Sname (S vcnt)) (ex2se e1 (S (S vcnt))))] ++
            [(SCIf (genSECV (S vcnt)) 
                ((ex2pre e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))
                ++ [(SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt)))))))]
                ++ [(SCIf (genSECV (S vcnt))
                      [(SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1)))]
                      [(SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0)))])])
                [(SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0)))])]
        | OOr =>
          ex2pre (EBinop op e1 e2) vcnt =
            (ex2pre e1 (S (S vcnt))) ++
            [(SCAsgnVar (nat2Sname (S vcnt)) (ex2se e1 (S (S vcnt))))] ++
            [(SCIf (genSECV (S vcnt)) 
                [(SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1)))]
                ((ex2pre e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))
                ++ [(SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt)))))))]
                ++ [(SCIf (genSECV (S vcnt))
                      [(SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1)))]
                      [(SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0)))])]))]
        | _ =>
          ex2pre (EBinop op e1 e2) vcnt =
              (ex2pre e1 (S (S vcnt))) 
              ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt))))] 
              ++ (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))
              ++ [(SCAsgnVar (nat2Sname (S vcnt)) 
                  (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))))]
        end.
Proof.
  destruct op;
  reflexivity.
Qed.

Lemma ex2pre_addrof {NameX : Names}:
    forall (e : expr) (vcnt : nat),
    match e with 
    | EDeref e0 => (ex2pre (EAddrOf e) vcnt) = (ex2pre e0 (S vcnt)) ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e0 (S vcnt)))]
    | _ =>
        (ex2pre (EAddrOf e) vcnt) 
        = []
    end.
Proof.
    intros.
    destruct e; simpl; reflexivity.
Qed. 

(* 一些关于command list的引理 *)
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
    induction cl1; intros.
    + simpl.
      sets_unfold.
      split; intros.
      - right.
        exists s1.
        tauto.
      - destruct H.
        tauto.
        destruct H.
        destruct H.
        rewrite H.
        tauto.
    + simpl.
      sets_unfold.
      split; intros.
      - destruct H.
        --  left.
            left.
            tauto.
        --  destruct H as [s2].
            destruct H.
            pose proof IHcl1 cl2 s2.
            destruct H1.
            pose proof H1 H0.
            destruct H3.
            * left.
              right.
              exists s2.
              split; tauto.
            * right.
              sets_unfold in H3.
              destruct H3 as [s3].
              exists s3.
              split.
              exists s2.
              tauto.
              tauto.
      - destruct H.
        --  destruct H.
            left.
            tauto.
            destruct H as [s2].
            destruct H.
            right.
            exists s2.
            split.
            tauto.
            pose proof IHcl1 cl2 s2.
            destruct H1.
            assert ((Seval_comlist cl1).(err) s2 \/
            ((Seval_comlist cl1).(nrm) ∘ (Seval_comlist cl2).(err)) s2).
            {tauto. }
            tauto.
        --  destruct H as [s3].
            destruct H.
            destruct H as [s2].
            destruct H.
            right.
            exists s2.
            split.
            tauto.
            pose proof IHcl1 cl2 s2.
            destruct H2.
            assert ((Seval_comlist cl1).(err) s2 \/
            ((Seval_comlist cl1).(nrm) ∘ (Seval_comlist cl2).(err)) s2).
            {sets_unfold. right. exists s3. tauto. }
            tauto.
Qed.

Lemma eval_comlist_seq_inf : forall (cl1 cl2 : Scomlist) (s1 : state),
    (Seval_comlist (cl1 ++ cl2)).(inf) s1
    <-> ((Seval_comlist cl1).(inf) s1 \/
        Rels.concat (Seval_comlist cl1).(nrm) (Seval_comlist cl2).(inf) s1).
Proof.
    induction cl1; intros.
    + simpl.
      sets_unfold.
      split; intros.
      - right.
        exists s1.
        tauto.
      - destruct H.
        tauto.
        destruct H.
        destruct H.
        rewrite H.
        tauto.
    + simpl.
      sets_unfold.
      split; intros.
      - destruct H.
        --  left.
            left.
            tauto.
        --  destruct H as [s2].
            destruct H.
            pose proof IHcl1 cl2 s2.
            destruct H1.
            pose proof H1 H0.
            destruct H3.
            * left.
              right.
              exists s2.
              split; tauto.
            * right.
              sets_unfold in H3.
              destruct H3 as [s3].
              exists s3.
              split.
              exists s2.
              tauto.
              tauto.
      - destruct H.
        --  destruct H.
            left.
            tauto.
            destruct H as [s2].
            destruct H.
            right.
            exists s2.
            split.
            tauto.
            pose proof IHcl1 cl2 s2.
            destruct H1.
            assert ((Seval_comlist cl1).(inf) s2 \/
            ((Seval_comlist cl1).(nrm) ∘ (Seval_comlist cl2).(inf)) s2).
            {tauto. }
            tauto.
        --  destruct H as [s3].
            destruct H.
            destruct H as [s2].
            destruct H.
            right.
            exists s2.
            split.
            tauto.
            pose proof IHcl1 cl2 s2.
            destruct H2.
            assert ((Seval_comlist cl1).(inf) s2 \/
            ((Seval_comlist cl1).(nrm) ∘ (Seval_comlist cl2).(inf)) s2).
            {sets_unfold. right. exists s3. tauto. }
            tauto.
Qed.

Lemma midstate_4_nrm {NameX : Names} {NPX : NamesProperty}:
forall (vcnt : nat) (e1 e2 : expr),
  forall (ss1 ss14 : state),
  (Seval_comlist
   ((ex2pre e1 (S (S vcnt)) ++
     [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
     ex2pre e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))) ++
     [SCAsgnVar (nat2Sname (S vcnt))
        (ex2se e2
           (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))]))).(nrm) ss1 ss14
  ->
  exists (ss11 ss12 ss13 : state),
  (Seval_comlist (ex2pre e1 (S (S vcnt)))).(nrm) ss1 ss11
  /\ (Seval_comlist [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))]).(nrm) ss11 ss12
  /\ (Seval_comlist (ex2pre e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))).(nrm) ss12 ss13
  /\ (Seval_comlist [SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2
     (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))]).(nrm) ss13 ss14.
Proof.
  unfold com2comlist, com2pre, com2sc.
  intros.
  pose proof eval_comlist_seq_nrm (ex2pre e1 (S (S vcnt)))
  ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
  ex2pre e2
    (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))) ++
  [SCAsgnVar (nat2Sname (S vcnt))
     (ex2se e2
        (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))]) ss1 ss14.
  destruct H0.
  pose proof H0 H.
  sets_unfold in H2.
  destruct H2 as [ss11].
  destruct H2.
  pose proof eval_comlist_seq_nrm 
  ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))]) 
         (ex2pre e2
           (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))) ++
         [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2
               (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))]) ss11 ss14.
  destruct H4.
  pose proof H4 H3.
  sets_unfold in H6.
  destruct H6 as [ss12].
  destruct H6.
  pose proof eval_comlist_seq_nrm
    (ex2pre e2
           (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))
         [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2
               (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))] ss12 ss14.
  destruct H8.
  pose proof H8 H7.
  sets_unfold in H10.
  destruct H10 as [ss13].
  destruct H10.
  exists ss11, ss12, ss13.
  tauto.
Qed.




Lemma midstate_deref_nrm {NameX : Names}: forall (e : expr) (vcnt : nat) (s1 : state) (s3 : state),
    (Seval_comlist (ex2pre (EDeref e) vcnt)).(nrm) s1 s3
    -> 
    exists (s2 : state), 
    (Seval_comlist (ex2pre e (S vcnt))).(nrm) s1 s2
    /\ (Seval_comlist 
        [(SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt)))]).(nrm) s2 s3.
Proof.
    simpl.
    intros.
    pose proof eval_comlist_seq_nrm 
      (ex2pre e (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se e (S vcnt))]
      s1 s3.
    destruct H0.
    pose proof H0 H.
    sets_unfold in H2.
    tauto.
Qed.

Lemma midstate_unop {NameX : Names}: 
    forall (op : unop) 
    (e : expr) (vcnt : nat) (s1 : state) (s3 : state),
    (Seval_comlist (ex2pre (EUnop op e) vcnt)).(nrm) s1 s3
    -> 
    exists (s2 : state), 
    (Seval_comlist (ex2pre e (S vcnt))).(nrm) s1 s2
    /\ (Seval_comlist 
        [(SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt)))]).(nrm) s2 s3.
Proof.
    simpl.
    intros.
    pose proof eval_comlist_seq_nrm 
      (ex2pre e (S vcnt)) 
      [SCAsgnVar (nat2Sname vcnt)
      (ex2se e (S vcnt))]
      s1 s3.
    destruct H0.
    pose proof H0 H.
    sets_unfold in H2.
    tauto.
Qed.

Lemma some_val: forall (x y : int64), 
    Some (Vint x) = Some (Vint y) <-> x = y.
Proof.
    intros.
    split; intros.
    + injection H as ?.
      tauto.
    + rewrite H.
      reflexivity.
Qed.

Lemma correspond_prop2_unop {NameX : Names}: 
    forall (e : expr) (op : unop),
    (forall (vcnt : nat) (s1 ss1 ss2 : state),
    correspond s1 ss1 
    -> (Seval_comlist (ex2pre e vcnt)).(nrm) ss1 ss2 
    -> correspond s1 ss2)
    -> (forall (vcnt : nat) (s1 ss1 ss2 : state),
    correspond s1 ss1 ->
    (Seval_comlist (ex2pre (EUnop op e) vcnt)).(nrm) ss1 ss2 ->
    correspond s1 ss2).
Proof.
    simpl.
    intros.
    pose proof eval_comlist_seq_nrm 
        (ex2pre e (S vcnt))
        [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))] ss1 ss2.
    destruct H2.
    pose proof H2 H1.
    sets_unfold in H4.
    destruct H4 as [ss15].
    destruct H4.
    pose proof H (S vcnt) s1 ss1 ss15 H0 H4.
    pose proof correspond_prop1 vcnt (ex2se e (S vcnt)) s1 ss15 ss2 H6 H5.
    tauto.
Qed.

Lemma correspond_prop2_deref {NameX : Names}: 
    forall (e : expr),
    (forall (vcnt : nat) (s1 ss1 ss2 : state),
    correspond s1 ss1 
    -> (Seval_comlist (ex2pre e vcnt)).(nrm) ss1 ss2 
    -> correspond s1 ss2)
    -> (forall (vcnt : nat) (s1 ss1 ss2 : state),
    correspond s1 ss1 ->
    (Seval_comlist (ex2pre (EDeref e) vcnt)).(nrm) ss1 ss2 ->
    correspond s1 ss2).
Proof.
    simpl.
    intros.
    pose proof eval_comlist_seq_nrm 
        (ex2pre e (S vcnt))
        [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))] ss1 ss2.
    destruct H2.
    pose proof H2 H1.
    sets_unfold in H4.
    destruct H4 as [ss15].
    destruct H4.
    pose proof H (S vcnt) s1 ss1 ss15 H0 H4.
    pose proof correspond_prop1 vcnt (ex2se e (S vcnt)) s1 ss15 ss2 H6 H5.
    tauto.
Qed.

Lemma correspond_prop2_addrof {NameX : Names}: 
    forall (e : expr),
    (forall (vcnt : nat) (s1 ss1 ss2 : state),
    correspond s1 ss1 
    -> (Seval_comlist (ex2pre e vcnt)).(nrm) ss1 ss2 
    -> correspond s1 ss2)
    -> (forall (vcnt : nat) (s1 ss1 ss2 : state),
    correspond s1 ss1 ->
    (Seval_comlist (ex2pre (EAddrOf e) vcnt)).(nrm) ss1 ss2 ->
    correspond s1 ss2).
Proof.
    intros e.
    simpl.
    destruct e.
    + simpl; tauto.
    + simpl; tauto.
    + intros.
      simpl in H1.
      sets_unfold in H1.
      rewrite H1 in H0.
      tauto.
    + intros.
      simpl in H1.
      sets_unfold in H1.
      rewrite H1 in H0.
      tauto.
    + intros.
      pose proof H vcnt s1 ss1 ss2 H0.
      revert H1 H2.
      simpl.
      tauto.
    + intros.
      simpl in H1.
      sets_unfold in H1.
      rewrite H1 in H0.
      tauto.
Qed.

Lemma midstate_binop {NameX : Names}: 
  forall (vcnt : nat) (e1 e2 : expr) (ss1 ss14 : state),
  (Seval_comlist
          (ex2pre e1 (S (S vcnt)) ++
          [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
          ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) ++
          [SCAsgnVar (nat2Sname (S vcnt))
              (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1 ss14
  -> exists (ss11 ss12 ss13: state),
    (Seval_comlist (ex2pre e1 (S (S vcnt)))).(nrm) ss1 ss11
    /\ (Seval_comlist [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))]).(nrm) ss11 ss12
    /\ (Seval_comlist (ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))).(nrm) ss12 ss13
    /\ (Seval_comlist [SCAsgnVar (nat2Sname (S vcnt))
        (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))]).(nrm) ss13 ss14.
Proof.
  unfold com2comlist, com2pre, com2sc.
  intros.
  pose proof eval_comlist_seq_nrm (ex2pre e1 (S (S vcnt)))
  ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
  ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) ++
  [SCAsgnVar (nat2Sname (S vcnt))
     (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))]) ss1 ss14.
  destruct H0.
  pose proof H0 H.
  sets_unfold in H2.
  destruct H2 as [ss11].
  destruct H2.
  pose proof eval_comlist_seq_nrm 
    ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))]) 
    (ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) ++
    [SCAsgnVar (nat2Sname (S vcnt))
       (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))]) ss11 ss14.
  destruct H4.
  pose proof H4 H3.
  sets_unfold in H6.
  destruct H6 as [ss12].
  destruct H6.
  pose proof eval_comlist_seq_nrm
    (ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))
    ([SCAsgnVar (nat2Sname (S vcnt))
      (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))]) ss12 ss14.
  destruct H8.
  pose proof H8 H7.
  sets_unfold in H10.
  destruct H10 as [ss13].
  destruct H10.
  exists ss11, ss12, ss13.
  tauto.
Qed.

Lemma correspond_prop2_binop_op {NameX : Names}: 
  forall (e1 e2 : expr) (vcnt : nat) (s1 ss1 ss2 : state),
  (forall (vcnt : nat) (s1 ss1 ss2 : state),
  correspond s1 ss1 ->
  (Seval_comlist (ex2pre e1 vcnt)).(nrm) ss1 ss2 -> correspond s1 ss2)
  -> (forall (vcnt : nat) (s1 ss1 ss2 : state),
  correspond s1 ss1 ->
  (Seval_comlist (ex2pre e2 vcnt)).(nrm) ss1 ss2 -> correspond s1 ss2)
  -> correspond s1 ss1
  -> ((Seval_comlist
  (ex2pre e1 (S (S vcnt)) ++
   SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S(S vcnt)))
   :: ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm)
    ss1 ss2)
  -> correspond s1 ss2.
Proof.
  intros.
  assert (
    (Seval_comlist  
      (ex2pre e1 (S (S vcnt)) ++
        SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))
        :: ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) ++
        [SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))]))
    = (Seval_comlist  
    (ex2pre e1 (S (S vcnt)) ++
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      (ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) ++
      [SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))]))).
  {
    simpl.
    reflexivity.
  }
  rewrite H3 in H2.
  clear H3.
  pose proof midstate_binop vcnt e1 e2 ss1 ss2 H2.
  destruct H3 as [ss11 [ss12 [ss13 [H3 [H4 [H5 H6]]]]]].
  pose proof H (S (S vcnt)) s1 ss1 ss11 H1 H3.
  pose proof correspond_prop1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H7 H4.
  pose proof H0 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H8 H5.
  pose proof correspond_prop1 (S vcnt) (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss2 H9 H6.
  tauto.
Qed.

Lemma correspond_prop2_binop {NameX : Names}: 
    forall (e1 e2 : expr) (op : binop),
    (forall (vcnt : nat) (s1 ss1 ss2 : state),
    correspond s1 ss1 
    -> (Seval_comlist (ex2pre e1 vcnt)).(nrm) ss1 ss2 
    -> correspond s1 ss2)
    -> (forall (vcnt : nat) (s1 ss1 ss2 : state),
    correspond s1 ss1 
    -> (Seval_comlist (ex2pre e2 vcnt)).(nrm) ss1 ss2 
    -> correspond s1 ss2)
    -> (forall (vcnt : nat) (s1 ss1 ss2 : state),
    correspond s1 ss1 ->
    (Seval_comlist (ex2pre (EBinop op e1 e2) vcnt)).(nrm) ss1 ss2 ->
    correspond s1 ss2).
Proof.
  intros.
  pose proof ex2pre_binop vcnt e1 e2 op as H999.
  destruct op.
  + rewrite H999 in H2.
    pose proof eval_comlist_seq_nrm 
    (ex2pre e1 (S (S vcnt)))
         ([SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e1 (S (S vcnt)))] ++
         [SCIf (genSECV (S vcnt))
            [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 1))]
            (ex2pre e2
               (nat_add (S (S vcnt))
                  (length (ex2pre e1 (S (S vcnt))))) ++
             [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2
                   (nat_add (S (S vcnt))
                      (length (ex2pre e1 (S (S vcnt))))))] ++
             [SCIf (genSECV (S vcnt))
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 1))]
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 0))]])]) ss1 ss2.
    destruct H3.
    pose proof H3 H2.
    sets_unfold in H5.
    destruct H5 as [ss11].
    destruct H5.
    pose proof H (S (S vcnt)) s1 ss1 ss11 H1 H5.
    pose proof eval_comlist_seq_nrm
      [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e1 (S (S vcnt)))] 
         [SCIf (genSECV (S vcnt))
            [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 1))]
            (ex2pre e2
               (nat_add (S (S vcnt))
                  (length (ex2pre e1 (S (S vcnt))))) ++
             [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2
                   (nat_add (S (S vcnt))
                      (length (ex2pre e1 (S (S vcnt))))))] ++
             [SCIf (genSECV (S vcnt))
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 1))]
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 0))]])] ss11 ss2.
    destruct H8.
    pose proof H8 H6.
    sets_unfold in H10.
    destruct H10 as [ss12].
    destruct H10.
    pose proof correspond_prop1 (S vcnt) (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H7 H10.
    simpl in H11.
    sets_unfold in H11.
    destruct H11.
    destruct H11.
    rewrite H13 in H11.
    destruct H11.
    ++
    destruct H11.
    destruct H11.
    unfold test_true in H11.
    sets_unfold in H11.
    destruct H11.
    destruct H11.
    destruct H11.
    rewrite <- H15 in H14.
    destruct H14.
    destruct H14.
    rewrite H17 in H14.
    unfold asgn_deref_sem_nrm in H14.
    destruct H14 as [i1[i2]].
    destruct H14.
    destruct H18.
    destruct H19.
    destruct H20.
    destruct H21.
    revert H12.
    unfold correspond.
    intros.
    destruct H12.
    destruct H23.
    split.
    +++
    intros.
    pose proof H21 (name2Sname x3).
    pose proof H12 x3 i.
    rewrite H25 in H26.
    tauto.
    +++
    split.
    ++++
    intros.
    pose proof classic (i1 = a).
    destruct H26.
    -
    rewrite <- H14 in H26.
    pose proof H24 vcnt.
    rewrite H26 in H27.
    rewrite H25 in H27.
    destruct H27.
    discriminate.
    -
    pose proof H22 a H26.
    pose proof H23 a v H25.
    rewrite H27 in H28.
    tauto.
    ++++
    intros.
    pose proof H21 (nat2Sname vcnt0).
    rewrite <- H25.
    pose proof H24 vcnt0.
    split; [tauto|].
    pose proof classic (i1 = ss12.(env) (nat2Sname vcnt0)).
    destruct H27.
    -
    rewrite <- H27.
    rewrite H20.
    discriminate.
    -
    pose proof H22 (ss12.(env) (nat2Sname vcnt0)) H27.
    rewrite <- H28.
    tauto.
    ++
    destruct H11.
    destruct H11.
    unfold test_false in H11.
    sets_unfold in H11.
    destruct H11.
    rewrite <- H15 in H14.
    pose proof eval_comlist_seq_nrm
      (ex2pre e2
            (S
               (S
                  (nat_add vcnt
                     (length (ex2pre e1 (S (S vcnt))))))))
          ([SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2
                (S
                   (S
                      (nat_add vcnt
                         (length (ex2pre e1 (S (S vcnt)))))))),
          SCIf (genSECV (S vcnt))
            [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 1))]
            [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 0))]]) ss12 ss2.
    destruct H16.
    pose proof H16 H14.
    sets_unfold in H18.
    destruct H18 as [ss13].
    destruct H18.
    pose proof H0 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H12 H18.
    pose proof eval_comlist_seq_nrm 
      [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2
               (S
                  (S
                     (nat_add vcnt
                        (length (ex2pre e1 (S (S vcnt))))))))]
         [SCIf (genSECV (S vcnt))
           [SCAsgnVar (nat2Sname vcnt)
              (SEConstOrVar (SEConst 1))]
           [SCAsgnVar (nat2Sname vcnt)
              (SEConstOrVar (SEConst 0))]] ss13 ss2.
    destruct H21.
    pose proof H21 H19.
    sets_unfold in H23.
    destruct H23 as [ss14].
    destruct H23.
    pose proof correspond_prop1 (S vcnt) (ex2se e2
    (S
       (S
          (nat_add vcnt
             (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss14 H20 H23.
    simpl in H24.
    sets_unfold in H24.
    destruct H24.
    destruct H24.
    rewrite H26 in H24.
    destruct H24.
    +++
    destruct H24.
    destruct H24.
    unfold test_true in H24.
    sets_unfold in H24.
    destruct H24.
    rewrite <- H28 in H27.
    destruct H27.
    destruct H27.
    rewrite H29 in H27.
    unfold asgn_deref_sem_nrm in H27.
    destruct H27 as [i1[i2]].
    destruct H27.
    destruct H30.
    destruct H31.
    destruct H32.
    destruct H33.
    revert H25.
    unfold correspond.
    intros.
    destruct H25.
    destruct H35.
    split.
    ++++
    intros.
    pose proof H33 (name2Sname x4).
    pose proof H25 x4 i.
    rewrite <- H37.
    tauto.
    ++++
    split.
    -
    intros.
    pose proof H35 a v H37.
    pose proof classic (i1 = a).
    destruct H39.
    --
    rewrite <- H39 in H37.
    rewrite <- H27 in H37.
    pose proof H36 vcnt.
    rewrite H37 in H40.
    destruct H40.
    discriminate.
    --
    pose proof H34 a H39.
    rewrite H40 in H38.
    tauto.
    -
    intros.
    pose proof H36 vcnt0.
    pose proof H33 (nat2Sname vcnt0).
    rewrite <- H38.
    split; [tauto|].
    pose proof classic (i1 = (ss14.(env) (nat2Sname vcnt0))).
    destruct H39.
    --
    rewrite <- H39.
    rewrite H32.
    discriminate.
    --
    pose proof H34 (ss14.(env) (nat2Sname vcnt0)) H39.
    rewrite <- H40.
    tauto.
    +++
    destruct H24.
    destruct H24.
    unfold test_false in H24.
    sets_unfold in H24.
    destruct H24.
    rewrite <- H28 in H27.
    destruct H27.
    destruct H27.
    rewrite H29 in H27.
    unfold asgn_deref_sem_nrm in H27.
    destruct H27 as [i1[i2]].
    destruct H27.
    destruct H30.
    destruct H31.
    destruct H32.
    destruct H33.
    revert H25.
    unfold correspond.
    intros.
    destruct H25.
    destruct H35.
    split.
    ++++
    intros.
    pose proof H33 (name2Sname x4).
    pose proof H25 x4 i.
    rewrite <- H37.
    tauto.
    ++++
    split.
    -
    intros.
    pose proof H35 a v H37.
    pose proof classic (i1 = a).
    destruct H39.
    --
    rewrite <- H39 in H37.
    rewrite <- H27 in H37.
    pose proof H36 vcnt.
    rewrite H37 in H40.
    destruct H40.
    discriminate.
    --
    pose proof H34 a H39.
    rewrite H40 in H38.
    tauto.
    -
    intros.
    pose proof H36 vcnt0.
    pose proof H33 (nat2Sname vcnt0).
    rewrite <- H38.
    split; [tauto|].
    pose proof classic (i1 = (ss14.(env) (nat2Sname vcnt0))).
    destruct H39.
    --
    rewrite <- H39.
    rewrite H32.
    discriminate.
    --
    pose proof H34 (ss14.(env) (nat2Sname vcnt0)) H39.
    rewrite <- H40.
    tauto.
  + rewrite H999 in H2.
    pose proof eval_comlist_seq_nrm 
    (ex2pre e1 (S (S vcnt)))
         ([SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e1 (S (S vcnt)))] ++
         [SCIf (genSECV (S vcnt))
            (ex2pre e2
               (nat_add (S (S vcnt))
                  (length (ex2pre e1 (S (S vcnt))))) ++
             [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2
                   (nat_add (S (S vcnt))
                      (length (ex2pre e1 (S (S vcnt))))))] ++
             [SCIf (genSECV (S vcnt))
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 1))]
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 0))]])
            [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 0))]]) ss1 ss2.
    destruct H3.
    pose proof H3 H2.
    sets_unfold in H5.
    destruct H5 as [ss11].
    destruct H5.
    pose proof H (S (S vcnt)) s1 ss1 ss11 H1 H5.
    pose proof eval_comlist_seq_nrm
      [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e1 (S (S vcnt)))] 
         [SCIf (genSECV (S vcnt))
            (ex2pre e2
               (nat_add (S (S vcnt))
                  (length (ex2pre e1 (S (S vcnt))))) ++
             [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2
                   (nat_add (S (S vcnt))
                      (length (ex2pre e1 (S (S vcnt))))))] ++
             [SCIf (genSECV (S vcnt))
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 1))]
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 0))]])
            [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 0))]] ss11 ss2.
    destruct H8.
    pose proof H8 H6.
    sets_unfold in H10.
    destruct H10 as [ss12].
    destruct H10.
    pose proof correspond_prop1 (S vcnt) (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H7 H10.
    simpl in H11.
    sets_unfold in H11.
    destruct H11.
    destruct H11.
    rewrite H13 in H11.
    destruct H11.
    ++
    destruct H11.
    destruct H11.
    unfold test_false in H11.
    sets_unfold in H11.
    destruct H11.
    rewrite <- H15 in H14.
    pose proof eval_comlist_seq_nrm
      (ex2pre e2
            (S
               (S
                  (nat_add vcnt
                     (length (ex2pre e1 (S (S vcnt))))))))
          ([SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2
                (S
                   (S
                      (nat_add vcnt
                         (length (ex2pre e1 (S (S vcnt)))))))),
          SCIf (genSECV (S vcnt))
            [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 1))]
            [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 0))]]) ss12 ss2.
    destruct H16.
    pose proof H16 H14.
    sets_unfold in H18.
    destruct H18 as [ss13].
    destruct H18.
    pose proof H0 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H12 H18.
    pose proof eval_comlist_seq_nrm 
      [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2
               (S
                  (S
                     (nat_add vcnt
                        (length (ex2pre e1 (S (S vcnt))))))))]
         [SCIf (genSECV (S vcnt))
           [SCAsgnVar (nat2Sname vcnt)
              (SEConstOrVar (SEConst 1))]
           [SCAsgnVar (nat2Sname vcnt)
              (SEConstOrVar (SEConst 0))]] ss13 ss2.
    destruct H21.
    pose proof H21 H19.
    sets_unfold in H23.
    destruct H23 as [ss14].
    destruct H23.
    pose proof correspond_prop1 (S vcnt) (ex2se e2
    (S
       (S
          (nat_add vcnt
             (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss14 H20 H23.
    simpl in H24.
    sets_unfold in H24.
    destruct H24.
    destruct H24.
    rewrite H26 in H24.
    destruct H24.
    +++
    destruct H24.
    destruct H24.
    unfold test_true in H24.
    sets_unfold in H24.
    destruct H24.
    rewrite <- H28 in H27.
    destruct H27.
    destruct H27.
    rewrite H29 in H27.
    unfold asgn_deref_sem_nrm in H27.
    destruct H27 as [i1[i2]].
    destruct H27.
    destruct H30.
    destruct H31.
    destruct H32.
    destruct H33.
    revert H25.
    unfold correspond.
    intros.
    destruct H25.
    destruct H35.
    split.
    ++++
    intros.
    pose proof H33 (name2Sname x4).
    pose proof H25 x4 i.
    rewrite <- H37.
    tauto.
    ++++
    split.
    -
    intros.
    pose proof H35 a v H37.
    pose proof classic (i1 = a).
    destruct H39.
    --
    rewrite <- H39 in H37.
    rewrite <- H27 in H37.
    pose proof H36 vcnt.
    rewrite H37 in H40.
    destruct H40.
    discriminate.
    --
    pose proof H34 a H39.
    rewrite H40 in H38.
    tauto.
    -
    intros.
    pose proof H36 vcnt0.
    pose proof H33 (nat2Sname vcnt0).
    rewrite <- H38.
    split; [tauto|].
    pose proof classic (i1 = (ss14.(env) (nat2Sname vcnt0))).
    destruct H39.
    --
    rewrite <- H39.
    rewrite H32.
    discriminate.
    --
    pose proof H34 (ss14.(env) (nat2Sname vcnt0)) H39.
    rewrite <- H40.
    tauto.
    +++
    destruct H24.
    destruct H24.
    unfold test_false in H24.
    sets_unfold in H24.
    destruct H24.
    rewrite <- H28 in H27.
    destruct H27.
    destruct H27.
    rewrite H29 in H27.
    unfold asgn_deref_sem_nrm in H27.
    destruct H27 as [i1[i2]].
    destruct H27.
    destruct H30.
    destruct H31.
    destruct H32.
    destruct H33.
    revert H25.
    unfold correspond.
    intros.
    destruct H25.
    destruct H35.
    split.
    ++++
    intros.
    pose proof H33 (name2Sname x4).
    pose proof H25 x4 i.
    rewrite <- H37.
    tauto.
    ++++
    split.
    -
    intros.
    pose proof H35 a v H37.
    pose proof classic (i1 = a).
    destruct H39.
    --
    rewrite <- H39 in H37.
    rewrite <- H27 in H37.
    pose proof H36 vcnt.
    rewrite H37 in H40.
    destruct H40.
    discriminate.
    --
    pose proof H34 a H39.
    rewrite H40 in H38.
    tauto.
    -
    intros.
    pose proof H36 vcnt0.
    pose proof H33 (nat2Sname vcnt0).
    rewrite <- H38.
    split; [tauto|].
    pose proof classic (i1 = (ss14.(env) (nat2Sname vcnt0))).
    destruct H39.
    --
    rewrite <- H39.
    rewrite H32.
    discriminate.
    --
    pose proof H34 (ss14.(env) (nat2Sname vcnt0)) H39.
    rewrite <- H40.
    tauto.
    ++
    destruct H11.
    destruct H11.
    unfold test_true in H11.
    sets_unfold in H11.
    destruct H11.
    destruct H11.
    destruct H11.
    rewrite <- H15 in H14.
    destruct H14.
    destruct H14.
    rewrite H17 in H14.
    unfold asgn_deref_sem_nrm in H14.
    destruct H14 as [i1[i2]].
    destruct H14.
    destruct H18.
    destruct H19.
    destruct H20.
    destruct H21.
    revert H12.
    unfold correspond.
    intros.
    destruct H12.
    destruct H23.
    split.
    +++
    intros.
    pose proof H21 (name2Sname x3).
    pose proof H12 x3 i.
    rewrite H25 in H26.
    tauto.
    +++
    split.
    ++++
    intros.
    pose proof classic (i1 = a).
    destruct H26.
    -
    rewrite <- H14 in H26.
    pose proof H24 vcnt.
    rewrite H26 in H27.
    rewrite H25 in H27.
    destruct H27.
    discriminate.
    -
    pose proof H22 a H26.
    pose proof H23 a v H25.
    rewrite H27 in H28.
    tauto.
    ++++
    intros.
    pose proof H21 (nat2Sname vcnt0).
    rewrite <- H25.
    pose proof H24 vcnt0.
    split; [tauto|].
    pose proof classic (i1 = ss12.(env) (nat2Sname vcnt0)).
    destruct H27.
    -
    rewrite <- H27.
    rewrite H20.
    discriminate.
    -
    pose proof H22 (ss12.(env) (nat2Sname vcnt0)) H27.
    rewrite <- H28.
    tauto.
  + pose proof correspond_prop2_binop_op e1 e2 vcnt s1 ss1 ss2.
    tauto.
  + pose proof correspond_prop2_binop_op e1 e2 vcnt s1 ss1 ss2.
    tauto.
  + pose proof correspond_prop2_binop_op e1 e2 vcnt s1 ss1 ss2.
    tauto.
  + pose proof correspond_prop2_binop_op e1 e2 vcnt s1 ss1 ss2.
    tauto.
  + pose proof correspond_prop2_binop_op e1 e2 vcnt s1 ss1 ss2.
    tauto.
  + pose proof correspond_prop2_binop_op e1 e2 vcnt s1 ss1 ss2.
    tauto.
  + pose proof correspond_prop2_binop_op e1 e2 vcnt s1 ss1 ss2.
    tauto.
  + pose proof correspond_prop2_binop_op e1 e2 vcnt s1 ss1 ss2.
    tauto.
  + pose proof correspond_prop2_binop_op e1 e2 vcnt s1 ss1 ss2.
    tauto.
  + pose proof correspond_prop2_binop_op e1 e2 vcnt s1 ss1 ss2.
    tauto.
  + pose proof correspond_prop2_binop_op e1 e2 vcnt s1 ss1 ss2.
    tauto.
Qed.


Lemma correspond_prop2 {NameX : Names}: 
    forall (e : expr) (vcnt : nat) (s1 ss1 ss2 : state),
        correspond s1 ss1
        -> (Seval_comlist (ex2pre e vcnt)).(nrm) ss1 ss2
        -> correspond s1 ss2.
Proof.
    intros e.
    induction e.
    + simpl.
      sets_unfold.
      intros.
      rewrite <- H0.
      tauto.
    + simpl.
      sets_unfold.
      intros.
      rewrite <- H0.
      tauto.
    + pose proof correspond_prop2_binop e1 e2 op IHe1 IHe2; tauto.
    + pose proof correspond_prop2_unop e op IHe; tauto.
    + pose proof correspond_prop2_deref e IHe; tauto.
    + pose proof correspond_prop2_addrof e IHe; tauto.
Qed.

Lemma midstate_cor_4_nrm {NameX : Names} {NPX : NamesProperty}:
forall (vcnt : nat) (e1 e2 : expr),
  forall (s1 ss1 ss14 : state),
  (Seval_comlist
   ((ex2pre e1 (S (S vcnt)) ++
     [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
     ex2pre e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))) ++
     [SCAsgnVar (nat2Sname (S vcnt))
        (ex2se e2
           (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))]))).(nrm) ss1 ss14
  -> correspond s1 ss1
  ->
  exists (ss11 ss12 ss13 : state),
  (Seval_comlist (ex2pre e1 (S (S vcnt)))).(nrm) ss1 ss11
  /\ (Seval_comlist [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))]).(nrm) ss11 ss12
  /\ (Seval_comlist (ex2pre e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))).(nrm) ss12 ss13
  /\ (Seval_comlist [SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2
     (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))]).(nrm) ss13 ss14
  /\ correspond s1 ss11
  /\ correspond s1 ss12
  /\ correspond s1 ss13
  /\ correspond s1 ss14.
Proof.
  intros.
  pose proof midstate_4_nrm vcnt e1 e2 ss1 ss14 H.
  destruct H1 as [ss11 [ss12 [ss13 [? [? [? ]]]]]].
  exists ss11, ss12, ss13.
  pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H0 H1.
  pose proof correspond_prop1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H5 H2.
  pose proof correspond_prop2 e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))) s1 ss12 ss13 H6 H3.
  pose proof correspond_prop1 (S vcnt) (ex2se e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt)))))) s1 ss13 ss14 H7 H4.
  tauto.
Qed.

Lemma asgn_pre {NameX : Names}: forall (x : var_name) (e : expr) (vcnt : nat),
    com2pre (CAsgnVar x e) vcnt = ex2pre e vcnt.
Proof.
    intros.
    simpl.
    tauto.
Qed.

Lemma asgn_sc {NameX : Names}: forall (x : var_name) (e : expr) (vcnt : nat),
    com2sc (CAsgnVar x e) vcnt = [SCAsgnVar (name2Sname x) (ex2se e vcnt)].
Proof.
    intros.
    simpl.
    tauto.
Qed.

Lemma correspond_prop3_asgnvar {NameX : Names}: 
    forall (x : var_name) (e : expr) (vcnt : nat) (s1 ss1 ss2 : state),
        correspond s1 ss1
        -> (Seval_comlist (com2pre (CAsgnVar x e) vcnt)).(nrm) ss1 ss2
        -> correspond s1 ss2.
Proof.
    intros.
    pose proof asgn_pre x e vcnt.
    rewrite H1 in H0.
    pose proof correspond_prop2 e vcnt s1 ss1 ss2 H H0.
    tauto.
Qed.

Lemma asgn_vcnt_ex2se_nrm_prop {NameX : Names}: 
    forall (se : Sexpr) (vcnt : nat) (s2 s3 : state),
    (Seval_comlist
        [SCAsgnVar (nat2Sname vcnt) se]).(nrm) s2 s3
        -> (Seval_r (genSECV vcnt)).(nrm) s3 ⊆ (Seval_r se).(nrm) s2.
Proof.
    simpl.
    unfold Seval_comlist, seq_sem, asgn_var_sem, asgn_deref_sem, asgn_deref_sem_nrm, skip_sem, CDenote.nrm.
    unfold var_sem_l.
    simpl.
    sets_unfold.
    unfold deref_sem_nrm.
    intros.
    destruct H.
    destruct H.
    rewrite H1 in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H2.
    destruct H3.
    destruct H4.
    destruct H5.
    destruct H0.
    destruct H0.
    pose proof H5 (nat2Sname vcnt).
    rewrite H8 in H.
    rewrite H in H0.
    rewrite H0 in H4.
    rewrite H4 in H7.
    pose proof some_val x1 a.
    destruct H9.
    pose proof H9 H7.
    rewrite <- H11.
    tauto.
Qed.

Lemma asgn_vcnt_ex2se_err_prop {NameX : Names}: 
    forall (se : Sexpr) (vcnt : nat) (s ss2 : state),
        correspond s ss2 -> 
        (Seval_comlist
        [SCAsgnVar (nat2Sname vcnt) se]).(err) ss2
        -> (Seval_r se).(err) ss2.
Proof.
  unfold Seval_comlist, seq_sem, asgn_var_sem, asgn_deref_sem, skip_sem, asgn_deref_sem_nrm, asgn_deref_sem_err,
      CDenote.nrm, CDenote.err, var_sem_l.
  sets_unfold.
  simpl.
  unfold correspond.
  intros e vcnt s ss2 H0 H.
  destruct H0 as [H10 [H11 H0]].
  destruct H as [H | H].
  destruct H as [H | H].
  destruct H as [H | H].
  unfold EDenote.err in H.
  tauto.
  tauto.
  destruct H.
  unfold EDenote.nrm in H.
  destruct H.
  pose proof H0 vcnt.
  destruct H2.
  rewrite <- H1 in H3.
  rewrite <- H in H3.
  assert (ss2.(mem) (ss2.(env) (nat2Sname vcnt)) =
  ss2.(mem) (ss2.(env) (nat2Sname vcnt))). {reflexivity. }
  congruence.
  destruct H.
  destruct H.
  tauto.
Qed.

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
        destruct H3 as [H3 Hv].
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

Lemma deref_nrm_prop1 {NameX : Names}: forall (s ss : state) (x : var_name) (a : int64),
    correspond s ss
    -> (Seval_r (SEDeref (SEVar (name2Sname x)))).(nrm) ss a
    -> (eval_r (EDeref (EVar x))).(nrm) s a \/ (eval_r (EDeref (EVar x))).(err) s.
Proof.
    simpl.
    unfold correspond, deref_sem_nrm, deref_sem_err.
    sets_unfold.
    intros ? ? ? ? H H10.
    destruct H as [H0 [H1 H2]].
    destruct H10 as [i2 [[i1 [H3 H4]] H5]].
    pose proof mem_split s i1.
    pose proof H0 x i1 as H6.
    destruct H6 as [H6 H7].
    pose proof H7 H3.
    destruct H.
    + destruct H as [v].
      pose proof H1 i1 v H.
      pose proof mem_split s i2.
      destruct H10.
      - destruct H10 as [v0].
        left.
        exists i2.
        pose proof H1 i2 v0 H10.
        rewrite <- H11 in H10.
        rewrite <- H9 in H.
        rewrite H4 in H.
        rewrite H5 in H10.
        split.
        exists i1.
        split; tauto.
        tauto.
      - right.
        right.
        exists i2.
        split.
        exists i1.
        rewrite <- H9 in H.
        rewrite H4 in H.
        split; tauto.
        left.
        tauto.
    + right.
      left.
      right.
      exists i1.
      split.
      tauto.    
      tauto.
Qed.


(* 定义精化关系 *)
Definition Serefine_nrm_l {NameX : Names} (cl : Scomlist) (se : Sexpr) (e : expr): Prop :=
    forall (s1 ss1 ss2 : state) (a : int64),
        correspond s1 ss1 ->
        (Seval_comlist cl).(nrm) ss1 ss2 ->
        (Seval_l se).(nrm) ss2 a -> 
        ((eval_l e).(nrm) s1 a \/ (eval_l e).(err) s1).

Definition Serefine_nrm_r {NameX : Names} (cl : Scomlist) (se : Sexpr) (e : expr): Prop :=
    forall (s1 ss1 ss2 : state) (a : int64),
        correspond s1 ss1 ->
        (Seval_comlist cl).(nrm) ss1 ss2 ->
        (Seval_r se).(nrm) ss2 a -> 
        ((eval_r e).(nrm) s1 a \/ (eval_r e).(err) s1).

Definition Serefine_nrm {NameX : Names} (cl : Scomlist) (se : Sexpr) (e : expr): Prop :=
    Serefine_nrm_l cl se e
    /\ Serefine_nrm_r cl se e.

Definition Serefine_err1 {NameX : Names} (cl : Scomlist) (se : Sexpr) (e : expr): Prop :=
    forall (s1 ss1 : state),
        correspond s1 ss1 
        -> (Seval_comlist cl).(err) ss1 
        -> (eval_l e).(err) s1 /\ (eval_r e).(err) s1.

Definition Serefine_err2_l {NameX : Names} (cl : Scomlist) (se : Sexpr) (e : expr): Prop :=
    forall (s1 ss1 ss2 : state),
        correspond s1 ss1
        -> (Seval_comlist cl).(nrm) ss1 ss2
        -> (Seval_l se).(err) ss2
        -> (eval_l e).(err) s1.

Definition Serefine_err2_r {NameX : Names} (cl : Scomlist) (se : Sexpr) (e : expr): Prop :=
    forall (s1 ss1 ss2 : state),
        correspond s1 ss1
        -> (Seval_comlist cl).(nrm) ss1 ss2
        -> (Seval_r se).(err) ss2
        -> (eval_r e).(err) s1.

Definition Serefine_err {NameX : Names} (cl : Scomlist) (se : Sexpr) (e : expr): Prop :=
    Serefine_err1 cl se e
    /\ Serefine_err2_l cl se e
    /\ Serefine_err2_r cl se e.

Record Serefine {NameX : Names} (cl : Scomlist) (se : Sexpr) (e : expr): Prop := {
    nrm_Serefine:
        Serefine_nrm cl se e;
    err_Serefine:
        Serefine_err cl se e;
    }.


Lemma greater_vcnt2 {NameX : Names} {NPX : NamesProperty}:
  forall (vcnt : nat) (ss1 ss2 :state) (e1 e2 : expr),
    (Seval_comlist [(SCAsgnVar (nat2Sname (S vcnt)) 
          (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))))]).(nrm) ss1 ss2
    -> ss1.(mem) (ss1.(env) (nat2Sname vcnt)) = ss2.(mem) (ss2.(env) (nat2Sname vcnt)).
Proof.
  simpl.
  unfold asgn_deref_sem_nrm.
  sets_unfold.
  intros.
  destruct H.
  destruct H.
  rewrite H0 in H.
  destruct H as [?[?[?[?[?[?[?]]]]]]].
  pose proof H4 (nat2Sname vcnt).
  rewrite H6.
  pose proof classic (x0 = (ss2.(env) (nat2Sname vcnt))).
  destruct H7.
  +
  rewrite H7 in H.
  rewrite <- H in H6.
  pose proof trans_prop2 vcnt (S vcnt) ss1.
  destruct H8.
  pose proof H9 H6.
  lia.
  +
  pose proof H5 (ss2.(env) (nat2Sname vcnt)) H7.
  tauto.
Qed.

Lemma greater_vcnt2_aux_aux: 
  forall (x vcnt : nat),
    vcnt = S (nat_add x vcnt) -> False.
Proof.
  unfold nat_add.
  induction vcnt.
  + simpl.
    lia.
  + simpl.
    intros.
    assert (forall (n : nat), S n = Nat.add 1%nat n).
    {
      intros.
      simpl.
      tauto.
    }
    pose proof H0 vcnt.
    pose proof H0 (x + (1%nat + vcnt))%nat.
    rewrite H1 in H.
    rewrite H2 in H.
    pose proof Nat.add_cancel_l vcnt (x + (1 + vcnt)%nat) 1%nat.
    destruct H3.
    pose proof H3 H.
    pose proof H0 (x + vcnt)%nat.
    rewrite H6 in IHvcnt.
    assert ((1 + (x + vcnt))%nat = (x + (1 + vcnt))%nat).
    {
      pose proof Nat.add_assoc 1 x vcnt.
      pose proof Nat.add_assoc x 1 vcnt.
      pose proof Nat.add_comm 1 x.
      rewrite H7.
      rewrite H8.
      rewrite H9.
      tauto.
    }
    rewrite <- H7 in H5.
    tauto.
Qed.

Lemma greater_vcnt2_aux {NameX : Names} {NPX : NamesProperty}:
  forall (vcnt : nat) (ss1 ss2 :state) (e : expr),
    (exists x y : nat,
    (Seval_comlist [(SCAsgnVar (nat2Sname (S (nat_add x vcnt))) 
          (ex2se e (S (S (nat_add y vcnt)))))]).(nrm) ss1 ss2)
    -> ss1.(mem) (ss1.(env) (nat2Sname vcnt)) = ss2.(mem) (ss2.(env) (nat2Sname vcnt)).
Proof.
  simpl.
  unfold asgn_deref_sem_nrm.
  sets_unfold.
  intros.
  destruct H.
  destruct H.
  destruct H.
  destruct H.
  rewrite H0 in H.
  destruct H as [?[?[?[?[?[?[?]]]]]]].
  pose proof H4 (nat2Sname vcnt).
  rewrite H6.
  pose proof classic (x2 = (ss2.(env) (nat2Sname vcnt))).
  destruct H7.
  +
  rewrite H7 in H.
  rewrite <- H in H6.
  pose proof trans_prop2 vcnt (S (nat_add x vcnt)) ss1.
  destruct H8.
  pose proof H9 H6.
  pose proof greater_vcnt2_aux_aux x vcnt H10.
  tauto.
  +
  pose proof H5 (ss2.(env) (nat2Sname vcnt)) H7.
  tauto.
Qed.

Lemma greater_vcnt1_aux {NameX : Names} {NPX : NamesProperty}:
  forall (vcnt : nat) (ss1 ss2 :state) (e : expr),
    (exists x : nat, (Seval_comlist 
      (ex2pre e (S (nat_add x vcnt)))).(nrm) ss1 ss2)
    -> ss1.(mem) (ss1.(env) (nat2Sname vcnt)) = ss2.(mem) (ss2.(env) (nat2Sname vcnt)).
Proof.
  intros.
  revert ss1 ss2 H.
  induction e.
  + simpl.
    sets_unfold.
    intros.
    destruct H.
    rewrite H.
    tauto.
  + intros.
    simpl in H.
    sets_unfold in H.
    destruct H.
    rewrite H.
    tauto.
  + intros.
    destruct H.
    pose proof ex2pre_binop (S (nat_add x vcnt)) e1 e2 op.
    destruct op; rewrite H0 in H.
    -
    pose proof eval_comlist_seq_nrm
      (ex2pre e1 (S (S (S (nat_add x vcnt)))))
        ([SCAsgnVar (nat2Sname (S (S (nat_add x vcnt))))
           (ex2se e1 (S (S (S (nat_add x vcnt)))))] ++
        [SCIf (genSECV (S (S (nat_add x vcnt))))
           [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
              (SEConstOrVar (SEConst 1))]
           (ex2pre e2
              (nat_add (S (S (S (nat_add x vcnt))))
                 (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))) ++
            [SCAsgnVar (nat2Sname (S (S (nat_add x vcnt))))
               (ex2se e2
                  (nat_add (S (S (S (nat_add x vcnt))))
                     (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))))] ++
            [SCIf (genSECV (S (S (nat_add x vcnt))))
               [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
                  (SEConstOrVar (SEConst 1))]
               [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
                  (SEConstOrVar (SEConst 0))]])]) ss1 ss2.
    destruct H1.
    pose proof H1 H.
    sets_unfold in H3.
    destruct H3 as [ss11].
    destruct H3.
    assert (exists x : nat,
        (Seval_comlist (ex2pre e1 (S (nat_add x vcnt)))).(nrm) ss1 ss11).
    {
      exists (S (S x)).
      tauto.
    }
    pose proof IHe1 ss1 ss11 H5.
    rewrite H6.
    pose proof eval_comlist_seq_nrm
       [SCAsgnVar (nat2Sname (S (S (nat_add x vcnt))))
           (ex2se e1 (S (S (S (nat_add x vcnt)))))] 
        ([SCIf (genSECV (S (S (nat_add x vcnt))))
           [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
              (SEConstOrVar (SEConst 1))]
           (ex2pre e2
              (nat_add (S (S (S (nat_add x vcnt))))
                 (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))) ++
            [SCAsgnVar (nat2Sname (S (S (nat_add x vcnt))))
               (ex2se e2
                  (nat_add (S (S (S (nat_add x vcnt))))
                     (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))))] ++
            [SCIf (genSECV (S (S (nat_add x vcnt))))
               [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
                  (SEConstOrVar (SEConst 1))]
               [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
                  (SEConstOrVar (SEConst 0))]])]) ss11 ss2.
    destruct H7.
    pose proof H7 H4.
    sets_unfold in H9.
    destruct H9 as [ss12].
    destruct H9.
    assert (exists x y : nat,
         (Seval_comlist
            [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
               (ex2se e1 (S (S (nat_add y vcnt))))]).(nrm) ss11
           ss12).
    {
      exists (S x), (S x).
      revert H9.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss11 ss12 e1 H11.
    rewrite H12.
    simpl in H10.
    sets_unfold in H10.
    destruct H10.
    destruct H10.
    rewrite H13 in H10.
    destruct H10.
    --
    destruct H10.
    destruct H10.
    unfold test_true in H10.
    sets_unfold in H10.
    destruct H10.
    rewrite <- H15 in H14.
    destruct H14.
    destruct H14.
    rewrite H16 in H14.
    unfold asgn_deref_sem_nrm in H14.
    destruct H14 as [i1[i2[?[?[?[?[?]]]]]]].
    pose proof H20 (nat2Sname vcnt).
    pose proof classic (i1 = (ss12.(env) (nat2Sname vcnt))).
    destruct H23.
    ---
    rewrite H23 in H14.
    pose proof trans_prop2 (S (nat_add x vcnt)) vcnt ss12.
    destruct H24.
    pose proof H25 H14.
    pose proof greater_vcnt2_aux_aux x vcnt.
    destruct H27.
    rewrite H26.
    tauto.
    ---
    pose proof H21 (ss12.(env) (nat2Sname vcnt)) H23.
    rewrite H24.
    rewrite H22.
    tauto.
    --
    destruct H10.
    destruct H10.
    unfold test_false in H10.
    sets_unfold in H10.
    destruct H10.
    rewrite <- H15 in H14.
    pose proof eval_comlist_seq_nrm 
      (ex2pre e2
            (S
               (S
                  (S
                     (nat_add (nat_add x vcnt)
                        (length
                           (ex2pre e1
                              (S (S (S (nat_add x vcnt)))))))))))
          [SCAsgnVar (nat2Sname (S (S (nat_add x vcnt))))
             (ex2se e2
                (S
                   (S
                      (S
                         (nat_add (nat_add x vcnt)
                            (length
                               (ex2pre e1
                                  (S (S (S (nat_add x vcnt))))))))))),
          SCIf (genSECV (S (S (nat_add x vcnt))))
            [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
               (SEConstOrVar (SEConst 1))]
            [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
               (SEConstOrVar (SEConst 0))]] ss12 ss2.
    destruct H16.
    pose proof H16 H14.
    sets_unfold in H18.
    destruct H18 as [ss13].
    destruct H18.
    assert (exists x : nat,
    (Seval_comlist (ex2pre e2 (S (nat_add x vcnt)))).(nrm)
      ss12 ss13).
    {
      exists (S (S (nat_add x (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))))).
      revert H18.
      simpl.
      unfold nat_add.
      pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite <- H18.
      pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite H20.
      pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
      rewrite H21.
      tauto.
    }
    pose proof IHe2 ss12 ss13 H20.
    rewrite H21.
    pose proof eval_comlist_seq_nrm
      [SCAsgnVar (nat2Sname (S (S (nat_add x vcnt))))
            (ex2se e2
               (S
                  (S
                     (S
                        (nat_add (nat_add x vcnt)
                           (length
                              (ex2pre e1
                                 (S (S (S (nat_add x vcnt)))))))))))]
         [SCIf (genSECV (S (S (nat_add x vcnt))))
           [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
              (SEConstOrVar (SEConst 1))]
           [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
              (SEConstOrVar (SEConst 0))]] ss13 ss2.
    destruct H22.
    pose proof H22 H19.
    sets_unfold in H24.
    destruct H24 as [ss14].
    destruct H24.
    assert (exists x y : nat,
    (Seval_comlist
       [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
          (ex2se e2 (S (S (nat_add y vcnt))))]).(nrm) ss13
      ss14).
      {
        exists (S x), (S (nat_add x (length (ex2pre e1 (S (S (S (nat_add x vcnt)))))))).
        revert H24.
        unfold nat_add.
        pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite <- H24.
        pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite H26.
        pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
        rewrite H27.
        tauto.
      }
    pose proof greater_vcnt2_aux vcnt ss13 ss14 e2 H26.
    rewrite H27.
    simpl in H25.
    sets_unfold in H25.
    destruct H25.
    destruct H25.
    rewrite H28 in H25.
    destruct H25.
    ---
    destruct H25.
    destruct H25.
    unfold test_true in H25.
    sets_unfold in H25.
    destruct H25.
    rewrite <- H30 in H29.
    destruct H29.
    destruct H29.
    rewrite H31 in H29.
    unfold asgn_deref_sem_nrm in H29.
    destruct H29 as [i1[i2[?[?[?[?[?]]]]]]].
    pose proof H35 (nat2Sname vcnt).
    pose proof classic (i1 = (ss14.(env) (nat2Sname vcnt))).
    destruct H38.
    ----
    rewrite H38 in H29.
    pose proof trans_prop2 (S (nat_add x vcnt)) vcnt ss14.
    destruct H39.
    pose proof H40 H29.
    pose proof greater_vcnt2_aux_aux x vcnt.
    destruct H42.
    rewrite H41.
    tauto.
    ----
    pose proof H36 (ss14.(env) (nat2Sname vcnt)) H38.
    rewrite H39.
    rewrite H37.
    tauto.
    ---
    destruct H25.
    destruct H25.
    unfold test_true in H25.
    sets_unfold in H25.
    destruct H25.
    rewrite <- H30 in H29.
    destruct H29.
    destruct H29.
    rewrite H31 in H29.
    unfold asgn_deref_sem_nrm in H29.
    destruct H29 as [i1[i2[?[?[?[?[?]]]]]]].
    pose proof H35 (nat2Sname vcnt).
    pose proof classic (i1 = (ss14.(env) (nat2Sname vcnt))).
    destruct H38.
    ----
    rewrite H38 in H29.
    pose proof trans_prop2 (S (nat_add x vcnt)) vcnt ss14.
    destruct H39.
    pose proof H40 H29.
    pose proof greater_vcnt2_aux_aux x vcnt.
    destruct H42.
    rewrite H41.
    tauto.
    ----
    pose proof H36 (ss14.(env) (nat2Sname vcnt)) H38.
    rewrite H39.
    rewrite H37.
    tauto.
    -
    pose proof eval_comlist_seq_nrm
      (ex2pre e1 (S (S (S (nat_add x vcnt)))))
        ([SCAsgnVar (nat2Sname (S (S (nat_add x vcnt))))
           (ex2se e1 (S (S (S (nat_add x vcnt)))))] ++
        [SCIf (genSECV (S (S (nat_add x vcnt))))
           (ex2pre e2
              (nat_add (S (S (S (nat_add x vcnt))))
                 (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))) ++
            [SCAsgnVar (nat2Sname (S (S (nat_add x vcnt))))
               (ex2se e2
                  (nat_add (S (S (S (nat_add x vcnt))))
                     (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))))] ++
            [SCIf (genSECV (S (S (nat_add x vcnt))))
               [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
                  (SEConstOrVar (SEConst 1))]
               [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
                  (SEConstOrVar (SEConst 0))]])
            [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
              (SEConstOrVar (SEConst 0))]]) ss1 ss2.
    destruct H1.
    pose proof H1 H.
    sets_unfold in H3.
    destruct H3 as [ss11].
    destruct H3.
    assert (exists x : nat,
        (Seval_comlist (ex2pre e1 (S (nat_add x vcnt)))).(nrm) ss1 ss11).
    {
      exists (S (S x)).
      tauto.
    }
    pose proof IHe1 ss1 ss11 H5.
    rewrite H6.
    pose proof eval_comlist_seq_nrm
       [SCAsgnVar (nat2Sname (S (S (nat_add x vcnt))))
           (ex2se e1 (S (S (S (nat_add x vcnt)))))] 
        ([SCIf (genSECV (S (S (nat_add x vcnt))))
           (ex2pre e2
              (nat_add (S (S (S (nat_add x vcnt))))
                 (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))) ++
            [SCAsgnVar (nat2Sname (S (S (nat_add x vcnt))))
               (ex2se e2
                  (nat_add (S (S (S (nat_add x vcnt))))
                     (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))))] ++
            [SCIf (genSECV (S (S (nat_add x vcnt))))
               [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
                  (SEConstOrVar (SEConst 1))]
               [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
                  (SEConstOrVar (SEConst 0))]])
            [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
              (SEConstOrVar (SEConst 0))]]) ss11 ss2.
    destruct H7.
    pose proof H7 H4.
    sets_unfold in H9.
    destruct H9 as [ss12].
    destruct H9.
    assert (exists x y : nat,
         (Seval_comlist
            [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
               (ex2se e1 (S (S (nat_add y vcnt))))]).(nrm) ss11
           ss12).
    {
      exists (S x), (S x).
      revert H9.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss11 ss12 e1 H11.
    rewrite H12.
    simpl in H10.
    sets_unfold in H10.
    destruct H10.
    destruct H10.
    rewrite H13 in H10.
    destruct H10.
    --
    destruct H10.
    destruct H10.
    unfold test_false in H10.
    sets_unfold in H10.
    destruct H10.
    rewrite <- H15 in H14.
    pose proof eval_comlist_seq_nrm 
      (ex2pre e2
            (S
               (S
                  (S
                     (nat_add (nat_add x vcnt)
                        (length
                           (ex2pre e1
                              (S (S (S (nat_add x vcnt)))))))))))
          [SCAsgnVar (nat2Sname (S (S (nat_add x vcnt))))
             (ex2se e2
                (S
                   (S
                      (S
                         (nat_add (nat_add x vcnt)
                            (length
                               (ex2pre e1
                                  (S (S (S (nat_add x vcnt))))))))))),
          SCIf (genSECV (S (S (nat_add x vcnt))))
            [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
               (SEConstOrVar (SEConst 1))]
            [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
               (SEConstOrVar (SEConst 0))]] ss12 ss2.
    destruct H16.
    pose proof H16 H14.
    sets_unfold in H18.
    destruct H18 as [ss13].
    destruct H18.
    assert (exists x : nat,
    (Seval_comlist (ex2pre e2 (S (nat_add x vcnt)))).(nrm)
      ss12 ss13).
    {
      exists (S (S (nat_add x (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))))).
      revert H18.
      simpl.
      unfold nat_add.
      pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite <- H18.
      pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite H20.
      pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
      rewrite H21.
      tauto.
    }
    pose proof IHe2 ss12 ss13 H20.
    rewrite H21.
    pose proof eval_comlist_seq_nrm
      [SCAsgnVar (nat2Sname (S (S (nat_add x vcnt))))
            (ex2se e2
               (S
                  (S
                     (S
                        (nat_add (nat_add x vcnt)
                           (length
                              (ex2pre e1
                                 (S (S (S (nat_add x vcnt)))))))))))]
         [SCIf (genSECV (S (S (nat_add x vcnt))))
           [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
              (SEConstOrVar (SEConst 1))]
           [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
              (SEConstOrVar (SEConst 0))]] ss13 ss2.
    destruct H22.
    pose proof H22 H19.
    sets_unfold in H24.
    destruct H24 as [ss14].
    destruct H24.
    assert (exists x y : nat,
    (Seval_comlist
       [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
          (ex2se e2 (S (S (nat_add y vcnt))))]).(nrm) ss13
      ss14).
      {
        exists (S x), (S (nat_add x (length (ex2pre e1 (S (S (S (nat_add x vcnt)))))))).
        revert H24.
        unfold nat_add.
        pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite <- H24.
        pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite H26.
        pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
        rewrite H27.
        tauto.
      }
    pose proof greater_vcnt2_aux vcnt ss13 ss14 e2 H26.
    rewrite H27.
    simpl in H25.
    sets_unfold in H25.
    destruct H25.
    destruct H25.
    rewrite H28 in H25.
    destruct H25.
    ---
    destruct H25.
    destruct H25.
    unfold test_true in H25.
    sets_unfold in H25.
    destruct H25.
    rewrite <- H30 in H29.
    destruct H29.
    destruct H29.
    rewrite H31 in H29.
    unfold asgn_deref_sem_nrm in H29.
    destruct H29 as [i1[i2[?[?[?[?[?]]]]]]].
    pose proof H35 (nat2Sname vcnt).
    pose proof classic (i1 = (ss14.(env) (nat2Sname vcnt))).
    destruct H38.
    ----
    rewrite H38 in H29.
    pose proof trans_prop2 (S (nat_add x vcnt)) vcnt ss14.
    destruct H39.
    pose proof H40 H29.
    pose proof greater_vcnt2_aux_aux x vcnt.
    destruct H42.
    rewrite H41.
    tauto.
    ----
    pose proof H36 (ss14.(env) (nat2Sname vcnt)) H38.
    rewrite H39.
    rewrite H37.
    tauto.
    ---
    destruct H25.
    destruct H25.
    unfold test_true in H25.
    sets_unfold in H25.
    destruct H25.
    rewrite <- H30 in H29.
    destruct H29.
    destruct H29.
    rewrite H31 in H29.
    unfold asgn_deref_sem_nrm in H29.
    destruct H29 as [i1[i2[?[?[?[?[?]]]]]]].
    pose proof H35 (nat2Sname vcnt).
    pose proof classic (i1 = (ss14.(env) (nat2Sname vcnt))).
    destruct H38.
    ----
    rewrite H38 in H29.
    pose proof trans_prop2 (S (nat_add x vcnt)) vcnt ss14.
    destruct H39.
    pose proof H40 H29.
    pose proof greater_vcnt2_aux_aux x vcnt.
    destruct H42.
    rewrite H41.
    tauto.
    ----
    pose proof H36 (ss14.(env) (nat2Sname vcnt)) H38.
    rewrite H39.
    rewrite H37.
    tauto.
    --
    destruct H10.
    destruct H10.
    unfold test_true in H10.
    sets_unfold in H10.
    destruct H10.
    rewrite <- H15 in H14.
    destruct H14.
    destruct H14.
    rewrite H16 in H14.
    unfold asgn_deref_sem_nrm in H14.
    destruct H14 as [i1[i2[?[?[?[?[?]]]]]]].
    pose proof H20 (nat2Sname vcnt).
    pose proof classic (i1 = (ss12.(env) (nat2Sname vcnt))).
    destruct H23.
    ---
    rewrite H23 in H14.
    pose proof trans_prop2 (S (nat_add x vcnt)) vcnt ss12.
    destruct H24.
    pose proof H25 H14.
    pose proof greater_vcnt2_aux_aux x vcnt.
    destruct H27.
    rewrite H26.
    tauto.
    ---
    pose proof H21 (ss12.(env) (nat2Sname vcnt)) H23.
    rewrite H24.
    rewrite H22.
    tauto.
    -
    pose proof midstate_binop (S (nat_add x vcnt)) e1 e2 ss1 ss2 H.
    destruct H1 as [ss11[ss12[ss13[?[?[?]]]]]].
    assert (exists x : nat,
    (Seval_comlist (ex2pre e1 (S (nat_add x vcnt)))).(nrm)
      ss1 ss11).
    {
      exists (S (S x)).
      tauto.
    }
    pose proof IHe1 ss1 ss11 H5.
    assert (exists x y : nat,
        (Seval_comlist
           [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
              (ex2se e1 (S (S (nat_add y vcnt))))]).(nrm)
          ss11 ss12).
    {
      exists x, (S x).
      revert H2.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss11 ss12 e1 H7.
    assert (exists x : nat,
    (Seval_comlist (ex2pre e2 (S (nat_add x vcnt)))).(nrm) ss12 ss13).
    {
      exists (nat_add (S (S x)) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      revert H3.
      simpl.
      unfold nat_add.
      pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite <- H3.
      pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite H9.
      pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
      rewrite H10.
      tauto.
    }
    pose proof IHe2 ss12 ss13 H9.
    assert (exists x y : nat,
         (Seval_comlist
            [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
               (ex2se e2 (S (S (nat_add y vcnt))))]).(nrm) ss13 ss2).
    {
      exists (S x), (nat_add (S x) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      assert ((S
      (S
         (nat_add
            (nat_add (S x)
               (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))) vcnt)))
               =
               (S
                 (S
                    (nat_add (S (nat_add x vcnt))
                       (length (ex2pre e1 (S (S (S (nat_add x vcnt)))))))))).
      {
        unfold nat_add.
        simpl.
        pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite <- H11.
        pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite H12.
        pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
        rewrite H13.
        tauto.
      }
      rewrite H11.
      revert H4.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss13 ss2 e2 H11.
    rewrite H6.
    rewrite H8.
    rewrite H10.
    rewrite H12.
    reflexivity.
    -
    pose proof midstate_binop (S (nat_add x vcnt)) e1 e2 ss1 ss2 H.
    destruct H1 as [ss11[ss12[ss13[?[?[?]]]]]].
    assert (exists x : nat,
    (Seval_comlist (ex2pre e1 (S (nat_add x vcnt)))).(nrm)
      ss1 ss11).
    {
      exists (S (S x)).
      tauto.
    }
    pose proof IHe1 ss1 ss11 H5.
    assert (exists x y : nat,
        (Seval_comlist
           [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
              (ex2se e1 (S (S (nat_add y vcnt))))]).(nrm)
          ss11 ss12).
    {
      exists x, (S x).
      revert H2.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss11 ss12 e1 H7.
    assert (exists x : nat,
    (Seval_comlist (ex2pre e2 (S (nat_add x vcnt)))).(nrm) ss12 ss13).
    {
      exists (nat_add (S (S x)) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      revert H3.
      simpl.
      unfold nat_add.
      pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite <- H3.
      pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite H9.
      pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
      rewrite H10.
      tauto.
    }
    pose proof IHe2 ss12 ss13 H9.
    assert (exists x y : nat,
         (Seval_comlist
            [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
               (ex2se e2 (S (S (nat_add y vcnt))))]).(nrm) ss13 ss2).
    {
      exists (S x), (nat_add (S x) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      assert ((S
      (S
         (nat_add
            (nat_add (S x)
               (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))) vcnt)))
               =
               (S
                 (S
                    (nat_add (S (nat_add x vcnt))
                       (length (ex2pre e1 (S (S (S (nat_add x vcnt)))))))))).
      {
        unfold nat_add.
        simpl.
        pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite <- H11.
        pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite H12.
        pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
        rewrite H13.
        tauto.
      }
      rewrite H11.
      revert H4.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss13 ss2 e2 H11.
    rewrite H6.
    rewrite H8.
    rewrite H10.
    rewrite H12.
    reflexivity.
    -
    pose proof midstate_binop (S (nat_add x vcnt)) e1 e2 ss1 ss2 H.
    destruct H1 as [ss11[ss12[ss13[?[?[?]]]]]].
    assert (exists x : nat,
    (Seval_comlist (ex2pre e1 (S (nat_add x vcnt)))).(nrm)
      ss1 ss11).
    {
      exists (S (S x)).
      tauto.
    }
    pose proof IHe1 ss1 ss11 H5.
    assert (exists x y : nat,
        (Seval_comlist
           [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
              (ex2se e1 (S (S (nat_add y vcnt))))]).(nrm)
          ss11 ss12).
    {
      exists x, (S x).
      revert H2.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss11 ss12 e1 H7.
    assert (exists x : nat,
    (Seval_comlist (ex2pre e2 (S (nat_add x vcnt)))).(nrm) ss12 ss13).
    {
      exists (nat_add (S (S x)) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      revert H3.
      simpl.
      unfold nat_add.
      pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite <- H3.
      pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite H9.
      pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
      rewrite H10.
      tauto.
    }
    pose proof IHe2 ss12 ss13 H9.
    assert (exists x y : nat,
         (Seval_comlist
            [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
               (ex2se e2 (S (S (nat_add y vcnt))))]).(nrm) ss13 ss2).
    {
      exists (S x), (nat_add (S x) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      assert ((S
      (S
         (nat_add
            (nat_add (S x)
               (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))) vcnt)))
               =
               (S
                 (S
                    (nat_add (S (nat_add x vcnt))
                       (length (ex2pre e1 (S (S (S (nat_add x vcnt)))))))))).
      {
        unfold nat_add.
        simpl.
        pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite <- H11.
        pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite H12.
        pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
        rewrite H13.
        tauto.
      }
      rewrite H11.
      revert H4.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss13 ss2 e2 H11.
    rewrite H6.
    rewrite H8.
    rewrite H10.
    rewrite H12.
    reflexivity.
    -
    pose proof midstate_binop (S (nat_add x vcnt)) e1 e2 ss1 ss2 H.
    destruct H1 as [ss11[ss12[ss13[?[?[?]]]]]].
    assert (exists x : nat,
    (Seval_comlist (ex2pre e1 (S (nat_add x vcnt)))).(nrm)
      ss1 ss11).
    {
      exists (S (S x)).
      tauto.
    }
    pose proof IHe1 ss1 ss11 H5.
    assert (exists x y : nat,
        (Seval_comlist
           [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
              (ex2se e1 (S (S (nat_add y vcnt))))]).(nrm)
          ss11 ss12).
    {
      exists x, (S x).
      revert H2.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss11 ss12 e1 H7.
    assert (exists x : nat,
    (Seval_comlist (ex2pre e2 (S (nat_add x vcnt)))).(nrm) ss12 ss13).
    {
      exists (nat_add (S (S x)) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      revert H3.
      simpl.
      unfold nat_add.
      pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite <- H3.
      pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite H9.
      pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
      rewrite H10.
      tauto.
    }
    pose proof IHe2 ss12 ss13 H9.
    assert (exists x y : nat,
         (Seval_comlist
            [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
               (ex2se e2 (S (S (nat_add y vcnt))))]).(nrm) ss13 ss2).
    {
      exists (S x), (nat_add (S x) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      assert ((S
      (S
         (nat_add
            (nat_add (S x)
               (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))) vcnt)))
               =
               (S
                 (S
                    (nat_add (S (nat_add x vcnt))
                       (length (ex2pre e1 (S (S (S (nat_add x vcnt)))))))))).
      {
        unfold nat_add.
        simpl.
        pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite <- H11.
        pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite H12.
        pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
        rewrite H13.
        tauto.
      }
      rewrite H11.
      revert H4.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss13 ss2 e2 H11.
    rewrite H6.
    rewrite H8.
    rewrite H10.
    rewrite H12.
    reflexivity.
    -
    pose proof midstate_binop (S (nat_add x vcnt)) e1 e2 ss1 ss2 H.
    destruct H1 as [ss11[ss12[ss13[?[?[?]]]]]].
    assert (exists x : nat,
    (Seval_comlist (ex2pre e1 (S (nat_add x vcnt)))).(nrm)
      ss1 ss11).
    {
      exists (S (S x)).
      tauto.
    }
    pose proof IHe1 ss1 ss11 H5.
    assert (exists x y : nat,
        (Seval_comlist
           [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
              (ex2se e1 (S (S (nat_add y vcnt))))]).(nrm)
          ss11 ss12).
    {
      exists x, (S x).
      revert H2.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss11 ss12 e1 H7.
    assert (exists x : nat,
    (Seval_comlist (ex2pre e2 (S (nat_add x vcnt)))).(nrm) ss12 ss13).
    {
      exists (nat_add (S (S x)) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      revert H3.
      simpl.
      unfold nat_add.
      pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite <- H3.
      pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite H9.
      pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
      rewrite H10.
      tauto.
    }
    pose proof IHe2 ss12 ss13 H9.
    assert (exists x y : nat,
         (Seval_comlist
            [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
               (ex2se e2 (S (S (nat_add y vcnt))))]).(nrm) ss13 ss2).
    {
      exists (S x), (nat_add (S x) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      assert ((S
      (S
         (nat_add
            (nat_add (S x)
               (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))) vcnt)))
               =
               (S
                 (S
                    (nat_add (S (nat_add x vcnt))
                       (length (ex2pre e1 (S (S (S (nat_add x vcnt)))))))))).
      {
        unfold nat_add.
        simpl.
        pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite <- H11.
        pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite H12.
        pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
        rewrite H13.
        tauto.
      }
      rewrite H11.
      revert H4.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss13 ss2 e2 H11.
    rewrite H6.
    rewrite H8.
    rewrite H10.
    rewrite H12.
    reflexivity.
    -
    pose proof midstate_binop (S (nat_add x vcnt)) e1 e2 ss1 ss2 H.
    destruct H1 as [ss11[ss12[ss13[?[?[?]]]]]].
    assert (exists x : nat,
    (Seval_comlist (ex2pre e1 (S (nat_add x vcnt)))).(nrm)
      ss1 ss11).
    {
      exists (S (S x)).
      tauto.
    }
    pose proof IHe1 ss1 ss11 H5.
    assert (exists x y : nat,
        (Seval_comlist
           [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
              (ex2se e1 (S (S (nat_add y vcnt))))]).(nrm)
          ss11 ss12).
    {
      exists x, (S x).
      revert H2.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss11 ss12 e1 H7.
    assert (exists x : nat,
    (Seval_comlist (ex2pre e2 (S (nat_add x vcnt)))).(nrm) ss12 ss13).
    {
      exists (nat_add (S (S x)) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      revert H3.
      simpl.
      unfold nat_add.
      pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite <- H3.
      pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite H9.
      pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
      rewrite H10.
      tauto.
    }
    pose proof IHe2 ss12 ss13 H9.
    assert (exists x y : nat,
         (Seval_comlist
            [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
               (ex2se e2 (S (S (nat_add y vcnt))))]).(nrm) ss13 ss2).
    {
      exists (S x), (nat_add (S x) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      assert ((S
      (S
         (nat_add
            (nat_add (S x)
               (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))) vcnt)))
               =
               (S
                 (S
                    (nat_add (S (nat_add x vcnt))
                       (length (ex2pre e1 (S (S (S (nat_add x vcnt)))))))))).
      {
        unfold nat_add.
        simpl.
        pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite <- H11.
        pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite H12.
        pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
        rewrite H13.
        tauto.
      }
      rewrite H11.
      revert H4.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss13 ss2 e2 H11.
    rewrite H6.
    rewrite H8.
    rewrite H10.
    rewrite H12.
    reflexivity.
    -
    pose proof midstate_binop (S (nat_add x vcnt)) e1 e2 ss1 ss2 H.
    destruct H1 as [ss11[ss12[ss13[?[?[?]]]]]].
    assert (exists x : nat,
    (Seval_comlist (ex2pre e1 (S (nat_add x vcnt)))).(nrm)
      ss1 ss11).
    {
      exists (S (S x)).
      tauto.
    }
    pose proof IHe1 ss1 ss11 H5.
    assert (exists x y : nat,
        (Seval_comlist
           [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
              (ex2se e1 (S (S (nat_add y vcnt))))]).(nrm)
          ss11 ss12).
    {
      exists x, (S x).
      revert H2.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss11 ss12 e1 H7.
    assert (exists x : nat,
    (Seval_comlist (ex2pre e2 (S (nat_add x vcnt)))).(nrm) ss12 ss13).
    {
      exists (nat_add (S (S x)) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      revert H3.
      simpl.
      unfold nat_add.
      pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite <- H3.
      pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite H9.
      pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
      rewrite H10.
      tauto.
    }
    pose proof IHe2 ss12 ss13 H9.
    assert (exists x y : nat,
         (Seval_comlist
            [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
               (ex2se e2 (S (S (nat_add y vcnt))))]).(nrm) ss13 ss2).
    {
      exists (S x), (nat_add (S x) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      assert ((S
      (S
         (nat_add
            (nat_add (S x)
               (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))) vcnt)))
               =
               (S
                 (S
                    (nat_add (S (nat_add x vcnt))
                       (length (ex2pre e1 (S (S (S (nat_add x vcnt)))))))))).
      {
        unfold nat_add.
        simpl.
        pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite <- H11.
        pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite H12.
        pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
        rewrite H13.
        tauto.
      }
      rewrite H11.
      revert H4.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss13 ss2 e2 H11.
    rewrite H6.
    rewrite H8.
    rewrite H10.
    rewrite H12.
    reflexivity.
    -
    pose proof midstate_binop (S (nat_add x vcnt)) e1 e2 ss1 ss2 H.
    destruct H1 as [ss11[ss12[ss13[?[?[?]]]]]].
    assert (exists x : nat,
    (Seval_comlist (ex2pre e1 (S (nat_add x vcnt)))).(nrm)
      ss1 ss11).
    {
      exists (S (S x)).
      tauto.
    }
    pose proof IHe1 ss1 ss11 H5.
    assert (exists x y : nat,
        (Seval_comlist
           [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
              (ex2se e1 (S (S (nat_add y vcnt))))]).(nrm)
          ss11 ss12).
    {
      exists x, (S x).
      revert H2.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss11 ss12 e1 H7.
    assert (exists x : nat,
    (Seval_comlist (ex2pre e2 (S (nat_add x vcnt)))).(nrm) ss12 ss13).
    {
      exists (nat_add (S (S x)) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      revert H3.
      simpl.
      unfold nat_add.
      pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite <- H3.
      pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite H9.
      pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
      rewrite H10.
      tauto.
    }
    pose proof IHe2 ss12 ss13 H9.
    assert (exists x y : nat,
         (Seval_comlist
            [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
               (ex2se e2 (S (S (nat_add y vcnt))))]).(nrm) ss13 ss2).
    {
      exists (S x), (nat_add (S x) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      assert ((S
      (S
         (nat_add
            (nat_add (S x)
               (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))) vcnt)))
               =
               (S
                 (S
                    (nat_add (S (nat_add x vcnt))
                       (length (ex2pre e1 (S (S (S (nat_add x vcnt)))))))))).
      {
        unfold nat_add.
        simpl.
        pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite <- H11.
        pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite H12.
        pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
        rewrite H13.
        tauto.
      }
      rewrite H11.
      revert H4.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss13 ss2 e2 H11.
    rewrite H6.
    rewrite H8.
    rewrite H10.
    rewrite H12.
    reflexivity.
    -
    pose proof midstate_binop (S (nat_add x vcnt)) e1 e2 ss1 ss2 H.
    destruct H1 as [ss11[ss12[ss13[?[?[?]]]]]].
    assert (exists x : nat,
    (Seval_comlist (ex2pre e1 (S (nat_add x vcnt)))).(nrm)
      ss1 ss11).
    {
      exists (S (S x)).
      tauto.
    }
    pose proof IHe1 ss1 ss11 H5.
    assert (exists x y : nat,
        (Seval_comlist
           [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
              (ex2se e1 (S (S (nat_add y vcnt))))]).(nrm)
          ss11 ss12).
    {
      exists x, (S x).
      revert H2.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss11 ss12 e1 H7.
    assert (exists x : nat,
    (Seval_comlist (ex2pre e2 (S (nat_add x vcnt)))).(nrm) ss12 ss13).
    {
      exists (nat_add (S (S x)) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      revert H3.
      simpl.
      unfold nat_add.
      pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite <- H3.
      pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite H9.
      pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
      rewrite H10.
      tauto.
    }
    pose proof IHe2 ss12 ss13 H9.
    assert (exists x y : nat,
         (Seval_comlist
            [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
               (ex2se e2 (S (S (nat_add y vcnt))))]).(nrm) ss13 ss2).
    {
      exists (S x), (nat_add (S x) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      assert ((S
      (S
         (nat_add
            (nat_add (S x)
               (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))) vcnt)))
               =
               (S
                 (S
                    (nat_add (S (nat_add x vcnt))
                       (length (ex2pre e1 (S (S (S (nat_add x vcnt)))))))))).
      {
        unfold nat_add.
        simpl.
        pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite <- H11.
        pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite H12.
        pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
        rewrite H13.
        tauto.
      }
      rewrite H11.
      revert H4.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss13 ss2 e2 H11.
    rewrite H6.
    rewrite H8.
    rewrite H10.
    rewrite H12.
    reflexivity.
    -
    pose proof midstate_binop (S (nat_add x vcnt)) e1 e2 ss1 ss2 H.
    destruct H1 as [ss11[ss12[ss13[?[?[?]]]]]].
    assert (exists x : nat,
    (Seval_comlist (ex2pre e1 (S (nat_add x vcnt)))).(nrm)
      ss1 ss11).
    {
      exists (S (S x)).
      tauto.
    }
    pose proof IHe1 ss1 ss11 H5.
    assert (exists x y : nat,
        (Seval_comlist
           [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
              (ex2se e1 (S (S (nat_add y vcnt))))]).(nrm)
          ss11 ss12).
    {
      exists x, (S x).
      revert H2.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss11 ss12 e1 H7.
    assert (exists x : nat,
    (Seval_comlist (ex2pre e2 (S (nat_add x vcnt)))).(nrm) ss12 ss13).
    {
      exists (nat_add (S (S x)) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      revert H3.
      simpl.
      unfold nat_add.
      pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite <- H3.
      pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite H9.
      pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
      rewrite H10.
      tauto.
    }
    pose proof IHe2 ss12 ss13 H9.
    assert (exists x y : nat,
         (Seval_comlist
            [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
               (ex2se e2 (S (S (nat_add y vcnt))))]).(nrm) ss13 ss2).
    {
      exists (S x), (nat_add (S x) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      assert ((S
      (S
         (nat_add
            (nat_add (S x)
               (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))) vcnt)))
               =
               (S
                 (S
                    (nat_add (S (nat_add x vcnt))
                       (length (ex2pre e1 (S (S (S (nat_add x vcnt)))))))))).
      {
        unfold nat_add.
        simpl.
        pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite <- H11.
        pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite H12.
        pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
        rewrite H13.
        tauto.
      }
      rewrite H11.
      revert H4.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss13 ss2 e2 H11.
    rewrite H6.
    rewrite H8.
    rewrite H10.
    rewrite H12.
    reflexivity.
    -
    pose proof midstate_binop (S (nat_add x vcnt)) e1 e2 ss1 ss2 H.
    destruct H1 as [ss11[ss12[ss13[?[?[?]]]]]].
    assert (exists x : nat,
    (Seval_comlist (ex2pre e1 (S (nat_add x vcnt)))).(nrm)
      ss1 ss11).
    {
      exists (S (S x)).
      tauto.
    }
    pose proof IHe1 ss1 ss11 H5.
    assert (exists x y : nat,
        (Seval_comlist
           [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
              (ex2se e1 (S (S (nat_add y vcnt))))]).(nrm)
          ss11 ss12).
    {
      exists x, (S x).
      revert H2.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss11 ss12 e1 H7.
    assert (exists x : nat,
    (Seval_comlist (ex2pre e2 (S (nat_add x vcnt)))).(nrm) ss12 ss13).
    {
      exists (nat_add (S (S x)) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      revert H3.
      simpl.
      unfold nat_add.
      pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite <- H3.
      pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
      rewrite H9.
      pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
      rewrite H10.
      tauto.
    }
    pose proof IHe2 ss12 ss13 H9.
    assert (exists x y : nat,
         (Seval_comlist
            [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
               (ex2se e2 (S (S (nat_add y vcnt))))]).(nrm) ss13 ss2).
    {
      exists (S x), (nat_add (S x) (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))).
      assert ((S
      (S
         (nat_add
            (nat_add (S x)
               (length (ex2pre e1 (S (S (S (nat_add x vcnt))))))) vcnt)))
               =
               (S
                 (S
                    (nat_add (S (nat_add x vcnt))
                       (length (ex2pre e1 (S (S (S (nat_add x vcnt)))))))))).
      {
        unfold nat_add.
        simpl.
        pose proof Nat.add_assoc x vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite <- H11.
        pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S (S (x + vcnt)))))).
        rewrite H12.
        pose proof Nat.add_assoc x (length (ex2pre e1 (S (S (S (x + vcnt)))))) vcnt.
        rewrite H13.
        tauto.
      }
      rewrite H11.
      revert H4.
      simpl.
      tauto.
    }
    pose proof greater_vcnt2_aux vcnt ss13 ss2 e2 H11.
    rewrite H6.
    rewrite H8.
    rewrite H10.
    rewrite H12.
    reflexivity.
  + simpl.
    intros.
    destruct H.
    pose proof eval_comlist_seq_nrm (ex2pre e (S (S (nat_add x vcnt))))
      [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
           (ex2se e (S (S (nat_add x vcnt))))] ss1 ss2.
    destruct H0.
    pose proof H0 H.
    sets_unfold in H2.
    destruct H2 as [ss15].
    destruct H2.
    assert (exists x : nat,
    (Seval_comlist (ex2pre e (S (nat_add x vcnt)))).(nrm) ss1 ss15).
    {
      exists (S x).
      simpl.
      tauto.
    }
    pose proof IHe ss1 ss15 H4.
    assert (exists x y : nat,
    (Seval_comlist
       [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
          (ex2se e (S (S (nat_add y vcnt))))]).(nrm) ss15 ss2).
    exists x, x.
    tauto.
    pose proof greater_vcnt2_aux vcnt ss15 ss2 e H6.
    rewrite H5.
    tauto.
  + simpl.
    intros.
    destruct H.
    pose proof eval_comlist_seq_nrm (ex2pre e (S (S (nat_add x vcnt))))
      [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
           (ex2se e (S (S (nat_add x vcnt))))] ss1 ss2.
    destruct H0.
    pose proof H0 H.
    sets_unfold in H2.
    destruct H2 as [ss15].
    destruct H2.
    assert (exists x : nat,
    (Seval_comlist (ex2pre e (S (nat_add x vcnt)))).(nrm) ss1 ss15).
    {
      exists (S x).
      simpl.
      tauto.
    }
    pose proof IHe ss1 ss15 H4.
    assert (exists x y : nat,
    (Seval_comlist
       [SCAsgnVar (nat2Sname (S (nat_add x vcnt)))
          (ex2se e (S (S (nat_add y vcnt))))]).(nrm) ss15 ss2).
    exists x, x.
    tauto.
    pose proof greater_vcnt2_aux vcnt ss15 ss2 e H6.
    rewrite H5.
    tauto.
  + destruct e; simpl; simpl in IHe.
    - tauto.
    - tauto.
    - sets_unfold.
      intros.
      destruct H.
      rewrite H.
      tauto.
    - sets_unfold.
      intros.
      destruct H.
      rewrite H.
      tauto.
    - tauto.
    - sets_unfold.
      intros.
      destruct H.
      rewrite H.
      tauto.
Qed.

Lemma greater_vcnt1 {NameX : Names} {NPX : NamesProperty}:
  forall (vcnt : nat) (ss1 ss2 :state) (e1 e2 : expr),
    (Seval_comlist 
          (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))).(nrm) ss1 ss2
    -> ss1.(mem) (ss1.(env) (nat2Sname vcnt)) = ss2.(mem) (ss2.(env) (nat2Sname vcnt)).
Proof.
  intros.
  assert (exists x : nat,
  (Seval_comlist (ex2pre e2 (S (nat_add x vcnt)))).(nrm) ss1 ss2).
  {
    exists (S (length (ex2pre e1 (S (S vcnt))))).
    revert H.
    unfold nat_add.
    simpl.
    pose proof Nat.add_comm vcnt (length (ex2pre e1 (S (S vcnt)))).
    rewrite H.
    tauto.
  }
  pose proof greater_vcnt1_aux vcnt ss1 ss2 e2 H0.
  tauto.
Qed.


Lemma midstate_prop_4_nrm {NameX : Names} {NPX : NamesProperty}:
forall (vcnt : nat) (e1 e2 : expr) (i1 i2 x0 x1 : int64),
  forall (s1 ss1 ss14 : state),
  (forall (vcnt : nat), Serefine_nrm (ex2pre e1 vcnt) (ex2se e1 vcnt) e1) ->
  (forall (vcnt : nat), Serefine_nrm (ex2pre e2 vcnt) (ex2se e2 vcnt) e2) ->
  (Seval_comlist
   ((ex2pre e1 (S (S vcnt)) ++
     [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
     ex2pre e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))) ++
     [SCAsgnVar (nat2Sname (S vcnt))
        (ex2se e2
           (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))]))).(nrm) ss1 ss14
  ->  correspond s1 ss1
  ->  ss14.(env) (nat2Sname vcnt) = i1
  ->  ss14.(mem) i1 = Some (Vint x0)
  ->  ss14.(env) (nat2Sname (S vcnt)) = i2
  ->  ss14.(mem) i2 = Some (Vint x1)
  ->  (((eval_r e1).(nrm) s1 x0 /\ (eval_r e2).(nrm) s1 x1)
      \/ (eval_r e1).(err) s1 \/ (eval_r e2).(err) s1) /\ correspond s1 ss14.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? IH1 IH2.
  intros.
  pose proof midstate_cor_4_nrm vcnt e1 e2 s1 ss1 ss14 H H0.
  destruct H5 as [ss11 [ss12 [ss13 [?[?[?[?[?[?[?]]]]]]]]]].
  assert ((Seval_r (genSECV vcnt)).(nrm) ss14 x0).
  {
    simpl.
    unfold deref_sem_nrm.
    exists i1.
    tauto.
  }
  assert ((Seval_r (genSECV (S vcnt))).(nrm) ss14 x1).
  {
    simpl.
    unfold deref_sem_nrm.
    exists i2.
    tauto.
  }
  pose proof asgn_vcnt_ex2se_nrm_prop 
    (ex2se e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))
    (S vcnt) ss13 ss14 H8 x1 H14 as H30.
  pose proof asgn_vcnt_ex2se_nrm_prop 
    (ex2se e1 (S (S vcnt)))
    vcnt ss11 ss12 H6 as H31.
  revert H6 H8.
  simpl.
  sets_unfold.
  unfold asgn_deref_sem_nrm.
  intros.
  destruct H6.
  destruct H6.
  rewrite H15 in H6.
  destruct H6 as [?[?[?[?[?[?[?]]]]]]].
  destruct H8.
  destruct H8.
  rewrite H21 in H8.
  destruct H8 as [?[?[?[?[?[?[?]]]]]]].
  pose proof IH2 (nat_add (S (S vcnt))
  (length (ex2pre e1 (S (S vcnt))))) as [H2l H2r].
  pose proof H2r s1 ss12 ss13 x1 H10 H7 H30.
  destruct H27; [|tauto].
  pose proof H25 (nat2Sname vcnt).
  rewrite H1 in H28.
  assert (x5 <> i1).
  {
    pose proof classic (x5 = i1).
    destruct H29; [|tauto].
    rewrite <- H28 in H29.
    rewrite <- H8 in H29.
    pose proof trans_prop2 (S vcnt) vcnt ss13.
    destruct H32.
    pose proof H33 H29.
    lia.
  }
  pose proof H26 i1 H29.
  rewrite <- H1 in H32.
  rewrite <- H1 in H2.
  rewrite H2 in H32.
  rewrite H1 in H32.
  rewrite <- H28 in H32.
  assert ((nat_add (S (S vcnt))
  (length (ex2pre e1 (S (S vcnt))))) = (S
  (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))).
  {
    simpl.
    tauto.
  }
  pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H7.
  assert ((Seval_r (genSECV vcnt)).(nrm) ss12 x0).
  {
    simpl.
    unfold deref_sem_nrm.
    exists (ss12.(env) (nat2Sname vcnt)).
    rewrite <- H32.
    tauto.
  }
  pose proof H31 x0 H35.
  pose proof IH1 (S (S vcnt)) as [H1l H1r].
  pose proof H1r s1 ss1 ss11 x0 H0 H5 H36.
  tauto.
Qed.

Lemma Split_Serefine_nrm_r_deref {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr),
    (forall (vcnt : nat), Serefine_nrm_l (ex2pre e vcnt) (ex2se e vcnt) e)
    -> 
    (forall (vcnt : nat), Serefine_nrm_r (ex2pre e vcnt) (ex2se e vcnt) e)
    ->
    forall (vcnt : nat), Serefine_nrm_r (ex2pre (EDeref e) vcnt) (ex2se (EDeref e) vcnt) (EDeref e).
Proof.
    unfold Serefine_nrm_r.
    simpl.
    intros e IHel IHe vcnt s1 ss1 ss3 a ? ? ?.
    pose proof midstate_deref_nrm e vcnt ss1 ss3 H0 as Hm.
    pose proof asgn_vcnt_ex2se_nrm_prop (ex2se e (S vcnt)) vcnt as Hp.
    sets_unfold in Hp.
    assert (ex2se (EDeref e) vcnt = SEDeref (genSEVar_n vcnt)) as Hd.
    {
      simpl.
      reflexivity.
    }
    pose proof deref4 e vcnt ss3 a H1 as Hd4.
    pose proof deref7 e vcnt as Hd7.
    pose proof correspond_prop1 as Hc1.
    pose proof correspond_prop2 as Hc2.
    pose proof Hc1 vcnt (ex2se e (S vcnt)) as Hc1.
    pose proof Hc2 e as Hc2.
    destruct Hm as [ss2].
    destruct H2.
    pose proof Hp ss2 ss3 H3. 
    pose proof Hd4 Hd as Hd4.
    destruct Hd4.
    pose proof H4 x H5.
    pose proof Hc2 (S vcnt) s1 ss1 ss2 H H2.
    pose proof Hc1 s1 ss2 ss3 H7 H3.
    pose proof IHe (S vcnt) s1 ss1 ss2 x H H2 H6.
    pose proof Hd7 x a s1 ss3 H8.
    tauto.
Qed.
    
Lemma Split_Serefine_nrm_l_deref {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr),
    (forall (vcnt : nat), Serefine_nrm_l (ex2pre e vcnt) (ex2se e vcnt) e)
    ->
    (forall (vcnt : nat), Serefine_nrm_r (ex2pre e vcnt) (ex2se e vcnt) e)
    ->
    forall (vcnt : nat), Serefine_nrm_l (ex2pre (EDeref e) vcnt) (ex2se (EDeref e) vcnt) (EDeref e).
    Proof.
    unfold Serefine_nrm_l, Serefine_nrm_r.
    simpl.
    intros e IHel IHe vcnt s1 ss1 ss3 a ? ? ?.
    pose proof midstate_deref_nrm e vcnt ss1 ss3 H0 as Hm.
    pose proof correspond_prop1 as Hc1.
    pose proof correspond_prop2 as Hc2.
    pose proof Hc1 vcnt (ex2se e (S vcnt)) as Hc1.
    pose proof Hc2 e as Hc2.
    pose proof asgn_vcnt_ex2se_nrm_prop (ex2se e (S vcnt)) vcnt as He.
    sets_unfold in He.
    revert H H0 H1.
    simpl.
    sets_unfold.
    unfold correspond, deref_sem_nrm, deref_sem_err.
    intros.
    destruct Hm as [ss2].
    destruct H2.
    pose proof Hc2 (S vcnt) s1 ss1 ss2 H H2.
    pose proof Hc1 s1 ss2 ss3 H4 H3.
    assert ((Seval_l (SEDeref (genSEVar_n vcnt))).(nrm) ss3 a = (Seval_r (genSECV vcnt)).(nrm) ss3 a).
    {
      simpl.
      reflexivity.
    }
    pose proof He ss2 ss3 H3 a H1.
    pose proof IHe (S vcnt) s1 ss1 ss2 a H H2 H7.
    tauto.
Qed.

Lemma unop4 {NameX : Names} : forall (e : expr) (vcnt : nat) (s : state) (op:unop) (a : int64),
    (Seval_r (ex2se (EUnop op e) vcnt)).(nrm) s a
    -> ex2se (EUnop op e) vcnt = SEUnop op (genSEVar_n vcnt)
    -> exists (x : int64), 
        (Seval_r (genSECV vcnt)).(nrm) s x.
Proof.
    intros.
    rewrite H0 in H.
    revert H.
    simpl.
    unfold deref_sem_nrm, unop_sem.
    destruct op.
    + unfold not_sem. simpl. unfold not_sem_nrm, deref_sem_nrm.
        intros.
        destruct H.
        destruct H.
        destruct H.
        exists x, x0.
        apply H.
    + unfold neg_sem, neg_sem_nrm. simpl. unfold deref_sem_nrm.
        intros.
        destruct H.
        destruct H.
        destruct H.
        exists x, x0.
        apply H.
Qed.

Lemma unop7{NameX : Names}:
    forall (e : expr) (vcnt : nat) (op : unop) (x a : int64) (s1 ss3 : state) ,
    correspond s1 ss3 ->
    ((eval_r e).(nrm) s1 x \/
    (eval_r e).(err) s1 /\ True)
    -> (Seval_r (genSECV vcnt)).(nrm) ss3 x
    -> (Seval_r (SEUnop op (genSEVar_n vcnt))).(nrm) ss3 a
    -> (eval_r (EUnop op e)).(nrm) s1 a
        \/ (eval_r (EUnop op e)).(err) s1 /\ True.
Proof.
    unfold correspond.
    simpl.
    destruct op.
    + unfold unop_sem, not_sem, deref_sem_nrm, deref_sem_err. simpl. unfold not_sem_nrm.
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
        - left. 
          exists x.
          tauto.
        - tauto.
    + unfold unop_sem, not_sem, deref_sem_nrm, deref_sem_err. simpl. unfold neg_sem_nrm. sets_unfold.
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
        - left. 
          exists x.
          tauto.
        - tauto.
Qed.

Lemma Split_Serefine_nrm_r_unop {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr),
    (forall (vcnt : nat), Serefine_nrm_l (ex2pre e vcnt) (ex2se e vcnt) e)
    -> 
    (forall (vcnt : nat), Serefine_nrm_r (ex2pre e vcnt) (ex2se e vcnt) e)
    ->
    forall (vcnt : nat) (op: unop), Serefine_nrm_r (ex2pre (EUnop op e) vcnt) (ex2se (EUnop op e) vcnt) (EUnop op e).
Proof.
    simpl.
    unfold Serefine_nrm_r.
    intros e IHel IHe vcnt op s1 ss1 ss3 a ? ? ?.
    pose proof asgn_vcnt_ex2se_nrm_prop (ex2se e (S vcnt)) vcnt as Hp.
    sets_unfold in Hp.
    pose proof correspond_prop1 as Hc1.
    pose proof correspond_prop2 as Hc2.
    pose proof midstate_unop op e vcnt ss1 ss3 H0 as Hmid.
    assert (ex2se (EUnop op e) vcnt = SEUnop op (genSEVar_n vcnt)) as Hd.
    {
      simpl.
      reflexivity.
    }
    pose proof unop4 e vcnt ss3 op a H1 as Hd4.
    pose proof unop7 e vcnt op as Hd7.
    destruct Hmid as [ss2 Hmid].
    destruct Hmid.
    pose proof Hp ss2 ss3 H3.
    pose proof Hd4 Hd as Hd4.
    destruct Hd4.
    pose proof H4 x H5 as H4.
    pose proof Hc2 e (S vcnt) s1 ss1 ss2 H H2 as Hc2.
    pose proof Hc1 vcnt (ex2se e (S vcnt)) s1 ss2 ss3 Hc2 H3 as Hc1.
    pose proof IHe (S vcnt) s1 ss1 ss2 x H H2 H4 as IHe.
    pose proof Hd7 x a s1 ss3. 
    tauto.
Qed.

Lemma Split_Serefine_nrm_l_unop {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr),
    (forall (vcnt : nat), Serefine_nrm_l (ex2pre e vcnt) (ex2se e vcnt) e)
    -> 
    (forall (vcnt : nat), Serefine_nrm_r (ex2pre e vcnt) (ex2se e vcnt) e)
    ->
    forall (vcnt : nat) (op: unop), Serefine_nrm_l (ex2pre (EUnop op e) vcnt) (ex2se (EUnop op e) vcnt) (EUnop op e).
Proof.
    unfold Serefine_nrm_l, Serefine_nrm_r.
    simpl.
    sets_unfold.
    intros.
    right.
    tauto.
Qed.

Lemma Split_Serefine_nrm_EVar {NameX : Names} {NPX : NamesProperty}:
      forall (x: var_name) (vcnt: nat), Serefine_nrm (ex2pre (EVar x) vcnt) (ex2se (EVar x) vcnt) (EVar x).
Proof.
    intros.
    unfold Serefine_nrm, Serefine_nrm_l, Serefine_nrm_r, correspond.
    simpl.
    split; sets_unfold; intros.
    + left.
       destruct H.
       pose proof H x a as H.
       destruct H.
       rewrite <- H0 in H1.
       pose proof H3 H1.
       tauto.
    + revert H1.
      unfold deref_sem_nrm, deref_sem_err.
      intros.
      rewrite <- H0 in H1.
       destruct H1 as [b [H1 H2]].
       pose proof mem_split s1 b.
       destruct H.
       destruct H3.
       pose proof H x b as H.
       destruct H as [H5 H6].
       pose proof H6 H1 as H6.
       destruct H3.
       destruct H4.
      - left.
         exists b.
         split; [tauto | ].
         pose proof H3 b x0 H.
         rewrite H2 in H7.
         rewrite <- H7 in H.
         tauto.
      - right.
         right.
         exists b.
         pose proof H x b as H.
         destruct H as [H5 H6].
         pose proof H6 H1. 
         tauto.
Qed.

Lemma ex2se_addrof {NameX : Names}:
    forall (e : expr) (vcnt : nat),
    match e with
      | EVar v =>
        ex2se (EAddrOf e) vcnt = SEAddrOf (genSEVar v)
      | EDeref e0 =>
        ex2se (EAddrOf e) vcnt = genSECV vcnt
      | _ =>
        ex2se (EAddrOf e) vcnt = SEConstOrVar (SEConst 0)
    end.
Proof.
    intros.
    unfold ex2se.
    destruct e; reflexivity.    
Qed.

Lemma addrof4 {NameX : Names} : forall (e : expr) (vcnt : nat) (s0 s : state) (a : int64),
    (Seval_r (ex2se (EAddrOf e) vcnt)).(nrm) s a
    -> ex2se (EAddrOf e) vcnt = SEAddrOf (genSEVar_n vcnt)
    -> (Seval_comlist [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))]).(nrm) s0 s
    -> exists (x : int64), 
        (Seval_r (genSECV vcnt)).(nrm) s x.
Proof.
    intros.
    rewrite H0 in H.
    revert H H1.
    simpl.
    unfold deref_sem_nrm, asgn_deref_sem_nrm. sets_unfold.
    intros.
    destruct H1.
    destruct H1.
    destruct H1.
    destruct H1.
    rewrite H2 in H1.
    destruct H1.
    destruct H3.
    destruct H4.
    destruct H5.
    destruct H6.
    pose proof H6 (nat2Sname vcnt).
    rewrite H in H8.
    rewrite H8 in H1.
    rewrite <- H1 in H5.
    exists x1.
    exists a.
    tauto.
Qed.

Lemma Split_Serefine_nrm_r_addrof {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr),
    (forall (vcnt : nat), Serefine_nrm_l (ex2pre e vcnt) (ex2se e vcnt) e)
    -> 
    (forall (vcnt : nat), Serefine_nrm_r (ex2pre e vcnt) (ex2se e vcnt) e)
    ->
    forall (vcnt : nat), Serefine_nrm_r (ex2pre (EAddrOf e) vcnt) (ex2se (EAddrOf e) vcnt) (EAddrOf e).
Proof.
    simpl.
    unfold Serefine_nrm_l, Serefine_nrm_r.
    intros e IHel IHe vcnt s1 ss1 ss3 a ? ? ?.
    pose proof asgn_vcnt_ex2se_nrm_prop (ex2se e (S vcnt)) vcnt as Hp.
    sets_unfold in Hp.
    pose proof correspond_prop1 as Hc1.
    pose proof correspond_prop2 as Hc2.
    pose proof ex2se_addrof e vcnt as Hd.
    pose proof ex2pre_addrof e vcnt as Hpre.
    destruct e.
    + simpl.
      sets_unfold.
      tauto.
    + revert H0 H1.
      simpl. sets_unfold.
      intros.
      left.
      rewrite <- H0 in H1.
      unfold correspond in H.
      destruct H as [He H100].
      pose proof He x a as He.
      destruct He as [He1 He].
      pose proof He H1.
      tauto.
    + right.
      simpl.
      sets_unfold.
      tauto.
    + right.
      simpl.
      sets_unfold.
      tauto.
    + simpl.
      assert ((Seval_comlist (ex2pre (EDeref e) vcnt)).(nrm) ss1 ss3).
      {
        simpl.
        tauto.
      }
      assert ((Seval_l (ex2se (EDeref e) vcnt)).(nrm) ss3 a).
      {
        revert H1.
        simpl.
        unfold deref_sem_nrm.
        tauto.
      }
      pose proof IHel vcnt s1 ss1 ss3 a H H2 H3.
      simpl in H4.
      tauto.
    + revert H0 H1.
      simpl.
      sets_unfold.
      intros.
      tauto.
Qed.

Lemma Split_Serefine_nrm_l_addrof {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr),
    (forall (vcnt : nat), Serefine_nrm_l (ex2pre e vcnt) (ex2se e vcnt) e)
    -> 
    (forall (vcnt : nat), Serefine_nrm_r (ex2pre e vcnt) (ex2se e vcnt) e)
    ->
    forall (vcnt : nat), Serefine_nrm_l (ex2pre (EAddrOf e) vcnt) (ex2se (EAddrOf e) vcnt) (EAddrOf e).
Proof.
    unfold Serefine_nrm_l, Serefine_nrm_r.
    simpl.
    sets_unfold.
    tauto.
Qed.


Lemma Split_Serefine_nrm_r_binop {NameX : Names} {NPX : NamesProperty}:
    forall (e1 e2 : expr),
    (forall (vcnt : nat), Serefine_nrm_l (ex2pre e1 vcnt) (ex2se e1 vcnt) e1)
    -> 
    (forall (vcnt : nat), Serefine_nrm_r (ex2pre e1 vcnt) (ex2se e1 vcnt) e1)
    ->
    (forall (vcnt : nat), Serefine_nrm_l (ex2pre e2 vcnt) (ex2se e2 vcnt) e2)
    -> 
    (forall (vcnt : nat), Serefine_nrm_r (ex2pre e2 vcnt) (ex2se e2 vcnt) e2)
    ->
    forall (vcnt : nat) (op: binop), Serefine_nrm_r (ex2pre (EBinop op e1 e2) vcnt) (ex2se (EBinop op e1 e2) vcnt) (EBinop op e1 e2).
Proof.
  unfold Serefine_nrm_r.
  intros e1 e2 IHel1 IHe1 IHel2 IHe2 vcnt op s1 ss1 ss3 a ? ? ?.
  pose proof correspond_prop1 as Hc1.
  pose proof correspond_prop2 as Hc2.
  pose proof ex2pre_binop vcnt e1 e2 op as H999.
  destruct op.
  +
  simpl.
  unfold or_sem_nrm, or_sem_err, NonSC_compute_nrm, NonSC_or, SC_or_compute_nrm.
  sets_unfold.
  rewrite H999 in H0.
  pose proof eval_comlist_seq_nrm 
    (ex2pre e1 (S (S vcnt)))
         ([SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e1 (S (S vcnt)))] ++
         [SCIf (genSECV (S vcnt))
            [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 1))]
            (ex2pre e2
               (nat_add (S (S vcnt))
                  (length (ex2pre e1 (S (S vcnt))))) ++
             [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2
                   (nat_add (S (S vcnt))
                      (length (ex2pre e1 (S (S vcnt))))))] ++
             [SCIf (genSECV (S vcnt))
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 1))]
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 0))]])]) ss1 ss3.
  destruct H2.
  pose proof H2 H0.
  sets_unfold in H4.
  destruct H4 as [ss11].
  destruct H4.
  pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H H4.
  pose proof eval_comlist_seq_nrm 
      [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e1 (S (S vcnt)))]
         [SCIf (genSECV (S vcnt))
            [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 1))]
            (ex2pre e2
               (nat_add (S (S vcnt))
                  (length (ex2pre e1 (S (S vcnt))))) ++
             [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2
                   (nat_add (S (S vcnt))
                      (length (ex2pre e1 (S (S vcnt))))))] ++
             [SCIf (genSECV (S vcnt))
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 1))]
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 0))]])] ss11 ss3.
  destruct H7.
  pose proof H7 H5.
  sets_unfold in H9.
  destruct H9 as [ss12].
  destruct H9.
  pose proof correspond_prop1 (S vcnt) (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H6 H9.
  simpl in H10.
  sets_unfold in H10.
  destruct H10.
  destruct H10.
  rewrite H12 in H10.
  destruct H10.
  ++
  destruct H10.
  destruct H10.
  unfold test_true in H10.
  sets_unfold in H10.
  destruct H10.
  rewrite <- H14 in H13.
  destruct H13.
  destruct H13.
  rewrite H15 in H13.
  destruct H13 as [i1[i2[?[?[?[?[?]]]]]]].
  revert H1.
  simpl.
  unfold deref_sem_nrm.
  intros.
  destruct H1.
  destruct H1.
  pose proof H19 (nat2Sname vcnt).
  rewrite H1 in H22.
  rewrite H13 in H22.
  rewrite H22 in H18.
  rewrite H18 in H21.
  injection H21.
  intros.
  rewrite H23 in H16.
  destruct H10.
  destruct H10.
  assert ((Seval_r (genSECV (S vcnt))).(nrm) ss12 x3).
  {
    revert H10.
    simpl.
    tauto.
  }
  pose proof asgn_vcnt_ex2se_nrm_prop (ex2se e1 (S (S vcnt))) (S vcnt) ss11 ss12 H9 x3 H25.
  pose proof IHe1 (S(S vcnt)) s1 ss1 ss11 x3 H H4 H26.
  destruct H27; [|tauto].
  left.
  exists x3.
  tauto.
  ++
  destruct H10.
  destruct H10.
  unfold test_false in H10.
  sets_unfold in H10.
  destruct H10.
  assert ((Seval_r (genSECV (S vcnt))).(nrm) ss12 (Int64.repr 0)) as H50.
  {
    revert H10.
    simpl.
    tauto.
  }
  pose proof asgn_vcnt_ex2se_nrm_prop (ex2se e1 (S (S vcnt))) (S vcnt) ss11 ss12 H9 (Int64.repr 0) H50 as H51.
  pose proof IHe1 (S(S vcnt)) s1 ss1 ss11 (Int64.repr 0) H H4 H51 as H52.
  destruct H52 as [H52 | H52]; [|tauto].
  rewrite <- H14 in H13.
  pose proof eval_comlist_seq_nrm
    (ex2pre e2
            (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))
          ([SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2
                (S
                   (S
                      (nat_add vcnt
                         (length (ex2pre e1 (S (S vcnt)))))))),
          SCIf (genSECV (S vcnt))
            [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1))]
            [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0))]]) ss12 ss3.
  destruct H15.
  pose proof H15 H13.
  sets_unfold in H17.
  destruct H17 as [ss13].
  destruct H17.
  pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H11 H17.
  pose proof eval_comlist_seq_nrm 
    [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2
               (S
                  (S
                     (nat_add vcnt
                        (length (ex2pre e1 (S (S vcnt))))))))]
        [SCIf (genSECV (S vcnt))
           [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1))]
           [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0))]] ss13 ss3.
  destruct H20.
  pose proof H20 H18.
  sets_unfold in H22.
  destruct H22 as [ss14].
  destruct H22.
  pose proof correspond_prop1 (S vcnt) (ex2se e2
  (S
     (S
        (nat_add vcnt
           (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss14 H19 H22.
  simpl in H23.
  sets_unfold in H23.
  destruct H23.
  destruct H23.
  rewrite H25 in H23.
  destruct H23.
  +++
  destruct H23.
  destruct H23.
  unfold test_true in H23.
  sets_unfold in H23.
  destruct H23.
  rewrite <- H27 in H26.
  destruct H26.
  destruct H26.
  rewrite H28 in H26.
  destruct H26 as [i3[i4[?[?[?[?[?]]]]]]].
  revert H1.
  simpl.
  unfold deref_sem_nrm.
  intros.
  destruct H1.
  destruct H1.
  destruct H23.
  pose proof H32 (nat2Sname vcnt).
  rewrite H1 in H35.
  rewrite H26 in H35.
  rewrite <- H35 in H34.
  rewrite H31 in H34.
  injection H34 as ?.
  rewrite H34 in H29.
  assert ((Seval_r (genSECV (S vcnt))).(nrm) ss14 x5).
  {
    revert H23.
    simpl.
    tauto.
  }
  pose proof asgn_vcnt_ex2se_nrm_prop (ex2se e2
  (S
     (S
        (nat_add vcnt
           (length (ex2pre e1 (S (S vcnt)))))))) (S vcnt) ss13 ss14 H22 x5 H36.
  pose proof IHe2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 x5 H11 H17 H37.
  destruct H38.
  ++++
  left.
  exists (Int64.repr 0).
  split; [tauto|].
  right.
  split; [tauto|].
  exists x5.
  tauto.
  ++++
  right.
  right.
  exists (Int64.repr 0).
  tauto.
  +++
  destruct H23.
  destruct H23.
  unfold test_false in H23.
  sets_unfold in H23.
  destruct H23.
  rewrite <- H27 in H26.
  destruct H26.
  destruct H26.
  rewrite H28 in H26.
  destruct H26 as [i3[i4[?[?[?[?[?]]]]]]].
  revert H1.
  simpl.
  unfold deref_sem_nrm.
  intros.
  destruct H1.
  destruct H1.
  destruct H23.
  pose proof H32 (nat2Sname vcnt).
  rewrite H1 in H35.
  rewrite H26 in H35.
  rewrite <- H35 in H34.
  rewrite H31 in H34.
  injection H34 as ?.
  rewrite H34 in H29.
  assert ((Seval_r (genSECV (S vcnt))).(nrm) ss14 (Int64.repr 0)).
  {
    revert H23.
    simpl.
    unfold deref_sem_nrm.
    intros.
    exists x5.
    tauto.
  }
  pose proof asgn_vcnt_ex2se_nrm_prop (ex2se e2
  (S
     (S
        (nat_add vcnt
           (length (ex2pre e1 (S (S vcnt)))))))) (S vcnt) ss13 ss14 H22 (Int64.repr 0) H36.
  pose proof IHe2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 (Int64.repr 0) H11 H17 H37.
  destruct H38.
  ++++
  left.
  exists (Int64.repr 0).
  split; [tauto|].
  right.
  split; [tauto|].
  exists (Int64.repr 0).
  tauto.
  ++++
  right.
  right.
  exists (Int64.repr 0).
  tauto.
  +
  simpl.
  unfold and_sem_nrm, and_sem_err, NonSC_compute_nrm, NonSC_and, SC_and_compute_nrm.
  sets_unfold.
  rewrite H999 in H0.
  pose proof eval_comlist_seq_nrm 
    (ex2pre e1 (S (S vcnt)))
         ([SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e1 (S (S vcnt)))] ++
         [SCIf (genSECV (S vcnt))
            (ex2pre e2
               (nat_add (S (S vcnt))
                  (length (ex2pre e1 (S (S vcnt))))) ++
             [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2
                   (nat_add (S (S vcnt))
                      (length (ex2pre e1 (S (S vcnt))))))] ++
             [SCIf (genSECV (S vcnt))
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 1))]
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 0))]])
            [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 0))]]) ss1 ss3.
  destruct H2.
  pose proof H2 H0.
  sets_unfold in H4.
  destruct H4 as [ss11].
  destruct H4.
  pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H H4.
  pose proof eval_comlist_seq_nrm 
      [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e1 (S (S vcnt)))]
         [SCIf (genSECV (S vcnt))
            (ex2pre e2
               (nat_add (S (S vcnt))
                  (length (ex2pre e1 (S (S vcnt))))) ++
             [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2
                   (nat_add (S (S vcnt))
                      (length (ex2pre e1 (S (S vcnt))))))] ++
             [SCIf (genSECV (S vcnt))
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 1))]
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 0))]])
              [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 0))]] ss11 ss3.
  destruct H7.
  pose proof H7 H5.
  sets_unfold in H9.
  destruct H9 as [ss12].
  destruct H9.
  pose proof correspond_prop1 (S vcnt) (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H6 H9.
  simpl in H10.
  sets_unfold in H10.
  destruct H10.
  destruct H10.
  rewrite H12 in H10.
  destruct H10.
  ++
  destruct H10.
  destruct H10.
  unfold test_true in H10.
  sets_unfold in H10.
  destruct H10.
  destruct H10.
  assert ((Seval_r (genSECV (S vcnt))).(nrm) ss12 x1) as H50.
  {
    revert H10.
    simpl.
    tauto.
  }
  pose proof asgn_vcnt_ex2se_nrm_prop (ex2se e1 (S (S vcnt))) (S vcnt) ss11 ss12 H9 x1 H50 as H51.
  pose proof IHe1 (S(S vcnt)) s1 ss1 ss11 x1 H H4 H51 as H52.
  destruct H52 as [H52 | H52]; [|tauto].
  rewrite <- H14 in H13.
  pose proof eval_comlist_seq_nrm
    (ex2pre e2
            (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))
          ([SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2
                (S
                   (S
                      (nat_add vcnt
                         (length (ex2pre e1 (S (S vcnt)))))))),
          SCIf (genSECV (S vcnt))
            [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1))]
            [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0))]]) ss12 ss3.
  destruct H15.
  pose proof H15 H13.
  sets_unfold in H17.
  destruct H17 as [ss13].
  destruct H17.
  pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H11 H17.
  pose proof eval_comlist_seq_nrm 
    [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2
               (S
                  (S
                     (nat_add vcnt
                        (length (ex2pre e1 (S (S vcnt))))))))]
        [SCIf (genSECV (S vcnt))
           [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1))]
           [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0))]] ss13 ss3.
  destruct H20.
  pose proof H20 H18.
  sets_unfold in H22.
  destruct H22 as [ss14].
  destruct H22.
  pose proof correspond_prop1 (S vcnt) (ex2se e2
  (S
     (S
        (nat_add vcnt
           (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss14 H19 H22.
  simpl in H23.
  sets_unfold in H23.
  destruct H23.
  destruct H23.
  rewrite H25 in H23.
  destruct H23.
  +++
  destruct H23.
  destruct H23.
  unfold test_true in H23.
  sets_unfold in H23.
  destruct H23.
  rewrite <- H27 in H26.
  destruct H26.
  destruct H26.
  rewrite H28 in H26.
  destruct H26 as [i3[i4[?[?[?[?[?]]]]]]].
  revert H1.
  simpl.
  unfold deref_sem_nrm.
  intros.
  destruct H1.
  destruct H1.
  destruct H23.
  pose proof H32 (nat2Sname vcnt).
  rewrite H1 in H35.
  rewrite H26 in H35.
  rewrite <- H35 in H34.
  rewrite H31 in H34.
  injection H34 as ?.
  rewrite H34 in H29.
  assert ((Seval_r (genSECV (S vcnt))).(nrm) ss14 x6).
  {
    revert H23.
    simpl.
    tauto.
  }
  pose proof asgn_vcnt_ex2se_nrm_prop (ex2se e2
  (S
     (S
        (nat_add vcnt
           (length (ex2pre e1 (S (S vcnt)))))))) (S vcnt) ss13 ss14 H22 x6 H36.
  pose proof IHe2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 x6 H11 H17 H37.
  destruct H38.
  ++++
  left.
  exists x1.
  split; [tauto|].
  right.
  split; [tauto|].
  exists x6.
  tauto.
  ++++
  right.
  right.
  exists x1.
  tauto.
  +++
  destruct H23.
  destruct H23.
  unfold test_false in H23.
  sets_unfold in H23.
  destruct H23.
  rewrite <- H27 in H26.
  destruct H26.
  destruct H26.
  rewrite H28 in H26.
  destruct H26 as [i3[i4[?[?[?[?[?]]]]]]].
  revert H1.
  simpl.
  unfold deref_sem_nrm.
  intros.
  destruct H1.
  destruct H1.
  destruct H23.
  pose proof H32 (nat2Sname vcnt).
  rewrite H1 in H35.
  rewrite H26 in H35.
  rewrite <- H35 in H34.
  rewrite H31 in H34.
  injection H34 as ?.
  rewrite H34 in H29.
  assert ((Seval_r (genSECV (S vcnt))).(nrm) ss14 (Int64.repr 0)).
  {
    revert H23.
    simpl.
    unfold deref_sem_nrm.
    intros.
    exists x6.
    tauto.
  }
  pose proof asgn_vcnt_ex2se_nrm_prop (ex2se e2
  (S
     (S
        (nat_add vcnt
           (length (ex2pre e1 (S (S vcnt)))))))) (S vcnt) ss13 ss14 H22 (Int64.repr 0) H36.
  pose proof IHe2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 (Int64.repr 0) H11 H17 H37.
  destruct H38.
  ++++
  left.
  exists x1.
  split; [tauto|].
  right.
  split; [tauto|].
  exists (Int64.repr 0).
  tauto.
  ++++
  right.
  right.
  exists x1.
  tauto.
  ++
  destruct H10.
  destruct H10.
  unfold test_true in H10.
  sets_unfold in H10.
  destruct H10.
  rewrite <- H14 in H13.
  destruct H13.
  destruct H13.
  rewrite H15 in H13.
  destruct H13 as [i1[i2[?[?[?[?[?]]]]]]].
  revert H1.
  simpl.
  unfold deref_sem_nrm.
  intros.
  destruct H1.
  destruct H1.
  pose proof H19 (nat2Sname vcnt).
  rewrite H1 in H22.
  rewrite H13 in H22.
  rewrite H22 in H18.
  rewrite H18 in H21.
  injection H21.
  intros.
  rewrite H23 in H16.
  destruct H10.
  assert ((Seval_r (genSECV (S vcnt))).(nrm) ss12 (Int64.repr 0)).
  {
    revert H10.
    simpl.
    unfold deref_sem_nrm.
    intros.
    exists x3.
    tauto.
  }
  pose proof asgn_vcnt_ex2se_nrm_prop (ex2se e1 (S (S vcnt))) (S vcnt) ss11 ss12 H9 (Int64.repr 0) H24.
  pose proof IHe1 (S(S vcnt)) s1 ss1 ss11 (Int64.repr 0) H H4 H25.
  destruct H26; [|tauto].
  left.
  exists (Int64.repr 0).
  tauto.
  + simpl in H0.
      assert (
        (Seval_comlist
        (ex2pre e1 (S (S vcnt)) ++
         [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
           ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) ++
            [SCAsgnVar (nat2Sname (S vcnt))
               (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1
       ss3).
      { simpl. tauto. }
      clear H0.
      pose proof midstate_binop vcnt e1 e2 ss1 ss3 H2.
      destruct H0 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
      pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H H0.
      pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H6 H3.
      pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H7 H4.
      pose proof Hc1 (S vcnt) (ex2se e2
        (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss3 H8 H5.
      pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
      sets_unfold in Hp.
      pose proof Hp (ex2se e1 (S (S vcnt))) vcnt ss11 ss12 H3 as Hp1.
      pose proof Hp (ex2se e2
        (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) (S vcnt) ss13 ss3 H5 as Hp2.
      assert (exists (x : int64), (Seval_r (genSECV (S vcnt))).(nrm) ss3 x) as Hd4.
      {
        simpl in H1.
        revert H1.
        simpl.
        unfold deref_sem_nrm, cmp_sem_nrm.
        intros.
        destruct H1 as [x0 [x1 ?]].
        destruct H1.
        destruct H10.
        destruct H10.
        exists x1, x.
        tauto.
      }
      destruct Hd4.
      pose proof Hp2 x H10.
      pose proof IHe2  (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 x H7 H4 H11.
      assert (exists (x : int64), (Seval_r (genSECV vcnt)).(nrm) ss12 x) as Hd5.
      {
        simpl in H1.
        revert H1.
        simpl.
        unfold deref_sem_nrm, cmp_sem_nrm.
        intros.
        destruct H1 as [x0 [x1 ?]].
        destruct H1.
        destruct H1.
        pose proof greater_vcnt1 as G1.
        pose proof greater_vcnt2 as G2.
        pose proof G2 vcnt ss13 ss3 e1 e2 H5.
        pose proof G1 vcnt ss12 ss13 e1 e2 H4.
        rewrite <- H15 in H14.
        destruct H1.
        rewrite <- H1 in H16.
        rewrite <- H14 in H16.
        exists x0, (ss12.(env) (nat2Sname vcnt)).
        tauto.
      }
      destruct Hd5.
      pose proof Hp1 x0 H13. 
      pose proof IHe1 (S (S vcnt)) s1 ss1 ss11 x0 H H0 H14.
      destruct H12, H15.
      - revert H1 H15 H12 H13 H10.
        simpl.
        unfold cmp_sem_nrm, deref_sem_nrm, cmp_compute_nrm.
        sets_unfold.
        intros.
        destruct H1 as [x1 [x2 [? [? ?]]]].
        left.
        exists x1, x2.
        destruct H1.
        destruct H1. 
        destruct H16.
        destruct H16.
        destruct H13.
        destruct H13.
        destruct H10.
        destruct H10.
        pose proof greater_vcnt1 as G1.
        pose proof greater_vcnt2 as G2.
        pose proof G2 vcnt ss13 ss3 e1 e2 H5 as G2.
        pose proof G1 vcnt ss12 ss13 e1 e2 H4 as G1.
        rewrite H10 in H16.
        rewrite <- H16 in H19.
        rewrite H19 in H21.
        pose proof some_val x2 x.
        destruct H22.
        pose proof H22 H21.
        rewrite <- H24 in H12.
        rewrite H13 in G1.
        rewrite G2 in G1.
        rewrite H1 in G1.
        rewrite H20 in G1.
        rewrite H18 in G1.
        pose proof some_val x0 x1.
        destruct H25.
        pose proof H25 G1.
        rewrite H27 in H15.
        tauto.
      - right.
        simpl.
        sets_unfold.
        tauto.
      - right.
        simpl.
        sets_unfold.
        tauto.
      - right.
        simpl.
        sets_unfold.
        tauto.
  + simpl in H0.
      assert (
        (Seval_comlist
        (ex2pre e1 (S (S vcnt)) ++
          [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
            ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) ++
            [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1
        ss3).
      { simpl. tauto. }
      clear H0.
      pose proof midstate_binop vcnt e1 e2 ss1 ss3 H2.
      destruct H0 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
      pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H H0.
      pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H6 H3.
      pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H7 H4.
      pose proof Hc1 (S vcnt) (ex2se e2
        (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss3 H8 H5.
      pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
      sets_unfold in Hp.
      pose proof Hp (ex2se e1 (S (S vcnt))) vcnt ss11 ss12 H3 as Hp1.
      pose proof Hp (ex2se e2
        (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) (S vcnt) ss13 ss3 H5 as Hp2.
      assert (exists (x : int64), (Seval_r (genSECV (S vcnt))).(nrm) ss3 x) as Hd4.
      {
        simpl in H1.
        revert H1.
        simpl.
        unfold deref_sem_nrm, cmp_sem_nrm.
        intros.
        destruct H1 as [x0 [x1 ?]].
        destruct H1.
        destruct H10.
        destruct H10.
        exists x1, x.
        tauto.
      }
      destruct Hd4.
      pose proof Hp2 x H10.
      pose proof IHe2  (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 x H7 H4 H11.
      assert (exists (x : int64), (Seval_r (genSECV vcnt)).(nrm) ss12 x) as Hd5.
      {
        simpl in H1.
        revert H1.
        simpl.
        unfold deref_sem_nrm, cmp_sem_nrm.
        intros.
        destruct H1 as [x0 [x1 ?]].
        destruct H1.
        destruct H1.
        pose proof greater_vcnt1 as G1.
        pose proof greater_vcnt2 as G2.
        pose proof G2 vcnt ss13 ss3 e1 e2 H5.
        pose proof G1 vcnt ss12 ss13 e1 e2 H4.
        rewrite <- H15 in H14.
        destruct H1.
        rewrite <- H1 in H16.
        rewrite <- H14 in H16.
        exists x0, (ss12.(env) (nat2Sname vcnt)).
        tauto.
      }
      destruct Hd5.
      pose proof Hp1 x0 H13. 
      pose proof IHe1 (S (S vcnt)) s1 ss1 ss11 x0 H H0 H14.
      destruct H12, H15.
      - revert H1 H15 H12 H13 H10.
        simpl.
        unfold cmp_sem_nrm, deref_sem_nrm, cmp_compute_nrm.
        sets_unfold.
        intros.
        destruct H1 as [x1 [x2 [? [? ?]]]].
        left.
        exists x1, x2.
        destruct H1.
        destruct H1. 
        destruct H16.
        destruct H16.
        destruct H13.
        destruct H13.
        destruct H10.
        destruct H10.
        pose proof greater_vcnt1 as G1.
        pose proof greater_vcnt2 as G2.
        pose proof G2 vcnt ss13 ss3 e1 e2 H5 as G2.
        pose proof G1 vcnt ss12 ss13 e1 e2 H4 as G1.
        rewrite H10 in H16.
        rewrite <- H16 in H19.
        rewrite H19 in H21.
        pose proof some_val x2 x.
        destruct H22.
        pose proof H22 H21.
        rewrite <- H24 in H12.
        rewrite H13 in G1.
        rewrite G2 in G1.
        rewrite H1 in G1.
        rewrite H20 in G1.
        rewrite H18 in G1.
        pose proof some_val x0 x1.
        destruct H25.
        pose proof H25 G1.
        rewrite H27 in H15.
        tauto.
      - right.
        simpl.
        sets_unfold.
        tauto.
      - right.
        simpl.
        sets_unfold.
        tauto.
      - right.
        simpl.
        sets_unfold.
        tauto.
  + simpl in H0.
      assert (
        (Seval_comlist
        (ex2pre e1 (S (S vcnt)) ++
          [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
            ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) ++
            [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1
        ss3).
      { simpl. tauto. }
      clear H0.
      pose proof midstate_binop vcnt e1 e2 ss1 ss3 H2.
      destruct H0 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
      pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H H0.
      pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H6 H3.
      pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H7 H4.
      pose proof Hc1 (S vcnt) (ex2se e2
        (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss3 H8 H5.
      pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
      sets_unfold in Hp.
      pose proof Hp (ex2se e1 (S (S vcnt))) vcnt ss11 ss12 H3 as Hp1.
      pose proof Hp (ex2se e2
        (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) (S vcnt) ss13 ss3 H5 as Hp2.
      assert (exists (x : int64), (Seval_r (genSECV (S vcnt))).(nrm) ss3 x) as Hd4.
      {
        simpl in H1.
        revert H1.
        simpl.
        unfold deref_sem_nrm, cmp_sem_nrm.
        intros.
        destruct H1 as [x0 [x1 ?]].
        destruct H1.
        destruct H10.
        destruct H10.
        exists x1, x.
        tauto.
      }
      destruct Hd4.
      pose proof Hp2 x H10.
      pose proof IHe2  (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 x H7 H4 H11.
      assert (exists (x : int64), (Seval_r (genSECV vcnt)).(nrm) ss12 x) as Hd5.
      {
        simpl in H1.
        revert H1.
        simpl.
        unfold deref_sem_nrm, cmp_sem_nrm.
        intros.
        destruct H1 as [x0 [x1 ?]].
        destruct H1.
        destruct H1.
        pose proof greater_vcnt1 as G1.
        pose proof greater_vcnt2 as G2.
        pose proof G2 vcnt ss13 ss3 e1 e2 H5.
        pose proof G1 vcnt ss12 ss13 e1 e2 H4.
        rewrite <- H15 in H14.
        destruct H1.
        rewrite <- H1 in H16.
        rewrite <- H14 in H16.
        exists x0, (ss12.(env) (nat2Sname vcnt)).
        tauto.
      }
      destruct Hd5.
      pose proof Hp1 x0 H13. 
      pose proof IHe1 (S (S vcnt)) s1 ss1 ss11 x0 H H0 H14.
      destruct H12, H15.
      - revert H1 H15 H12 H13 H10.
        simpl.
        unfold cmp_sem_nrm, deref_sem_nrm, cmp_compute_nrm.
        sets_unfold.
        intros.
        destruct H1 as [x1 [x2 [? [? ?]]]].
        left.
        exists x1, x2.
        destruct H1.
        destruct H1. 
        destruct H16.
        destruct H16.
        destruct H13.
        destruct H13.
        destruct H10.
        destruct H10.
        pose proof greater_vcnt1 as G1.
        pose proof greater_vcnt2 as G2.
        pose proof G2 vcnt ss13 ss3 e1 e2 H5 as G2.
        pose proof G1 vcnt ss12 ss13 e1 e2 H4 as G1.
        rewrite H10 in H16.
        rewrite <- H16 in H19.
        rewrite H19 in H21.
        pose proof some_val x2 x.
        destruct H22.
        pose proof H22 H21.
        rewrite <- H24 in H12.
        rewrite H13 in G1.
        rewrite G2 in G1.
        rewrite H1 in G1.
        rewrite H20 in G1.
        rewrite H18 in G1.
        pose proof some_val x0 x1.
        destruct H25.
        pose proof H25 G1.
        rewrite H27 in H15.
        tauto.
      - right.
        simpl.
        sets_unfold.
        tauto.
      - right.
        simpl.
        sets_unfold.
        tauto.
      - right.
        simpl.
        sets_unfold.
        tauto.
        + simpl in H0.
        assert (
          (Seval_comlist
          (ex2pre e1 (S (S vcnt)) ++
            [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
              ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) ++
              [SCAsgnVar (nat2Sname (S vcnt))
                  (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1
          ss3).
        { simpl. tauto. }
        clear H0.
        pose proof midstate_binop vcnt e1 e2 ss1 ss3 H2.
        destruct H0 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
        pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H H0.
        pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H6 H3.
        pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H7 H4.
        pose proof Hc1 (S vcnt) (ex2se e2
          (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss3 H8 H5.
        pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
        sets_unfold in Hp.
        pose proof Hp (ex2se e1 (S (S vcnt))) vcnt ss11 ss12 H3 as Hp1.
        pose proof Hp (ex2se e2
          (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) (S vcnt) ss13 ss3 H5 as Hp2.
        assert (exists (x : int64), (Seval_r (genSECV (S vcnt))).(nrm) ss3 x) as Hd4.
        {
          simpl in H1.
          revert H1.
          simpl.
          unfold deref_sem_nrm, cmp_sem_nrm.
          intros.
          destruct H1 as [x0 [x1 ?]].
          destruct H1.
          destruct H10.
          destruct H10.
          exists x1, x.
          tauto.
        }
        destruct Hd4.
        pose proof Hp2 x H10.
        pose proof IHe2  (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 x H7 H4 H11.
        assert (exists (x : int64), (Seval_r (genSECV vcnt)).(nrm) ss12 x) as Hd5.
        {
          simpl in H1.
          revert H1.
          simpl.
          unfold deref_sem_nrm, cmp_sem_nrm.
          intros.
          destruct H1 as [x0 [x1 ?]].
          destruct H1.
          destruct H1.
          pose proof greater_vcnt1 as G1.
          pose proof greater_vcnt2 as G2.
          pose proof G2 vcnt ss13 ss3 e1 e2 H5.
          pose proof G1 vcnt ss12 ss13 e1 e2 H4.
          rewrite <- H15 in H14.
          destruct H1.
          rewrite <- H1 in H16.
          rewrite <- H14 in H16.
          exists x0, (ss12.(env) (nat2Sname vcnt)).
          tauto.
        }
        destruct Hd5.
        pose proof Hp1 x0 H13. 
        pose proof IHe1 (S (S vcnt)) s1 ss1 ss11 x0 H H0 H14.
        destruct H12, H15.
        - revert H1 H15 H12 H13 H10.
          simpl.
          unfold cmp_sem_nrm, deref_sem_nrm, cmp_compute_nrm.
          sets_unfold.
          intros.
          destruct H1 as [x1 [x2 [? [? ?]]]].
          left.
          exists x1, x2.
          destruct H1.
          destruct H1. 
          destruct H16.
          destruct H16.
          destruct H13.
          destruct H13.
          destruct H10.
          destruct H10.
          pose proof greater_vcnt1 as G1.
          pose proof greater_vcnt2 as G2.
          pose proof G2 vcnt ss13 ss3 e1 e2 H5 as G2.
          pose proof G1 vcnt ss12 ss13 e1 e2 H4 as G1.
          rewrite H10 in H16.
          rewrite <- H16 in H19.
          rewrite H19 in H21.
          pose proof some_val x2 x.
          destruct H22.
          pose proof H22 H21.
          rewrite <- H24 in H12.
          rewrite H13 in G1.
          rewrite G2 in G1.
          rewrite H1 in G1.
          rewrite H20 in G1.
          rewrite H18 in G1.
          pose proof some_val x0 x1.
          destruct H25.
          pose proof H25 G1.
          rewrite H27 in H15.
          tauto.
        - right.
          simpl.
          sets_unfold.
          tauto.
        - right.
          simpl.
          sets_unfold.
          tauto.
        - right.
          simpl.
          sets_unfold.
          tauto.
  + simpl in H0.
    assert (
      (Seval_comlist
      (ex2pre e1 (S (S vcnt)) ++
        [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
          ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) ++
          [SCAsgnVar (nat2Sname (S vcnt))
              (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1
      ss3).
    { simpl. tauto. }
    clear H0.
    pose proof midstate_binop vcnt e1 e2 ss1 ss3 H2.
    destruct H0 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
    pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H H0.
    pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H6 H3.
    pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H7 H4.
    pose proof Hc1 (S vcnt) (ex2se e2
      (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss3 H8 H5.
    pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
    sets_unfold in Hp.
    pose proof Hp (ex2se e1 (S (S vcnt))) vcnt ss11 ss12 H3 as Hp1.
    pose proof Hp (ex2se e2
      (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) (S vcnt) ss13 ss3 H5 as Hp2.
    assert (exists (x : int64), (Seval_r (genSECV (S vcnt))).(nrm) ss3 x) as Hd4.
    {
      simpl in H1.
      revert H1.
      simpl.
      unfold deref_sem_nrm, cmp_sem_nrm.
      intros.
      destruct H1 as [x0 [x1 ?]].
      destruct H1.
      destruct H10.
      destruct H10.
      exists x1, x.
      tauto.
    }
    destruct Hd4.
    pose proof Hp2 x H10.
    pose proof IHe2  (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 x H7 H4 H11.
    assert (exists (x : int64), (Seval_r (genSECV vcnt)).(nrm) ss12 x) as Hd5.
    {
      simpl in H1.
      revert H1.
      simpl.
      unfold deref_sem_nrm, cmp_sem_nrm.
      intros.
      destruct H1 as [x0 [x1 ?]].
      destruct H1.
      destruct H1.
      pose proof greater_vcnt1 as G1.
      pose proof greater_vcnt2 as G2.
      pose proof G2 vcnt ss13 ss3 e1 e2 H5.
      pose proof G1 vcnt ss12 ss13 e1 e2 H4.
      rewrite <- H15 in H14.
      destruct H1.
      rewrite <- H1 in H16.
      rewrite <- H14 in H16.
      exists x0, (ss12.(env) (nat2Sname vcnt)).
      tauto.
    }
    destruct Hd5.
    pose proof Hp1 x0 H13. 
    pose proof IHe1 (S (S vcnt)) s1 ss1 ss11 x0 H H0 H14.
    destruct H12, H15.
    - revert H1 H15 H12 H13 H10.
      simpl.
      unfold cmp_sem_nrm, deref_sem_nrm, cmp_compute_nrm.
      sets_unfold.
      intros.
      destruct H1 as [x1 [x2 [? [? ?]]]].
      left.
      exists x1, x2.
      destruct H1.
      destruct H1. 
      destruct H16.
      destruct H16.
      destruct H13.
      destruct H13.
      destruct H10.
      destruct H10.
      pose proof greater_vcnt1 as G1.
      pose proof greater_vcnt2 as G2.
      pose proof G2 vcnt ss13 ss3 e1 e2 H5 as G2.
      pose proof G1 vcnt ss12 ss13 e1 e2 H4 as G1.
      rewrite H10 in H16.
      rewrite <- H16 in H19.
      rewrite H19 in H21.
      pose proof some_val x2 x.
      destruct H22.
      pose proof H22 H21.
      rewrite <- H24 in H12.
      rewrite H13 in G1.
      rewrite G2 in G1.
      rewrite H1 in G1.
      rewrite H20 in G1.
      rewrite H18 in G1.
      pose proof some_val x0 x1.
      destruct H25.
      pose proof H25 G1.
      rewrite H27 in H15.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto.
  + simpl in H0.
    assert (
      (Seval_comlist
      (ex2pre e1 (S (S vcnt)) ++
        [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
          ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) ++
          [SCAsgnVar (nat2Sname (S vcnt))
              (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1
      ss3).
    { simpl. tauto. }
    clear H0.
    pose proof midstate_binop vcnt e1 e2 ss1 ss3 H2.
    destruct H0 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
    pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H H0.
    pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H6 H3.
    pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H7 H4.
    pose proof Hc1 (S vcnt) (ex2se e2
      (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss3 H8 H5.
    pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
    sets_unfold in Hp.
    pose proof Hp (ex2se e1 (S (S vcnt))) vcnt ss11 ss12 H3 as Hp1.
    pose proof Hp (ex2se e2
      (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) (S vcnt) ss13 ss3 H5 as Hp2.
    assert (exists (x : int64), (Seval_r (genSECV (S vcnt))).(nrm) ss3 x) as Hd4.
    {
      simpl in H1.
      revert H1.
      simpl.
      unfold deref_sem_nrm, cmp_sem_nrm.
      intros.
      destruct H1 as [x0 [x1 ?]].
      destruct H1.
      destruct H10.
      destruct H10.
      exists x1, x.
      tauto.
    }
    destruct Hd4.
    pose proof Hp2 x H10.
    pose proof IHe2  (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 x H7 H4 H11.
    assert (exists (x : int64), (Seval_r (genSECV vcnt)).(nrm) ss12 x) as Hd5.
    {
      simpl in H1.
      revert H1.
      simpl.
      unfold deref_sem_nrm, cmp_sem_nrm.
      intros.
      destruct H1 as [x0 [x1 ?]].
      destruct H1.
      destruct H1.
      pose proof greater_vcnt1 as G1.
      pose proof greater_vcnt2 as G2.
      pose proof G2 vcnt ss13 ss3 e1 e2 H5.
      pose proof G1 vcnt ss12 ss13 e1 e2 H4.
      rewrite <- H15 in H14.
      destruct H1.
      rewrite <- H1 in H16.
      rewrite <- H14 in H16.
      exists x0, (ss12.(env) (nat2Sname vcnt)).
      tauto.
    }
    destruct Hd5.
    pose proof Hp1 x0 H13. 
    pose proof IHe1 (S (S vcnt)) s1 ss1 ss11 x0 H H0 H14.
    destruct H12, H15.
    - revert H1 H15 H12 H13 H10.
      simpl.
      unfold cmp_sem_nrm, deref_sem_nrm, cmp_compute_nrm.
      sets_unfold.
      intros.
      destruct H1 as [x1 [x2 [? [? ?]]]].
      left.
      exists x1, x2.
      destruct H1.
      destruct H1. 
      destruct H16.
      destruct H16.
      destruct H13.
      destruct H13.
      destruct H10.
      destruct H10.
      pose proof greater_vcnt1 as G1.
      pose proof greater_vcnt2 as G2.
      pose proof G2 vcnt ss13 ss3 e1 e2 H5 as G2.
      pose proof G1 vcnt ss12 ss13 e1 e2 H4 as G1.
      rewrite H10 in H16.
      rewrite <- H16 in H19.
      rewrite H19 in H21.
      pose proof some_val x2 x.
      destruct H22.
      pose proof H22 H21.
      rewrite <- H24 in H12.
      rewrite H13 in G1.
      rewrite G2 in G1.
      rewrite H1 in G1.
      rewrite H20 in G1.
      rewrite H18 in G1.
      pose proof some_val x0 x1.
      destruct H25.
      pose proof H25 G1.
      rewrite H27 in H15.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto. 
  + simpl in H0.
    assert (
      (Seval_comlist
      (ex2pre e1 (S (S vcnt)) ++
        [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
          ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) ++
          [SCAsgnVar (nat2Sname (S vcnt))
              (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1
      ss3).
    { simpl. tauto. }
    clear H0.
    pose proof midstate_binop vcnt e1 e2 ss1 ss3 H2.
    destruct H0 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
    pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H H0.
    pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H6 H3.
    pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H7 H4.
    pose proof Hc1 (S vcnt) (ex2se e2
      (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss3 H8 H5.
    pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
    sets_unfold in Hp.
    pose proof Hp (ex2se e1 (S (S vcnt))) vcnt ss11 ss12 H3 as Hp1.
    pose proof Hp (ex2se e2
      (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) (S vcnt) ss13 ss3 H5 as Hp2.
    assert (exists (x : int64), (Seval_r (genSECV (S vcnt))).(nrm) ss3 x) as Hd4.
    {
      simpl in H1.
      revert H1.
      simpl.
      unfold deref_sem_nrm, cmp_sem_nrm.
      intros.
      destruct H1 as [x0 [x1 ?]].
      destruct H1.
      destruct H10.
      destruct H10.
      exists x1, x.
      tauto.
    }
    destruct Hd4.
    pose proof Hp2 x H10.
    pose proof IHe2  (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 x H7 H4 H11.
    assert (exists (x : int64), (Seval_r (genSECV vcnt)).(nrm) ss12 x) as Hd5.
    {
      simpl in H1.
      revert H1.
      simpl.
      unfold deref_sem_nrm, cmp_sem_nrm.
      intros.
      destruct H1 as [x0 [x1 ?]].
      destruct H1.
      destruct H1.
      pose proof greater_vcnt1 as G1.
      pose proof greater_vcnt2 as G2.
      pose proof G2 vcnt ss13 ss3 e1 e2 H5.
      pose proof G1 vcnt ss12 ss13 e1 e2 H4.
      rewrite <- H15 in H14.
      destruct H1.
      rewrite <- H1 in H16.
      rewrite <- H14 in H16.
      exists x0, (ss12.(env) (nat2Sname vcnt)).
      tauto.
    }
    destruct Hd5.
    pose proof Hp1 x0 H13. 
    pose proof IHe1 (S (S vcnt)) s1 ss1 ss11 x0 H H0 H14.
    destruct H12, H15.
    - revert H1 H15 H12 H13 H10.
      simpl.
      unfold cmp_sem_nrm, deref_sem_nrm, cmp_compute_nrm.
      sets_unfold.
      intros.
      destruct H1 as [x1 [x2 [? [? ?]]]].
      left.
      exists x1, x2.
      destruct H1.
      destruct H1. 
      destruct H16.
      destruct H16.
      destruct H13.
      destruct H13.
      destruct H10.
      destruct H10.
      pose proof greater_vcnt1 as G1.
      pose proof greater_vcnt2 as G2.
      pose proof G2 vcnt ss13 ss3 e1 e2 H5 as G2.
      pose proof G1 vcnt ss12 ss13 e1 e2 H4 as G1.
      rewrite H10 in H16.
      rewrite <- H16 in H19.
      rewrite H19 in H21.
      pose proof some_val x2 x.
      destruct H22.
      pose proof H22 H21.
      rewrite <- H24 in H12.
      rewrite H13 in G1.
      rewrite G2 in G1.
      rewrite H1 in G1.
      rewrite H20 in G1.
      rewrite H18 in G1.
      pose proof some_val x0 x1.
      destruct H25.
      pose proof H25 G1.
      rewrite H27 in H15.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto. 
  + simpl in H0.
    assert (
      (Seval_comlist
      (ex2pre e1 (S (S vcnt)) ++
        [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
          ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) ++
          [SCAsgnVar (nat2Sname (S vcnt))
              (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1
      ss3).
    { simpl. tauto. }
    clear H0.
    pose proof midstate_binop vcnt e1 e2 ss1 ss3 H2.
    destruct H0 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
    pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H H0.
    pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H6 H3.
    pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H7 H4.
    pose proof Hc1 (S vcnt) (ex2se e2
      (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss3 H8 H5.
    pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
    sets_unfold in Hp.
    pose proof Hp (ex2se e1 (S (S vcnt))) vcnt ss11 ss12 H3 as Hp1.
    pose proof Hp (ex2se e2
      (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) (S vcnt) ss13 ss3 H5 as Hp2.
    assert (exists (x : int64), (Seval_r (genSECV (S vcnt))).(nrm) ss3 x) as Hd4.
    {
      simpl in H1.
      revert H1.
      simpl.
      unfold deref_sem_nrm, cmp_sem_nrm.
      intros.
      destruct H1 as [x0 [x1 ?]].
      destruct H1.
      destruct H10.
      destruct H10.
      exists x1, x.
      tauto.
    }
    destruct Hd4.
    pose proof Hp2 x H10.
    pose proof IHe2  (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 x H7 H4 H11.
    assert (exists (x : int64), (Seval_r (genSECV vcnt)).(nrm) ss12 x) as Hd5.
    {
      simpl in H1.
      revert H1.
      simpl.
      unfold deref_sem_nrm, cmp_sem_nrm.
      intros.
      destruct H1 as [x0 [x1 ?]].
      destruct H1.
      destruct H1.
      pose proof greater_vcnt1 as G1.
      pose proof greater_vcnt2 as G2.
      pose proof G2 vcnt ss13 ss3 e1 e2 H5.
      pose proof G1 vcnt ss12 ss13 e1 e2 H4.
      rewrite <- H15 in H14.
      destruct H1.
      rewrite <- H1 in H16.
      rewrite <- H14 in H16.
      exists x0, (ss12.(env) (nat2Sname vcnt)).
      tauto.
    }
    destruct Hd5.
    pose proof Hp1 x0 H13. 
    pose proof IHe1 (S (S vcnt)) s1 ss1 ss11 x0 H H0 H14.
    destruct H12, H15.
    - revert H1 H15 H12 H13 H10.
      simpl.
      unfold cmp_sem_nrm, deref_sem_nrm, cmp_compute_nrm.
      sets_unfold.
      intros.
      destruct H1 as [x1 [x2 [? [? ?]]]].
      left.
      exists x1, x2.
      destruct H1.
      destruct H1. 
      destruct H16.
      destruct H16.
      destruct H13.
      destruct H13.
      destruct H10.
      destruct H10.
      pose proof greater_vcnt1 as G1.
      pose proof greater_vcnt2 as G2.
      pose proof G2 vcnt ss13 ss3 e1 e2 H5 as G2.
      pose proof G1 vcnt ss12 ss13 e1 e2 H4 as G1.
      rewrite H10 in H16.
      rewrite <- H16 in H19.
      rewrite H19 in H21.
      pose proof some_val x2 x.
      destruct H22.
      pose proof H22 H21.
      rewrite <- H24 in H12.
      rewrite H13 in G1.
      rewrite G2 in G1.
      rewrite H1 in G1.
      rewrite H20 in G1.
      rewrite H18 in G1.
      pose proof some_val x0 x1.
      destruct H25.
      pose proof H25 G1.
      rewrite H27 in H15.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto.
  + simpl in H0.
    assert (
      (Seval_comlist
      (ex2pre e1 (S (S vcnt)) ++
        [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
          ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) ++
          [SCAsgnVar (nat2Sname (S vcnt))
              (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1
      ss3).
    { simpl. tauto. }
    clear H0.
    pose proof midstate_binop vcnt e1 e2 ss1 ss3 H2.
    destruct H0 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
    pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H H0.
    pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H6 H3.
    pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H7 H4.
    pose proof Hc1 (S vcnt) (ex2se e2
      (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss3 H8 H5.
    pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
    sets_unfold in Hp.
    pose proof Hp (ex2se e1 (S (S vcnt))) vcnt ss11 ss12 H3 as Hp1.
    pose proof Hp (ex2se e2
      (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) (S vcnt) ss13 ss3 H5 as Hp2.
    assert (exists (x : int64), (Seval_r (genSECV (S vcnt))).(nrm) ss3 x) as Hd4.
    {
      simpl in H1.
      revert H1.
      simpl.
      unfold deref_sem_nrm, cmp_sem_nrm.
      intros.
      destruct H1 as [x0 [x1 ?]].
      destruct H1.
      destruct H10.
      destruct H10.
      exists x1, x.
      tauto.
    }
    destruct Hd4.
    pose proof Hp2 x H10.
    pose proof IHe2  (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 x H7 H4 H11.
    assert (exists (x : int64), (Seval_r (genSECV vcnt)).(nrm) ss12 x) as Hd5.
    {
      simpl in H1.
      revert H1.
      simpl.
      unfold deref_sem_nrm, cmp_sem_nrm.
      intros.
      destruct H1 as [x0 [x1 ?]].
      destruct H1.
      destruct H1.
      pose proof greater_vcnt1 as G1.
      pose proof greater_vcnt2 as G2.
      pose proof G2 vcnt ss13 ss3 e1 e2 H5.
      pose proof G1 vcnt ss12 ss13 e1 e2 H4.
      rewrite <- H15 in H14.
      destruct H1.
      rewrite <- H1 in H16.
      rewrite <- H14 in H16.
      exists x0, (ss12.(env) (nat2Sname vcnt)).
      tauto.
    }
    destruct Hd5.
    pose proof Hp1 x0 H13. 
    pose proof IHe1 (S (S vcnt)) s1 ss1 ss11 x0 H H0 H14.
    destruct H12, H15.
    - revert H1 H15 H12 H13 H10.
      simpl.
      unfold cmp_sem_nrm, deref_sem_nrm, cmp_compute_nrm.
      sets_unfold.
      intros.
      destruct H1 as [x1 [x2 [? [? ?]]]].
      left.
      exists x1, x2.
      destruct H1.
      destruct H1. 
      destruct H16.
      destruct H16.
      destruct H13.
      destruct H13.
      destruct H10.
      destruct H10.
      pose proof greater_vcnt1 as G1.
      pose proof greater_vcnt2 as G2.
      pose proof G2 vcnt ss13 ss3 e1 e2 H5 as G2.
      pose proof G1 vcnt ss12 ss13 e1 e2 H4 as G1.
      rewrite H10 in H16.
      rewrite <- H16 in H19.
      rewrite H19 in H21.
      pose proof some_val x2 x.
      destruct H22.
      pose proof H22 H21.
      rewrite <- H24 in H12.
      rewrite H13 in G1.
      rewrite G2 in G1.
      rewrite H1 in G1.
      rewrite H20 in G1.
      rewrite H18 in G1.
      pose proof some_val x0 x1.
      destruct H25.
      pose proof H25 G1.
      rewrite H27 in H15.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto.
  + simpl in H0.
    assert (
      (Seval_comlist
      (ex2pre e1 (S (S vcnt)) ++
        [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
          ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) ++
          [SCAsgnVar (nat2Sname (S vcnt))
              (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1
      ss3).
    { simpl. tauto. }
    clear H0.
    pose proof midstate_binop vcnt e1 e2 ss1 ss3 H2.
    destruct H0 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
    pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H H0.
    pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H6 H3.
    pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H7 H4.
    pose proof Hc1 (S vcnt) (ex2se e2
      (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss3 H8 H5.
    pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
    sets_unfold in Hp.
    pose proof Hp (ex2se e1 (S (S vcnt))) vcnt ss11 ss12 H3 as Hp1.
    pose proof Hp (ex2se e2
      (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) (S vcnt) ss13 ss3 H5 as Hp2.
    assert (exists (x : int64), (Seval_r (genSECV (S vcnt))).(nrm) ss3 x) as Hd4.
    {
      simpl in H1.
      revert H1.
      simpl.
      unfold deref_sem_nrm, cmp_sem_nrm.
      intros.
      destruct H1 as [x0 [x1 ?]].
      destruct H1.
      destruct H10.
      destruct H10.
      exists x1, x.
      tauto.
    }
    destruct Hd4.
    pose proof Hp2 x H10.
    pose proof IHe2  (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 x H7 H4 H11.
    assert (exists (x : int64), (Seval_r (genSECV vcnt)).(nrm) ss12 x) as Hd5.
    {
      simpl in H1.
      revert H1.
      simpl.
      unfold deref_sem_nrm, cmp_sem_nrm.
      intros.
      destruct H1 as [x0 [x1 ?]].
      destruct H1.
      destruct H1.
      pose proof greater_vcnt1 as G1.
      pose proof greater_vcnt2 as G2.
      pose proof G2 vcnt ss13 ss3 e1 e2 H5.
      pose proof G1 vcnt ss12 ss13 e1 e2 H4.
      rewrite <- H15 in H14.
      destruct H1.
      rewrite <- H1 in H16.
      rewrite <- H14 in H16.
      exists x0, (ss12.(env) (nat2Sname vcnt)).
      tauto.
    }
    destruct Hd5.
    pose proof Hp1 x0 H13. 
    pose proof IHe1 (S (S vcnt)) s1 ss1 ss11 x0 H H0 H14.
    destruct H12, H15.
    - revert H1 H15 H12 H13 H10.
      simpl.
      unfold cmp_sem_nrm, deref_sem_nrm, cmp_compute_nrm.
      sets_unfold.
      intros.
      destruct H1 as [x1 [x2 [? [? ?]]]].
      left.
      exists x1, x2.
      destruct H1.
      destruct H1. 
      destruct H16.
      destruct H16.
      destruct H13.
      destruct H13.
      destruct H10.
      destruct H10.
      pose proof greater_vcnt1 as G1.
      pose proof greater_vcnt2 as G2.
      pose proof G2 vcnt ss13 ss3 e1 e2 H5 as G2.
      pose proof G1 vcnt ss12 ss13 e1 e2 H4 as G1.
      rewrite H10 in H16.
      rewrite <- H16 in H19.
      rewrite H19 in H21.
      pose proof some_val x2 x.
      destruct H22.
      pose proof H22 H21.
      rewrite <- H24 in H12.
      rewrite H13 in G1.
      rewrite G2 in G1.
      rewrite H1 in G1.
      rewrite H20 in G1.
      rewrite H18 in G1.
      pose proof some_val x0 x1.
      destruct H25.
      pose proof H25 G1.
      rewrite H27 in H15.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto.
  + simpl in H0.
    assert (
      (Seval_comlist
      (ex2pre e1 (S (S vcnt)) ++
        [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
          ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) ++
          [SCAsgnVar (nat2Sname (S vcnt))
              (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1
      ss3).
    { simpl. tauto. }
    clear H0.
    pose proof midstate_binop vcnt e1 e2 ss1 ss3 H2.
    destruct H0 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
    pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H H0.
    pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H6 H3.
    pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H7 H4.
    pose proof Hc1 (S vcnt) (ex2se e2
      (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss3 H8 H5.
    pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
    sets_unfold in Hp.
    pose proof Hp (ex2se e1 (S (S vcnt))) vcnt ss11 ss12 H3 as Hp1.
    pose proof Hp (ex2se e2
      (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) (S vcnt) ss13 ss3 H5 as Hp2.
    assert (exists (x : int64), (Seval_r (genSECV (S vcnt))).(nrm) ss3 x) as Hd4.
    {
      simpl in H1.
      revert H1.
      simpl.
      unfold deref_sem_nrm, cmp_sem_nrm.
      intros.
      destruct H1 as [x0 [x1 ?]].
      destruct H1.
      destruct H10.
      destruct H10.
      exists x1, x.
      tauto.
    }
    destruct Hd4.
    pose proof Hp2 x H10.
    pose proof IHe2  (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 x H7 H4 H11.
    assert (exists (x : int64), (Seval_r (genSECV vcnt)).(nrm) ss12 x) as Hd5.
    {
      simpl in H1.
      revert H1.
      simpl.
      unfold deref_sem_nrm, cmp_sem_nrm.
      intros.
      destruct H1 as [x0 [x1 ?]].
      destruct H1.
      destruct H1.
      pose proof greater_vcnt1 as G1.
      pose proof greater_vcnt2 as G2.
      pose proof G2 vcnt ss13 ss3 e1 e2 H5.
      pose proof G1 vcnt ss12 ss13 e1 e2 H4.
      rewrite <- H15 in H14.
      destruct H1.
      rewrite <- H1 in H16.
      rewrite <- H14 in H16.
      exists x0, (ss12.(env) (nat2Sname vcnt)).
      tauto.
    }
    destruct Hd5.
    pose proof Hp1 x0 H13. 
    pose proof IHe1 (S (S vcnt)) s1 ss1 ss11 x0 H H0 H14.
    destruct H12, H15.
    - revert H1 H15 H12 H13 H10.
      simpl.
      unfold cmp_sem_nrm, deref_sem_nrm, cmp_compute_nrm.
      sets_unfold.
      intros.
      destruct H1 as [x1 [x2 [? [? ?]]]].
      left.
      exists x1, x2.
      destruct H1.
      destruct H1. 
      destruct H16.
      destruct H16.
      destruct H13.
      destruct H13.
      destruct H10.
      destruct H10.
      pose proof greater_vcnt1 as G1.
      pose proof greater_vcnt2 as G2.
      pose proof G2 vcnt ss13 ss3 e1 e2 H5 as G2.
      pose proof G1 vcnt ss12 ss13 e1 e2 H4 as G1.
      rewrite H10 in H16.
      rewrite <- H16 in H19.
      rewrite H19 in H21.
      pose proof some_val x2 x.
      destruct H22.
      pose proof H22 H21.
      rewrite <- H24 in H12.
      rewrite H13 in G1.
      rewrite G2 in G1.
      rewrite H1 in G1.
      rewrite H20 in G1.
      rewrite H18 in G1.
      pose proof some_val x0 x1.
      destruct H25.
      pose proof H25 G1.
      rewrite H27 in H15.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto.
    - right.
      simpl.
      sets_unfold.
      tauto.
Qed.

Lemma Split_Serefine_nrm_l_binop {NameX : Names} {NPX : NamesProperty}:
    forall (e1 e2 : expr),
    (forall (vcnt : nat), Serefine_nrm_l (ex2pre e1 vcnt) (ex2se e1 vcnt) e1)
    -> 
    (forall (vcnt : nat), Serefine_nrm_r (ex2pre e1 vcnt) (ex2se e1 vcnt) e1)
    ->
    (forall (vcnt : nat), Serefine_nrm_l (ex2pre e2 vcnt) (ex2se e2 vcnt) e2)
    -> 
    (forall (vcnt : nat), Serefine_nrm_r (ex2pre e2 vcnt) (ex2se e2 vcnt) e2)
    ->
    forall (vcnt : nat) (op: binop), Serefine_nrm_l (ex2pre (EBinop op e1 e2) vcnt) (ex2se (EBinop op e1 e2) vcnt) (EBinop op e1 e2).
Proof.
  unfold Serefine_nrm_l, Serefine_nrm_r.
  simpl.
  sets_unfold.
  destruct op, e1, e2; tauto.
Qed.


Lemma Split_Serefine_nrm {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr) (vcnt : nat), 
    Serefine_nrm (ex2pre e vcnt) (ex2se e vcnt) e.
Proof.
    induction e.
    + unfold Serefine_nrm, Serefine_nrm_l, Serefine_nrm_r.
        tauto.
    + pose proof  Split_Serefine_nrm_EVar x.
        tauto.
    + revert IHe1 IHe2.
      unfold Serefine_nrm.
      intros.
      assert ((forall vcnt : nat, Serefine_nrm_l (ex2pre e1 vcnt) (ex2se e1 vcnt) e1) /\ (forall vcnt : nat, Serefine_nrm_r (ex2pre e1 vcnt) (ex2se e1 vcnt) e1)).
        { split; intros; pose proof IHe1 vcnt0; tauto. }
      assert ((forall vcnt : nat, Serefine_nrm_l (ex2pre e2 vcnt) (ex2se e2 vcnt) e2) /\ (forall vcnt : nat, Serefine_nrm_r (ex2pre e2 vcnt) (ex2se e2 vcnt) e2)).
        { split; intros; pose proof IHe2 vcnt0; tauto. }
        destruct H as [H1 H2].
        destruct H0 as [H3 H4].
        pose proof Split_Serefine_nrm_l_binop e1 e2 H1 H2 H3 H4 vcnt op.
        pose proof Split_Serefine_nrm_r_binop e1 e2 H1 H2 H3 H4 vcnt op.
        tauto.
    + revert IHe.
        unfold Serefine_nrm.
        intros.
        assert ((forall vcnt : nat, Serefine_nrm_l (ex2pre e vcnt) (ex2se e vcnt) e) /\ (forall vcnt : nat, Serefine_nrm_r (ex2pre e vcnt) (ex2se e vcnt) e)).
        { split; intros; pose proof IHe vcnt0; tauto. }
        destruct H.
        pose proof Split_Serefine_nrm_l_unop e H H0 vcnt op.
        pose proof Split_Serefine_nrm_r_unop e H H0 vcnt op.
        tauto.
    + revert IHe.
        unfold Serefine_nrm.
        intros.
        assert ((forall vcnt : nat, Serefine_nrm_l (ex2pre e vcnt) (ex2se e vcnt) e) /\ (forall vcnt : nat, Serefine_nrm_r (ex2pre e vcnt) (ex2se e vcnt) e)).
        { split; intros; pose proof IHe vcnt0; tauto. }
        destruct H.
        pose proof Split_Serefine_nrm_l_deref e H H0 vcnt.
        pose proof Split_Serefine_nrm_r_deref e H H0 vcnt.
        tauto.
    + revert IHe.
        unfold Serefine_nrm.
        intros.
        assert ((forall vcnt : nat, Serefine_nrm_l (ex2pre e vcnt) (ex2se e vcnt) e) /\ (forall vcnt : nat, Serefine_nrm_r (ex2pre e vcnt) (ex2se e vcnt) e)).
        { split; intros; pose proof IHe vcnt0; tauto. }
        destruct H.
        pose proof Split_Serefine_nrm_l_addrof e H H0 vcnt.
        pose proof Split_Serefine_nrm_r_addrof e H H0 vcnt.
        tauto.
Qed.

Lemma Split_Serefine_err1_deref {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr),
    (forall (vcnt : nat), Serefine_err (ex2pre e vcnt) (ex2se e vcnt) e)
    ->
    forall (vcnt : nat), Serefine_err1 (ex2pre (EDeref e) vcnt) (ex2se (EDeref e) vcnt) (EDeref e).
Proof.
    unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
    simpl.
    sets_unfold.
    intros.
    pose proof H (S vcnt) as H.
    destruct H as [IH1 [IH2 IH3]].
    pose proof midstate_deref_nrm e vcnt as Hm.
    pose proof eval_comlist_seq_err (ex2pre e (S vcnt)) 
        [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))] ss1 as Hs.
    pose proof deref_err_r e s1 as Herr.
    destruct Hs as [Hs1 Hs2].
    pose proof asgn_vcnt_ex2se_err_prop (ex2se e (S vcnt)) as He.
    pose proof correspond_prop1 as Hc1.
    pose proof correspond_prop2 as Hc2.
    pose proof Hc1 vcnt (ex2se e (S vcnt)) as Hc1.
    pose proof Hc2 e as Hc2.
    pose proof Hs1 H1 as H.
    destruct H.
    - pose proof IH1 s1 ss1 H0 H.
      tauto.
    - sets_unfold in H.
      destruct H as [ss2].
      destruct H.
      pose proof Hc2 (S vcnt) s1 ss1 ss2 H0 H.
      pose proof He vcnt s1 ss2 H3 H2.
      pose proof IH3 s1 ss1 ss2 H0 H H4.
      pose proof Herr H5.
      split; [|tauto].
      revert H5.
      simpl; tauto.
Qed.


Lemma Split_Serefine_err2_l_deref {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr),
    (forall (vcnt : nat), Serefine_err (ex2pre e vcnt) (ex2se e vcnt) e)
    ->
    forall (vcnt : nat), Serefine_err2_l (ex2pre (EDeref e) vcnt) (ex2se (EDeref e) vcnt) (EDeref e).
Proof.
    unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
    intros ? ? ? ? ss1 ss3 ? ? ?.
    pose proof H (S vcnt) as H.
    destruct H as [IH1 [IH2 IH3]].
    pose proof midstate_deref_nrm e vcnt as Hm.
    pose proof eval_comlist_seq_nrm (ex2pre e (S vcnt)) 
        [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))] ss1 ss3 as Hs.
    pose proof deref_err_r e s1 as Herr.
    destruct Hs as [Hs1 Hs2].
    pose proof asgn_vcnt_ex2se_nrm_prop (ex2se e (S vcnt)) as He.
    pose proof correspond_prop1 as Hc1.
    pose proof correspond_prop2 as Hc2.
    pose proof Hc1 vcnt (ex2se e (S vcnt)) as Hc1.
    pose proof Hc2 e as Hc2.
    pose proof Hs1 H1 as H.
    sets_unfold in H.
    destruct H as [ss2].
    destruct H.
    revert H2.
    simpl.
    sets_unfold.
    intros.
    destruct H2; [tauto|].
    unfold deref_sem_err in H2.
    destruct H2.
    unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
    asgn_deref_sem, asgn_deref_sem_nrm in H3.
    sets_unfold in H3.
    destruct H3.
    destruct H3.
    rewrite H4 in H3.
    destruct H3.
    destruct H3.
    destruct H3.
    unfold var_sem_l, EDenote.nrm in H3.
    destruct H5.
    destruct H6.
    destruct H7.
    destruct H8.
    destruct H2.
    pose proof H8 (nat2Sname vcnt).
    rewrite H11 in H3.
    rewrite H2 in H3.
    rewrite <- H3 in H7.
    rewrite H7 in H10.
    destruct H10; discriminate.
Qed.

Lemma Split_Serefine_err2_r_deref {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr),
    (forall (vcnt : nat), Serefine_err (ex2pre e vcnt) (ex2se e vcnt) e)
    ->
    forall (vcnt : nat), Serefine_err2_r (ex2pre (EDeref e) vcnt) (ex2se (EDeref e) vcnt) (EDeref e).
Proof.
    unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
    intros ? ? ? ? ss1 ss3 ? ? ?.
    pose proof H (S vcnt) as H.
    destruct H as [IH1 [IH2 IH3]].
    pose proof asgn_vcnt_ex2se_nrm_prop (ex2se e (S vcnt)) vcnt as Hp.
    sets_unfold in Hp.
    pose proof deref4 e vcnt ss3 as Hd4.
    pose proof midstate_deref_nrm e vcnt as Hm.
    pose proof eval_comlist_seq_nrm (ex2pre e (S vcnt)) 
        [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))] ss1 ss3 as Hs.
    pose proof deref_err_r e s1 as Herr.
    destruct Hs as [Hs1 Hs2].
    pose proof correspond_prop1 as Hc1.
    pose proof correspond_prop2 as Hc2.
    pose proof Hc1 vcnt (ex2se e (S vcnt)) as Hc1.
    pose proof Hc2 e as Hc2.
    pose proof Split_Serefine_nrm e (S vcnt) as Hsen.
    unfold Serefine_nrm, Serefine_nrm_r in Hsen.
    destruct Hsen as [H100 Hsen].
    simpl in H1.
      pose proof Hs1 H1 as H.
      sets_unfold in H.
      destruct H as [ss2].
      destruct H.
      revert H2.
      simpl.
      sets_unfold.
      intros.
      destruct H2.
      - destruct H2; [tauto|].
        unfold deref_sem_err in H2.
        destruct H2.
        unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
        asgn_deref_sem, asgn_deref_sem_nrm in H3.
        sets_unfold in H3.
        destruct H3.
        destruct H3.
        rewrite H4 in H3.
        destruct H3.
        destruct H3.
        destruct H3.
        unfold var_sem_l, EDenote.nrm in H3.
        destruct H5.
        destruct H6.
        destruct H7.
        destruct H8.
        destruct H2.
        pose proof H8 (nat2Sname vcnt).
        rewrite H11 in H3.
        rewrite H2 in H3.
        rewrite <- H3 in H7.
        rewrite H7 in H10.
        destruct H10; discriminate.
      - unfold deref_sem_nrm, deref_sem_err in H2.
        destruct H2.
        destruct H2.
        destruct H2.
        destruct H2.
        pose proof Hp ss2 ss3 H3.
        assert ((Seval_r (genSECV vcnt)).(nrm) ss3 x).
        {
            simpl.
            unfold deref_sem_nrm.
            exists x0.
            tauto.
        }
        pose proof H6 x H7.
        pose proof Hsen s1 ss1 ss2 x H0 H H8.
        destruct H9.
        right.
        revert H9.
        simpl.
        intros.
        unfold deref_sem_err.
        exists x.
        pose proof Hc2 (S vcnt) s1 ss1 ss2 H0 H.
        pose proof Hc1 s1 ss2 ss3 H10 H3.
        pose proof correspond_prop0 s1 ss3 x H11 H4.
        tauto.
        left.
        revert H9.
        simpl.
        tauto.
Qed.


Lemma unop_err_r: forall (e : expr) (s : state) (op: unop),
    (eval_r e).(err) s
    -> (eval_r (EUnop op e)).(err) s.
Proof.
    destruct op.
    + unfold eval_r.
      intros.
      unfold deref_sem_r, EDenote.err.
      sets_unfold.
      tauto.
    + unfold eval_r.
      intros.
      unfold deref_sem_r, EDenote.err, unop_sem, neg_sem.
      sets_unfold.
      tauto.
Qed.


Lemma Split_Serefine_err1_unop {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr),
    (forall (vcnt : nat), Serefine_err (ex2pre e vcnt) (ex2se e vcnt) e)
    ->
    forall (vcnt : nat) (op: unop), Serefine_err1 (ex2pre (EUnop op e) vcnt) (ex2se (EUnop op e) vcnt) (EUnop op e).
Proof.
    unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
    intros.
    pose proof H (S vcnt) as H.
    destruct H as [IH1 [IH2 IH3]].
    pose proof midstate_unop op e vcnt as Hm.
    pose proof eval_comlist_seq_err (ex2pre e (S vcnt)) 
    [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))] ss1 as Hs.
    pose proof unop_err_r e s1 op as Herr.
    destruct Hs as [Hs1 Hs2].
    pose proof asgn_vcnt_ex2se_err_prop (ex2se e (S vcnt)) as He.
    pose proof correspond_prop1 as Hc1.
    pose proof correspond_prop2 as Hc2.
    pose proof Hc1 vcnt (ex2se e (S vcnt)) as Hc1.
    pose proof Hc2 e as Hc2.
    simpl in H1.
    pose proof Hs1 H1 as H.
    destruct H.
      - pose proof IH1 s1 ss1 H0 H.
        revert H2.
        unfold eval_l, eval_r; simpl; sets_unfold.
        tauto.
      - sets_unfold in H.
          destruct H as [ss2].
          destruct H.
          pose proof Hc2 (S vcnt) s1 ss1 ss2 H0 H.
          pose proof He vcnt s1 ss2 H3 H2.
          pose proof IH3 s1 ss1 ss2 H0 H H4.
          pose proof Herr H5.
          split; [|tauto].
          revert H5.
          simpl. 
          sets_unfold. 
          tauto.
Qed.


Lemma Split_Serefine_err2_l_unop {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr),
    (forall (vcnt : nat), Serefine_err (ex2pre e vcnt) (ex2se e vcnt) e)
    ->
    forall (vcnt : nat)(op : unop), Serefine_err2_l (ex2pre (EUnop op e) vcnt) (ex2se (EUnop op e) vcnt) (EUnop op e).
Proof.
    unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
    destruct e; tauto.
Qed.

Lemma Split_Serefine_err2_r_unop {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr),
    (forall (vcnt : nat), Serefine_err (ex2pre e vcnt) (ex2se e vcnt) e)
    ->
    forall (vcnt : nat)(op : unop), Serefine_err2_r (ex2pre (EUnop op e) vcnt) (ex2se (EUnop op e) vcnt) (EUnop op e).
Proof.
    unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
    intros ? ? ? ? ? ss1 ss3 ? ? ?.
    pose proof H (S vcnt) as H.
    destruct H as [IH1 [IH2 IH3]].
    pose proof asgn_vcnt_ex2se_nrm_prop (ex2se e (S vcnt)) vcnt as Hp.
    sets_unfold in Hp.
    pose proof unop4 e vcnt ss3 op as Hd4.
    pose proof midstate_unop op e vcnt ss1 ss3 H1 as Hm.
    pose proof eval_comlist_seq_nrm (ex2pre e (S vcnt)) 
        [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))] ss1 ss3 as Hs.
    pose proof unop_err_r e s1 op as Herr.
    destruct Hs as [Hs1 Hs2].
    pose proof correspond_prop1 as Hc1.
    pose proof correspond_prop2 as Hc2.
    pose proof Hc1 vcnt (ex2se e (S vcnt)) as Hc1.
    pose proof Hc2 e as Hc2.
    pose proof Split_Serefine_nrm e (S vcnt) as Hsen.
    unfold Serefine_nrm, Serefine_nrm_r in Hsen.
    destruct Hsen as [H100 Hsen].
    simpl in H1.
      pose proof Hs1 H1 as H.
      sets_unfold in H.
      destruct H as [ss2].
      destruct H.
      revert H2.
      simpl.
      destruct op.
      - unfold unop_sem,not_sem.
        simpl.
        sets_unfold.
        intros.
        destruct H2; [tauto|].
        unfold deref_sem_err in H2.
        destruct H2.
        unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
          asgn_deref_sem, asgn_deref_sem_nrm in H3.
        sets_unfold in H3.
        destruct H3.
        destruct H3.
        rewrite H4 in H3.
        destruct H3.
        destruct H3.
        destruct H3.
        unfold var_sem_l, EDenote.nrm in H3.
        destruct H5.
        destruct H6.
        destruct H7.
        destruct H8.
        destruct H2.
        pose proof H8 (nat2Sname vcnt).
        rewrite H11 in H3.
        rewrite H2 in H3.
        rewrite <- H3 in H7.
        rewrite H7 in H10.
        destruct H10; discriminate.
      - unfold unop_sem, neg_sem, neg_sem_err.
        simpl. 
        unfold deref_sem_err, deref_sem_nrm.
        sets_unfold.
        intros.
        pose proof Hc2 (S vcnt) s1 ss1 ss2 H0 H as Hc2.
        pose proof Hc1 s1 ss2 ss3 Hc2 H3 as Hc1.
        unfold correspond in Hc1.
        destruct Hc1 as [Hc1e Hc1m].
        destruct Hc1m as [Hc1m1 Hc1m2].
        destruct H2.
        destruct H2; [tauto|].
        * destruct H2 as [x [H21 H22]].
          unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
          asgn_deref_sem, asgn_deref_sem_nrm in H3.
          sets_unfold in H3.
          destruct H3.
          destruct H2.
          rewrite H3 in H2.
          destruct H2.
          destruct H2.
          destruct H2.
          unfold var_sem_l,EDenote.nrm in H2.
          destruct H4.
          destruct H5.
          destruct H6.
          destruct H7.
          pose proof H7 (nat2Sname vcnt).
          rewrite H9 in H2.
          rewrite H21 in H2.
          rewrite <- H2 in H6.
          rewrite H6 in H22.
          destruct H22; discriminate.
        * destruct H2.
          destruct H2.
          destruct H2.
          pose proof Hp ss2 ss3 H3 x.
          assert ((Seval_r (genSECV vcnt)).(nrm) ss3 x).
          {
            simpl.
            unfold deref_sem_nrm.
            exists x0.
            tauto.
          }
          pose proof H5 H6.
          pose proof Hsen s1 ss1 ss2 x H0 H H7.
          destruct H8.
          -- right.
             exists x.
             tauto.
          -- left.
             revert H8.
             simpl.
             tauto.
Qed. 


Lemma Split_Serefine_err1_addrof {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr),
    (forall (vcnt : nat), Serefine_err (ex2pre e vcnt) (ex2se e vcnt) e)
    ->
    forall (vcnt : nat), Serefine_err1 (ex2pre (EAddrOf e) vcnt) (ex2se (EAddrOf e) vcnt) (EAddrOf e).
Proof.
    unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
    intros.
    pose proof H as H100.
    pose proof H (S vcnt) as H.
    destruct H as [IH1 [IH2 IH3]].
    pose proof ex2pre_addrof e vcnt as Hd.
    pose proof eval_comlist_seq_err (ex2pre e (S vcnt)) 
        [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))] ss1 as Hs.
    destruct Hs as [Hs1 Hs2].
    pose proof asgn_vcnt_ex2se_err_prop (ex2se e (S vcnt)) as He.
    pose proof correspond_prop1 as Hc1.
    pose proof correspond_prop2 as Hc2.
    pose proof Hc1 vcnt (ex2se e (S vcnt)) as Hc1.
    pose proof Hc2 e as Hc2.
    destruct e.
    + rewrite Hd in H1.
    revert H1.
    simpl.
    sets_unfold.
    tauto.
    + rewrite Hd in H1.
    revert H1.
    simpl.
    sets_unfold.
    tauto.
    + simpl in H1.
      sets_unfold in H1.
      tauto.
    + simpl in H1.
      sets_unfold in H1.
      tauto.
    + simpl.
      sets_unfold.
      split; [tauto|].
      simpl in H1.
      pose proof H100 vcnt as [? [? ?]].
      pose proof H s1 ss1 H0.
      revert H4 H1.
      simpl.
      tauto.
    + simpl in H1.
      sets_unfold in H1.
      tauto.
Qed.


Lemma Split_Serefine_err2_l_addrof {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr),
    (forall (vcnt : nat), Serefine_err (ex2pre e vcnt) (ex2se e vcnt) e)
    ->
    forall (vcnt : nat), Serefine_err2_l (ex2pre (EAddrOf e) vcnt) (ex2se (EAddrOf e) vcnt) (EAddrOf e).
Proof.
    unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
    intros ? ? ? ? ss1 ss3 ? ? ?.
    pose proof H (S vcnt) as H.
    destruct H as [IH1 [IH2 IH3]].
    (* pose proof ex2pre_addrof e vcnt as Hd. *)
    pose proof eval_comlist_seq_nrm (ex2pre e (S vcnt)) 
        [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))] ss1 ss3 as Hs.
    destruct Hs as [Hs1 Hs2].
    destruct e.
    + revert H2.
      simpl.
      tauto.
    + revert H1 H2.
      simpl.
      sets_unfold.
      tauto.
    + simpl in H1.
      sets_unfold in H1.
      rewrite <- H1 in H2.
      revert H2.
      simpl.
      sets_unfold.
      tauto.
    + simpl in H1.
      sets_unfold in H1.
      rewrite <- H1 in H2.
      revert H2.
      simpl.
      sets_unfold.
      tauto.
    + simpl. 
      sets_unfold. 
      tauto.
    + simpl in H1.
      sets_unfold in H1.
      rewrite <- H1 in H2.
      revert H2.
      simpl.
      sets_unfold.
      tauto.
Qed.

Lemma Split_Serefine_err2_r_addrof {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr),
    (forall (vcnt : nat), Serefine_err (ex2pre e vcnt) (ex2se e vcnt) e)
    ->
    forall (vcnt : nat), Serefine_err2_r (ex2pre (EAddrOf e) vcnt) (ex2se (EAddrOf e) vcnt) (EAddrOf e).
Proof.
    unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
    intros ? ? ? ? ss1 ss3 ? ? ?.
    pose proof H vcnt as H.
    destruct H as [IH1 [IH2 IH3]].
    induction e.
    + simpl. sets_unfold. tauto.
    + simpl. sets_unfold. tauto.
    + simpl. sets_unfold. tauto.
    + simpl. sets_unfold. tauto.
    + simpl. 
      pose proof IH2 s1 ss1 ss3 H0.
      revert H H1 H2.
      simpl.
      tauto.
    + simpl. sets_unfold. tauto.
Qed.

Lemma Split_Serefine_err1_binop {NameX : Names} {NPX : NamesProperty}:
    forall (op : binop) (e1 e2 : expr),
    (forall (vcnt : nat), Serefine_err (ex2pre e1 vcnt) (ex2se e1 vcnt) e1)
    -> (forall (vcnt : nat), Serefine_err (ex2pre e2 vcnt) (ex2se e2 vcnt) e2)
    -> (forall (vcnt : nat), Serefine_err1 (ex2pre (EBinop op e1 e2) vcnt) (ex2se (EBinop op e1 e2) vcnt) (EBinop op e1 e2)).
Proof.
  unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
  intros.
  (* pose proof midstate_binop vcnt e1 e2 as Hm. *)
  simpl.
  sets_unfold.
  split; [tauto|].
  pose proof ex2pre_binop vcnt e1 e2 op as Hp.
  pose proof Split_Serefine_nrm e1 (S (S vcnt)) as [Hl Hr].
  destruct op.
  +
  pose proof H (S (S vcnt)) as [H101 [H102 H103]].
  pose proof H0 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) as [H201 [H202 H203]].
  rewrite Hp in H2.
  simpl.
  sets_unfold.
  unfold or_sem_err, NonSC_or.
  pose proof eval_comlist_seq_err 
    (ex2pre e1 (S (S vcnt)))
         ([SCAsgnVar (nat2Sname (S vcnt)) (ex2se e1 (S (S vcnt)))] ++
         [SCIf (genSECV (S vcnt))
            [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1))]
            (ex2pre e2
               (nat_add (S (S vcnt))
                  (length (ex2pre e1 (S (S vcnt))))) ++
             [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2
                   (nat_add (S (S vcnt))
                      (length (ex2pre e1 (S (S vcnt))))))] ++
             [SCIf (genSECV (S vcnt))
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 1))]
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 0))]])]) ss1.
  destruct H3.
  pose proof H3 H2.
  destruct H5.
  ++
  pose proof H101 s1 ss1 H1 H5.
  tauto.
  ++
  sets_unfold in H5.
  destruct H5 as [ss11].
  destruct H5.
  pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H5.
  pose proof eval_comlist_seq_err
    ([SCAsgnVar (nat2Sname (S vcnt)) (ex2se e1 (S (S vcnt)))])
         ([SCIf (genSECV (S vcnt))
            [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1))]
            (ex2pre e2
               (nat_add (S (S vcnt))
                  (length (ex2pre e1 (S (S vcnt))))) ++
             [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2
                   (nat_add (S (S vcnt))
                      (length (ex2pre e1 (S (S vcnt))))))] ++
             [SCIf (genSECV (S vcnt))
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 1))]
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 0))]])]) ss11.
  destruct H8.
  pose proof H8 H6.
  destruct H10.
  +++
  pose proof asgn_vcnt_ex2se_err_prop (ex2se e1 (S (S vcnt))) (S vcnt) s1 ss11 H7 H10.
  pose proof H103 s1 ss1 ss11 H1 H5 H11.
  tauto.
  +++
  sets_unfold in H10.
  destruct H10 as [ss12].
  destruct H10.
  pose proof correspond_prop1 (S vcnt) (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H7 H10.
  simpl in H11.
  sets_unfold in H11.
  destruct H11.
  ++++
  destruct H11.
  -
  destruct H11.
  --
  destruct H11; [tauto|].
  unfold deref_sem_err in H11.
  destruct H11.
  destruct H11.
  simpl in H10.
  unfold asgn_deref_sem_nrm in H10.
  sets_unfold in H10.
  destruct H10.
  destruct H10.
  rewrite H14 in H10.
  destruct H10 as [i1[i2[?[?[?[?[?]]]]]]].
  pose proof H18 (nat2Sname (S vcnt)).
  rewrite H20 in H10.
  rewrite H10 in H11.
  rewrite <- H11 in H13.
  rewrite H17 in H13.
  destruct H13; discriminate.
  --
  destruct H11.
  destruct H11.
  unfold test_true in H11.
  sets_unfold in H11.
  destruct H11.
  rewrite <- H14 in H13.
  destruct H13.
  ---
  destruct H13.
  ----
  destruct H13; [tauto|].
  revert H13.
  unfold Int64.min_signed, Int64.max_signed, Int64.half_modulus, Int64.modulus; simpl; lia.
  ----
  destruct H13.
  destruct H13.
  unfold correspond in H12.
  destruct H12.
  destruct H16.
  pose proof H17 vcnt.
  rewrite H13 in H18.
  rewrite H15 in H18.
  tauto.
  ---
  destruct H13.
  tauto.
  -
  destruct H11.
  destruct H11.
  unfold test_false in H11.
  sets_unfold in H11.
  destruct H11.
  rewrite <- H14 in H13.
  assert ((Seval_r (genSECV (S vcnt))).(nrm) ss12 (Int64.repr 0)).
  {
    revert H11.
    simpl.
    tauto.
  }
  pose proof asgn_vcnt_ex2se_nrm_prop (ex2se e1 (S (S vcnt))) (S vcnt) ss11 ss12 H10 (Int64.repr 0) H15.
  pose proof Hr s1 ss1 ss11 (Int64.repr 0) H1 H5 H16.
  destruct H17; [|tauto].
  pose proof eval_comlist_seq_err 
    (ex2pre e2
            (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))
          ([SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2
                (S
                   (S
                      (nat_add vcnt
                         (length (ex2pre e1 (S (S vcnt)))))))),
          SCIf (genSECV (S vcnt))
            [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1))]
            [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0))]]) ss12.
  destruct H18.
  pose proof H18 H13.
  destruct H20.
  --
  pose proof H201 s1 ss12 H12 H20.
  right.
  exists (Int64.repr 0). 
  tauto.
  --
  sets_unfold in H20.
  destruct H20 as [ss13].
  destruct H20.
  pose proof eval_comlist_seq_err 
    [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2
               (S
                  (S
                     (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))]
        [SCIf (genSECV (S vcnt))
           [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1))]
           [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0))]] ss13.
  destruct H22.
  pose proof H22 H21.
  destruct H24.
  ---
  simpl in H24.
  sets_unfold in H24.
  destruct H24.
  ----
  destruct H24.
  *
  destruct H24; [tauto|].
  pose proof H203 s1 ss12 ss13 H12 H20 H24.
  right.
  exists (Int64.repr 0).
  tauto.
  *
  destruct H24.
  destruct H24.
  simpl in H20.
  pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H12 H20.
  destruct H26 as [?[?]].
  pose proof H28 (S vcnt).
  destruct H29.
  rewrite H24 in H30.
  rewrite H25 in H30.
  tauto.
  ----
  destruct H24.
  tauto.
  ---
  sets_unfold in H24.
  destruct H24 as [ss14].
  destruct H24.
  simpl in H25.
  sets_unfold in H25.
  destruct H25.
  ----
  destruct H25.
  *
  destruct H25.
  **
  destruct H25; [tauto|].
  destruct H25.
  destruct H25.
  simpl in H24.
  unfold asgn_deref_sem_nrm in H24.
  sets_unfold in H24.
  destruct H24.
  destruct H24.
  rewrite H27 in H24.
  destruct H24 as [i3[i4[?[?[?[?[?]]]]]]].
  pose proof H31 (nat2Sname (S vcnt)).
  rewrite H24 in H33.
  rewrite H25 in H33.
  rewrite <- H33 in H26.
  rewrite H30 in H26.
  destruct H26; discriminate.
  **
  destruct H25.
  destruct H25.
  unfold test_true in H25.
  sets_unfold in H25.
  destruct H25.
  rewrite <- H27 in H26.
  destruct H26.
  ***
  destruct H26.
  ****
  destruct H26; [tauto|].
  revert H26.
  unfold Int64.min_signed, Int64.max_signed, Int64.half_modulus, Int64.modulus; simpl; lia.
  ****
  destruct H26.
  destruct H26.
  pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H12 H20.
  pose proof correspond_prop1 (S vcnt) (ex2se e2
  (S
     (S
        (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss14 H29 H24.
  unfold correspond in H30.
  destruct H30.
  destruct H31.
  pose proof H32 vcnt.
  destruct H33.
  rewrite H26 in H34.
  rewrite H28 in H34.
  tauto.
  ***
  destruct H26.
  tauto.
  *
  destruct H25.
  destruct H25.
  unfold test_false in H25.
  sets_unfold in H25.
  destruct H25.
  rewrite <- H27 in H26.
  destruct H26.
  **
  destruct H26.
  ***
  destruct H26; [tauto|].
  revert H26.
  unfold Int64.min_signed, Int64.max_signed, Int64.half_modulus, Int64.modulus; simpl; lia.
  ***
  destruct H26.
  destruct H26.
  pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H12 H20.
  pose proof correspond_prop1 (S vcnt) (ex2se e2
  (S
     (S
        (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss14 H29 H24.
  unfold correspond in H30.
  destruct H30.
  destruct H31.
  pose proof H32 vcnt.
  destruct H33.
  rewrite H26 in H34.
  rewrite H28 in H34.
  tauto.
  **
  destruct H26.
  tauto.
  ----
  destruct H25.
  tauto.
  ++++
  destruct H11.
  tauto.
  +
  pose proof H (S (S vcnt)) as [H101 [H102 H103]].
  pose proof H0 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) as [H201 [H202 H203]].
  rewrite Hp in H2.
  simpl.
  sets_unfold.
  unfold and_sem_err, NonSC_and.
  pose proof eval_comlist_seq_err 
    (ex2pre e1 (S (S vcnt)))
         ([SCAsgnVar (nat2Sname (S vcnt)) (ex2se e1 (S (S vcnt)))] ++
         [SCIf (genSECV (S vcnt))
            (ex2pre e2
               (nat_add (S (S vcnt))
                  (length (ex2pre e1 (S (S vcnt))))) ++
             [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2
                   (nat_add (S (S vcnt))
                      (length (ex2pre e1 (S (S vcnt))))))] ++
             [SCIf (genSECV (S vcnt))
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 1))]
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 0))]])
            [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0))]]) ss1.
  destruct H3.
  pose proof H3 H2.
  destruct H5.
  ++
  pose proof H101 s1 ss1 H1 H5.
  tauto.
  ++
  sets_unfold in H5.
  destruct H5 as [ss11].
  destruct H5.
  pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H5.
  pose proof eval_comlist_seq_err
    ([SCAsgnVar (nat2Sname (S vcnt)) (ex2se e1 (S (S vcnt)))])
         ([SCIf (genSECV (S vcnt))
            (ex2pre e2
               (nat_add (S (S vcnt))
                  (length (ex2pre e1 (S (S vcnt))))) ++
             [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2
                   (nat_add (S (S vcnt))
                      (length (ex2pre e1 (S (S vcnt))))))] ++
             [SCIf (genSECV (S vcnt))
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 1))]
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 0))]])
              [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0))]]) ss11.
  destruct H8.
  pose proof H8 H6.
  destruct H10.
  +++
  pose proof asgn_vcnt_ex2se_err_prop (ex2se e1 (S (S vcnt))) (S vcnt) s1 ss11 H7 H10.
  pose proof H103 s1 ss1 ss11 H1 H5 H11.
  tauto.
  +++
  sets_unfold in H10.
  destruct H10 as [ss12].
  destruct H10.
  pose proof correspond_prop1 (S vcnt) (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H7 H10.
  simpl in H11.
  sets_unfold in H11.
  destruct H11.
  ++++
  destruct H11.
  -
  destruct H11.
  --
  destruct H11; [tauto|].
  unfold deref_sem_err in H11.
  destruct H11.
  destruct H11.
  simpl in H10.
  unfold asgn_deref_sem_nrm in H10.
  sets_unfold in H10.
  destruct H10.
  destruct H10.
  rewrite H14 in H10.
  destruct H10 as [i1[i2[?[?[?[?[?]]]]]]].
  pose proof H18 (nat2Sname (S vcnt)).
  rewrite H20 in H10.
  rewrite H10 in H11.
  rewrite <- H11 in H13.
  rewrite H17 in H13.
  destruct H13; discriminate.
  --
  destruct H11.
  destruct H11.
  unfold test_true in H11.
  sets_unfold in H11.
  destruct H11.
  destruct H11.
  assert ((Seval_r (genSECV (S vcnt))).(nrm) ss12 x0).
  {
    revert H11.
    simpl.
    tauto.
  }
  pose proof asgn_vcnt_ex2se_nrm_prop (ex2se e1 (S (S vcnt))) (S vcnt) ss11 ss12 H10 x0 H15.
  pose proof Hr s1 ss1 ss11 x0 H1 H5 H16.
  destruct H17; [|tauto].
  rewrite <- H14 in H13.
  pose proof eval_comlist_seq_err 
    (ex2pre e2
            (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))
          ([SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2
                (S
                   (S
                      (nat_add vcnt
                         (length (ex2pre e1 (S (S vcnt)))))))),
          SCIf (genSECV (S vcnt))
            [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1))]
            [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0))]]) ss12.
  destruct H18.
  pose proof H18 H13.
  destruct H20.
  ---
  pose proof H201 s1 ss12 H12 H20.
  right.
  exists x0. 
  tauto.
  ---
  sets_unfold in H20.
  destruct H20 as [ss13].
  destruct H20.
  pose proof eval_comlist_seq_err 
    [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2
               (S
                  (S
                     (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))]
        [SCIf (genSECV (S vcnt))
           [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1))]
           [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0))]] ss13.
  destruct H22.
  pose proof H22 H21.
  destruct H24.
  ----
  simpl in H24.
  sets_unfold in H24.
  destruct H24.
  *
  destruct H24.
  **
  destruct H24; [tauto|].
  pose proof H203 s1 ss12 ss13 H12 H20 H24.
  right.
  exists x0.
  tauto.
  **
  destruct H24.
  destruct H24.
  pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H12 H20.
  destruct H26 as [?[?]].
  pose proof H28 (S vcnt).
  destruct H29.
  rewrite H24 in H30.
  rewrite H25 in H30.
  tauto.
  *
  destruct H24.
  tauto.
  ----
  sets_unfold in H24.
  destruct H24 as [ss14].
  destruct H24.
  simpl in H25.
  sets_unfold in H25.
  destruct H25.
  *
  destruct H25.
  **
  destruct H25.
  ***
  destruct H25; [tauto|].
  destruct H25.
  destruct H25.
  simpl in H24.
  unfold asgn_deref_sem_nrm in H24.
  sets_unfold in H24.
  destruct H24.
  destruct H24.
  rewrite H27 in H24.
  destruct H24 as [i3[i4[?[?[?[?[?]]]]]]].
  pose proof H31 (nat2Sname (S vcnt)).
  rewrite H24 in H33.
  rewrite H25 in H33.
  rewrite <- H33 in H26.
  rewrite H30 in H26.
  destruct H26; discriminate.
  ***
  destruct H25.
  destruct H25.
  unfold test_true in H25.
  sets_unfold in H25.
  destruct H25.
  rewrite <- H27 in H26.
  destruct H26.
  ****
  destruct H26.
  *****
  destruct H26; [tauto|].
  revert H26.
  unfold Int64.min_signed, Int64.max_signed, Int64.half_modulus, Int64.modulus; simpl; lia.
  *****
  destruct H26.
  destruct H26.
  pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H12 H20.
  pose proof correspond_prop1 (S vcnt) (ex2se e2
  (S
     (S
        (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss14 H29 H24.
  unfold correspond in H30.
  destruct H30.
  destruct H31.
  pose proof H32 vcnt.
  destruct H33.
  rewrite H26 in H34.
  rewrite H28 in H34.
  tauto.
  ****
  destruct H26.
  tauto.
  **
  destruct H25.
  destruct H25.
  unfold test_false in H25.
  sets_unfold in H25.
  destruct H25.
  rewrite <- H27 in H26.
  destruct H26.
  ***
  destruct H26.
  ****
  destruct H26; [tauto|].
  revert H26.
  unfold Int64.min_signed, Int64.max_signed, Int64.half_modulus, Int64.modulus; simpl; lia.
  ****
  destruct H26.
  destruct H26.
  pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H12 H20.
  pose proof correspond_prop1 (S vcnt) (ex2se e2
  (S
     (S
        (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss14 H29 H24.
  unfold correspond in H30.
  destruct H30.
  destruct H31.
  pose proof H32 vcnt.
  destruct H33.
  rewrite H26 in H34.
  rewrite H28 in H34.
  tauto.
  ***
  destruct H26.
  tauto.
  *
  destruct H25.
  tauto.
  -
  destruct H11.
  destruct H11.
  unfold test_false in H11.
  sets_unfold in H11.
  destruct H11.
  rewrite <- H14 in H13.
  destruct H13.
  --
  destruct H13.
  ---
  destruct H13; [tauto|].
  revert H13.
  unfold Int64.min_signed, Int64.max_signed, Int64.half_modulus, Int64.modulus; simpl; lia.
  ---
  destruct H13.
  destruct H13.
  unfold correspond in H12.
  destruct H12.
  destruct H16.
  pose proof H17 vcnt.
  rewrite H13 in H18.
  rewrite H15 in H18.
  tauto.
  --
  destruct H13.
  tauto.
  ++++
  destruct H11.
  tauto.
  + pose proof H (S (S vcnt)) as H.
    destruct H as [IH1 [IH2 IH3]].
    rewrite Hp in H2.
    simpl.
    sets_unfold.
    unfold or_sem_err, NonSC_or. 
    pose proof eval_comlist_seq_err (ex2pre e1 (S (S vcnt))) 
    ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
         ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
         [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss1.
    destruct H.
    pose proof H H2.
    destruct H4.
    ++ pose proof IH1 s1 ss1 H1 H4.
       tauto.
    ++ sets_unfold in H4.
      destruct H4 as [ss11].
      destruct H4.
      pose proof eval_comlist_seq_err
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))]
      (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2
            (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss11.
      destruct H6.
      pose proof H6 H5.
      pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H4 as H10.
      destruct H8.
      +++
      simpl in H8.
      sets_unfold in H8.
      destruct H8.
      ++++
      destruct H8.
        -
        destruct H8; [tauto|].
        pose proof IH3 s1 ss1 ss11 H1 H4 H8.
        tauto.
        -
        unfold asgn_deref_sem_err in H8.
        destruct H8.
        destruct H8.
        unfold correspond in H10.
        destruct H10.
        destruct H11.
        pose proof H12 vcnt.
        destruct H13.
        rewrite <- H8 in H9.
        rewrite H9 in H14.
        tauto.
      ++++
      destruct H8.
      tauto.
    +++
    sets_unfold in H8.
    destruct H8 as [ss12].
    destruct H8.
    pose proof correspond_prop1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H10 H8.
    pose proof eval_comlist_seq_err (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) 
    ([SCAsgnVar (nat2Sname (S vcnt))
    (ex2se e2
       (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss12.
    destruct H12.
    pose proof H12 H9.
    destruct H14.
    ++++  pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H15 as [He21 [He22 He23]].
          pose proof He21 s1 ss12 H11 H14.
          tauto.
    ++++
      destruct H14 as [ss13].
      simpl in H14.
      sets_unfold in H14.
      destruct H14.
      pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H11 H14.
      destruct H15.
      - destruct H15.
        -- 
          destruct H15; [tauto|].
          pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H17 as [He21 [He22 He23]].
          pose proof He23 s1 ss12 ss13 H11 H14 H15.
          tauto.
        -- destruct H15.
          destruct H15.
          unfold correspond in H16.
          destruct H16.
          destruct H18.
          pose proof H19 (S vcnt).
          destruct H20.
          rewrite <- H15 in H17.
          rewrite H17 in H21.
          tauto.
      -   destruct H15.
          destruct H15.
          tauto.
  + pose proof H (S (S vcnt)) as H.
    destruct H as [IH1 [IH2 IH3]].
    rewrite Hp in H2.
    simpl.
    sets_unfold.
    unfold or_sem_err, NonSC_or. 
    pose proof eval_comlist_seq_err (ex2pre e1 (S (S vcnt))) 
    ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
         ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
         [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss1.
    destruct H.
    pose proof H H2.
    destruct H4.
    ++ pose proof IH1 s1 ss1 H1 H4.
       tauto.
    ++ sets_unfold in H4.
      destruct H4 as [ss11].
      destruct H4.
      pose proof eval_comlist_seq_err
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))]
      (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2
            (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss11.
      destruct H6.
      pose proof H6 H5.
      pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H4 as H10.
      destruct H8.
      +++
      simpl in H8.
      sets_unfold in H8.
      destruct H8.
      ++++
      destruct H8.
        -
        destruct H8; [tauto|].
        pose proof IH3 s1 ss1 ss11 H1 H4 H8.
        tauto.
        -
        unfold asgn_deref_sem_err in H8.
        destruct H8.
        destruct H8.
        unfold correspond in H10.
        destruct H10.
        destruct H11.
        pose proof H12 vcnt.
        destruct H13.
        rewrite <- H8 in H9.
        rewrite H9 in H14.
        tauto.
      ++++
      destruct H8.
      tauto.
    +++
    sets_unfold in H8.
    destruct H8 as [ss12].
    destruct H8.
    pose proof correspond_prop1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H10 H8.
    pose proof eval_comlist_seq_err (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) 
    ([SCAsgnVar (nat2Sname (S vcnt))
    (ex2se e2
       (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss12.
    destruct H12.
    pose proof H12 H9.
    destruct H14.
    ++++  pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H15 as [He21 [He22 He23]].
          pose proof He21 s1 ss12 H11 H14.
          tauto.
    ++++
      destruct H14 as [ss13].
      simpl in H14.
      sets_unfold in H14.
      destruct H14.
      pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H11 H14.
      destruct H15.
      - destruct H15.
        -- 
          destruct H15; [tauto|].
          pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H17 as [He21 [He22 He23]].
          pose proof He23 s1 ss12 ss13 H11 H14 H15.
          tauto.
        -- destruct H15.
          destruct H15.
          unfold correspond in H16.
          destruct H16.
          destruct H18.
          pose proof H19 (S vcnt).
          destruct H20.
          rewrite <- H15 in H17.
          rewrite H17 in H21.
          tauto.
      -   destruct H15.
          destruct H15.
          tauto.
  + pose proof H (S (S vcnt)) as H.
    destruct H as [IH1 [IH2 IH3]].
    rewrite Hp in H2.
    simpl.
    sets_unfold.
    unfold or_sem_err, NonSC_or. 
    pose proof eval_comlist_seq_err (ex2pre e1 (S (S vcnt))) 
    ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
         ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
         [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss1.
    destruct H.
    pose proof H H2.
    destruct H4.
    ++ pose proof IH1 s1 ss1 H1 H4.
       tauto.
    ++ sets_unfold in H4.
      destruct H4 as [ss11].
      destruct H4.
      pose proof eval_comlist_seq_err
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))]
      (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2
            (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss11.
      destruct H6.
      pose proof H6 H5.
      pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H4 as H10.
      destruct H8.
      +++
      simpl in H8.
      sets_unfold in H8.
      destruct H8.
      ++++
      destruct H8.
        -
        destruct H8; [tauto|].
        pose proof IH3 s1 ss1 ss11 H1 H4 H8.
        tauto.
        -
        unfold asgn_deref_sem_err in H8.
        destruct H8.
        destruct H8.
        unfold correspond in H10.
        destruct H10.
        destruct H11.
        pose proof H12 vcnt.
        destruct H13.
        rewrite <- H8 in H9.
        rewrite H9 in H14.
        tauto.
      ++++
      destruct H8.
      tauto.
    +++
    sets_unfold in H8.
    destruct H8 as [ss12].
    destruct H8.
    pose proof correspond_prop1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H10 H8.
    pose proof eval_comlist_seq_err (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) 
    ([SCAsgnVar (nat2Sname (S vcnt))
    (ex2se e2
       (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss12.
    destruct H12.
    pose proof H12 H9.
    destruct H14.
    ++++  pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H15 as [He21 [He22 He23]].
          pose proof He21 s1 ss12 H11 H14.
          tauto.
    ++++
      destruct H14 as [ss13].
      simpl in H14.
      sets_unfold in H14.
      destruct H14.
      pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H11 H14.
      destruct H15.
      - destruct H15.
        -- 
          destruct H15; [tauto|].
          pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H17 as [He21 [He22 He23]].
          pose proof He23 s1 ss12 ss13 H11 H14 H15.
          tauto.
        -- destruct H15.
          destruct H15.
          unfold correspond in H16.
          destruct H16.
          destruct H18.
          pose proof H19 (S vcnt).
          destruct H20.
          rewrite <- H15 in H17.
          rewrite H17 in H21.
          tauto.
      -   destruct H15.
          destruct H15.
          tauto.
  + pose proof H (S (S vcnt)) as H.
    destruct H as [IH1 [IH2 IH3]].
    rewrite Hp in H2.
    simpl.
    sets_unfold.
    unfold or_sem_err, NonSC_or. 
    pose proof eval_comlist_seq_err (ex2pre e1 (S (S vcnt))) 
    ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
         ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
         [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss1.
    destruct H.
    pose proof H H2.
    destruct H4.
    ++ pose proof IH1 s1 ss1 H1 H4.
       tauto.
    ++ sets_unfold in H4.
      destruct H4 as [ss11].
      destruct H4.
      pose proof eval_comlist_seq_err
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))]
      (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2
            (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss11.
      destruct H6.
      pose proof H6 H5.
      pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H4 as H10.
      destruct H8.
      +++
      simpl in H8.
      sets_unfold in H8.
      destruct H8.
      ++++
      destruct H8.
        -
        destruct H8; [tauto|].
        pose proof IH3 s1 ss1 ss11 H1 H4 H8.
        tauto.
        -
        unfold asgn_deref_sem_err in H8.
        destruct H8.
        destruct H8.
        unfold correspond in H10.
        destruct H10.
        destruct H11.
        pose proof H12 vcnt.
        destruct H13.
        rewrite <- H8 in H9.
        rewrite H9 in H14.
        tauto.
      ++++
      destruct H8.
      tauto.
    +++
    sets_unfold in H8.
    destruct H8 as [ss12].
    destruct H8.
    pose proof correspond_prop1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H10 H8.
    pose proof eval_comlist_seq_err (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) 
    ([SCAsgnVar (nat2Sname (S vcnt))
    (ex2se e2
       (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss12.
    destruct H12.
    pose proof H12 H9.
    destruct H14.
    ++++  pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H15 as [He21 [He22 He23]].
          pose proof He21 s1 ss12 H11 H14.
          tauto.
    ++++
      destruct H14 as [ss13].
      simpl in H14.
      sets_unfold in H14.
      destruct H14.
      pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H11 H14.
      destruct H15.
      - destruct H15.
        -- 
          destruct H15; [tauto|].
          pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H17 as [He21 [He22 He23]].
          pose proof He23 s1 ss12 ss13 H11 H14 H15.
          tauto.
        -- destruct H15.
          destruct H15.
          unfold correspond in H16.
          destruct H16.
          destruct H18.
          pose proof H19 (S vcnt).
          destruct H20.
          rewrite <- H15 in H17.
          rewrite H17 in H21.
          tauto.
      -   destruct H15.
          destruct H15.
          tauto.
  + pose proof H (S (S vcnt)) as H.
    destruct H as [IH1 [IH2 IH3]].
    rewrite Hp in H2.
    simpl.
    sets_unfold.
    unfold or_sem_err, NonSC_or. 
    pose proof eval_comlist_seq_err (ex2pre e1 (S (S vcnt))) 
    ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
         ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
         [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss1.
    destruct H.
    pose proof H H2.
    destruct H4.
    ++ pose proof IH1 s1 ss1 H1 H4.
       tauto.
    ++ sets_unfold in H4.
      destruct H4 as [ss11].
      destruct H4.
      pose proof eval_comlist_seq_err
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))]
      (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2
            (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss11.
      destruct H6.
      pose proof H6 H5.
      pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H4 as H10.
      destruct H8.
      +++
      simpl in H8.
      sets_unfold in H8.
      destruct H8.
      ++++
      destruct H8.
        -
        destruct H8; [tauto|].
        pose proof IH3 s1 ss1 ss11 H1 H4 H8.
        tauto.
        -
        unfold asgn_deref_sem_err in H8.
        destruct H8.
        destruct H8.
        unfold correspond in H10.
        destruct H10.
        destruct H11.
        pose proof H12 vcnt.
        destruct H13.
        rewrite <- H8 in H9.
        rewrite H9 in H14.
        tauto.
      ++++
      destruct H8.
      tauto.
    +++
    sets_unfold in H8.
    destruct H8 as [ss12].
    destruct H8.
    pose proof correspond_prop1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H10 H8.
    pose proof eval_comlist_seq_err (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) 
    ([SCAsgnVar (nat2Sname (S vcnt))
    (ex2se e2
       (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss12.
    destruct H12.
    pose proof H12 H9.
    destruct H14.
    ++++  pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H15 as [He21 [He22 He23]].
          pose proof He21 s1 ss12 H11 H14.
          tauto.
    ++++
      destruct H14 as [ss13].
      simpl in H14.
      sets_unfold in H14.
      destruct H14.
      pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H11 H14.
      destruct H15.
      - destruct H15.
        -- 
          destruct H15; [tauto|].
          pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H17 as [He21 [He22 He23]].
          pose proof He23 s1 ss12 ss13 H11 H14 H15.
          tauto.
        -- destruct H15.
          destruct H15.
          unfold correspond in H16.
          destruct H16.
          destruct H18.
          pose proof H19 (S vcnt).
          destruct H20.
          rewrite <- H15 in H17.
          rewrite H17 in H21.
          tauto.
      -   destruct H15.
          destruct H15.
          tauto.
  + pose proof H (S (S vcnt)) as H.
    destruct H as [IH1 [IH2 IH3]].
    rewrite Hp in H2.
    simpl.
    sets_unfold.
    unfold or_sem_err, NonSC_or. 
    pose proof eval_comlist_seq_err (ex2pre e1 (S (S vcnt))) 
    ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
         ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
         [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss1.
    destruct H.
    pose proof H H2.
    destruct H4.
    ++ pose proof IH1 s1 ss1 H1 H4.
       tauto.
    ++ sets_unfold in H4.
      destruct H4 as [ss11].
      destruct H4.
      pose proof eval_comlist_seq_err
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))]
      (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2
            (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss11.
      destruct H6.
      pose proof H6 H5.
      pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H4 as H10.
      destruct H8.
      +++
      simpl in H8.
      sets_unfold in H8.
      destruct H8.
      ++++
      destruct H8.
        -
        destruct H8; [tauto|].
        pose proof IH3 s1 ss1 ss11 H1 H4 H8.
        tauto.
        -
        unfold asgn_deref_sem_err in H8.
        destruct H8.
        destruct H8.
        unfold correspond in H10.
        destruct H10.
        destruct H11.
        pose proof H12 vcnt.
        destruct H13.
        rewrite <- H8 in H9.
        rewrite H9 in H14.
        tauto.
      ++++
      destruct H8.
      tauto.
    +++
    sets_unfold in H8.
    destruct H8 as [ss12].
    destruct H8.
    pose proof correspond_prop1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H10 H8.
    pose proof eval_comlist_seq_err (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) 
    ([SCAsgnVar (nat2Sname (S vcnt))
    (ex2se e2
       (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss12.
    destruct H12.
    pose proof H12 H9.
    destruct H14.
    ++++  pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H15 as [He21 [He22 He23]].
          pose proof He21 s1 ss12 H11 H14.
          tauto.
    ++++
      destruct H14 as [ss13].
      simpl in H14.
      sets_unfold in H14.
      destruct H14.
      pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H11 H14.
      destruct H15.
      - destruct H15.
        -- 
          destruct H15; [tauto|].
          pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H17 as [He21 [He22 He23]].
          pose proof He23 s1 ss12 ss13 H11 H14 H15.
          tauto.
        -- destruct H15.
          destruct H15.
          unfold correspond in H16.
          destruct H16.
          destruct H18.
          pose proof H19 (S vcnt).
          destruct H20.
          rewrite <- H15 in H17.
          rewrite H17 in H21.
          tauto.
      -   destruct H15.
          destruct H15.
          tauto.
  + pose proof H (S (S vcnt)) as H.
    destruct H as [IH1 [IH2 IH3]].
    rewrite Hp in H2.
    simpl.
    sets_unfold.
    unfold or_sem_err, NonSC_or. 
    pose proof eval_comlist_seq_err (ex2pre e1 (S (S vcnt))) 
    ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
         ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
         [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss1.
    destruct H.
    pose proof H H2.
    destruct H4.
    ++ pose proof IH1 s1 ss1 H1 H4.
       tauto.
    ++ sets_unfold in H4.
      destruct H4 as [ss11].
      destruct H4.
      pose proof eval_comlist_seq_err
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))]
      (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2
            (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss11.
      destruct H6.
      pose proof H6 H5.
      pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H4 as H10.
      destruct H8.
      +++
      simpl in H8.
      sets_unfold in H8.
      destruct H8.
      ++++
      destruct H8.
        -
        destruct H8; [tauto|].
        pose proof IH3 s1 ss1 ss11 H1 H4 H8.
        tauto.
        -
        unfold asgn_deref_sem_err in H8.
        destruct H8.
        destruct H8.
        unfold correspond in H10.
        destruct H10.
        destruct H11.
        pose proof H12 vcnt.
        destruct H13.
        rewrite <- H8 in H9.
        rewrite H9 in H14.
        tauto.
      ++++
      destruct H8.
      tauto.
    +++
    sets_unfold in H8.
    destruct H8 as [ss12].
    destruct H8.
    pose proof correspond_prop1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H10 H8.
    pose proof eval_comlist_seq_err (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) 
    ([SCAsgnVar (nat2Sname (S vcnt))
    (ex2se e2
       (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss12.
    destruct H12.
    pose proof H12 H9.
    destruct H14.
    ++++  pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H15 as [He21 [He22 He23]].
          pose proof He21 s1 ss12 H11 H14.
          tauto.
    ++++
      destruct H14 as [ss13].
      simpl in H14.
      sets_unfold in H14.
      destruct H14.
      pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H11 H14.
      destruct H15.
      - destruct H15.
        -- 
          destruct H15; [tauto|].
          pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H17 as [He21 [He22 He23]].
          pose proof He23 s1 ss12 ss13 H11 H14 H15.
          tauto.
        -- destruct H15.
          destruct H15.
          unfold correspond in H16.
          destruct H16.
          destruct H18.
          pose proof H19 (S vcnt).
          destruct H20.
          rewrite <- H15 in H17.
          rewrite H17 in H21.
          tauto.
      -   destruct H15.
          destruct H15.
          tauto.
  + pose proof H (S (S vcnt)) as H.
    destruct H as [IH1 [IH2 IH3]].
    rewrite Hp in H2.
    simpl.
    sets_unfold.
    unfold or_sem_err, NonSC_or. 
    pose proof eval_comlist_seq_err (ex2pre e1 (S (S vcnt))) 
    ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
         ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
         [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss1.
    destruct H.
    pose proof H H2.
    destruct H4.
    ++ pose proof IH1 s1 ss1 H1 H4.
       tauto.
    ++ sets_unfold in H4.
      destruct H4 as [ss11].
      destruct H4.
      pose proof eval_comlist_seq_err
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))]
      (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2
            (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss11.
      destruct H6.
      pose proof H6 H5.
      pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H4 as H10.
      destruct H8.
      +++
      simpl in H8.
      sets_unfold in H8.
      destruct H8.
      ++++
      destruct H8.
        -
        destruct H8; [tauto|].
        pose proof IH3 s1 ss1 ss11 H1 H4 H8.
        tauto.
        -
        unfold asgn_deref_sem_err in H8.
        destruct H8.
        destruct H8.
        unfold correspond in H10.
        destruct H10.
        destruct H11.
        pose proof H12 vcnt.
        destruct H13.
        rewrite <- H8 in H9.
        rewrite H9 in H14.
        tauto.
      ++++
      destruct H8.
      tauto.
    +++
    sets_unfold in H8.
    destruct H8 as [ss12].
    destruct H8.
    pose proof correspond_prop1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H10 H8.
    pose proof eval_comlist_seq_err (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) 
    ([SCAsgnVar (nat2Sname (S vcnt))
    (ex2se e2
       (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss12.
    destruct H12.
    pose proof H12 H9.
    destruct H14.
    ++++  pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H15 as [He21 [He22 He23]].
          pose proof He21 s1 ss12 H11 H14.
          tauto.
    ++++
      destruct H14 as [ss13].
      simpl in H14.
      sets_unfold in H14.
      destruct H14.
      pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H11 H14.
      destruct H15.
      - destruct H15.
        -- 
          destruct H15; [tauto|].
          pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H17 as [He21 [He22 He23]].
          pose proof He23 s1 ss12 ss13 H11 H14 H15.
          tauto.
        -- destruct H15.
          destruct H15.
          unfold correspond in H16.
          destruct H16.
          destruct H18.
          pose proof H19 (S vcnt).
          destruct H20.
          rewrite <- H15 in H17.
          rewrite H17 in H21.
          tauto.
      -   destruct H15.
          destruct H15.
          tauto.
  + pose proof H (S (S vcnt)) as H.
    destruct H as [IH1 [IH2 IH3]].
    rewrite Hp in H2.
    simpl.
    sets_unfold.
    unfold or_sem_err, NonSC_or. 
    pose proof eval_comlist_seq_err (ex2pre e1 (S (S vcnt))) 
    ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
         ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
         [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss1.
    destruct H.
    pose proof H H2.
    destruct H4.
    ++ pose proof IH1 s1 ss1 H1 H4.
       tauto.
    ++ sets_unfold in H4.
      destruct H4 as [ss11].
      destruct H4.
      pose proof eval_comlist_seq_err
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))]
      (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2
            (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss11.
      destruct H6.
      pose proof H6 H5.
      pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H4 as H10.
      destruct H8.
      +++
      simpl in H8.
      sets_unfold in H8.
      destruct H8.
      ++++
      destruct H8.
        -
        destruct H8; [tauto|].
        pose proof IH3 s1 ss1 ss11 H1 H4 H8.
        tauto.
        -
        unfold asgn_deref_sem_err in H8.
        destruct H8.
        destruct H8.
        unfold correspond in H10.
        destruct H10.
        destruct H11.
        pose proof H12 vcnt.
        destruct H13.
        rewrite <- H8 in H9.
        rewrite H9 in H14.
        tauto.
      ++++
      destruct H8.
      tauto.
    +++
    sets_unfold in H8.
    destruct H8 as [ss12].
    destruct H8.
    pose proof correspond_prop1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H10 H8.
    pose proof eval_comlist_seq_err (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) 
    ([SCAsgnVar (nat2Sname (S vcnt))
    (ex2se e2
       (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss12.
    destruct H12.
    pose proof H12 H9.
    destruct H14.
    ++++  pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H15 as [He21 [He22 He23]].
          pose proof He21 s1 ss12 H11 H14.
          tauto.
    ++++
      destruct H14 as [ss13].
      simpl in H14.
      sets_unfold in H14.
      destruct H14.
      pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H11 H14.
      destruct H15.
      - destruct H15.
        -- 
          destruct H15; [tauto|].
          pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H17 as [He21 [He22 He23]].
          pose proof He23 s1 ss12 ss13 H11 H14 H15.
          tauto.
        -- destruct H15.
          destruct H15.
          unfold correspond in H16.
          destruct H16.
          destruct H18.
          pose proof H19 (S vcnt).
          destruct H20.
          rewrite <- H15 in H17.
          rewrite H17 in H21.
          tauto.
      -   destruct H15.
          destruct H15.
          tauto.
  + pose proof H (S (S vcnt)) as H.
    destruct H as [IH1 [IH2 IH3]].
    rewrite Hp in H2.
    simpl.
    sets_unfold.
    unfold or_sem_err, NonSC_or. 
    pose proof eval_comlist_seq_err (ex2pre e1 (S (S vcnt))) 
    ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
         ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
         [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss1.
    destruct H.
    pose proof H H2.
    destruct H4.
    ++ pose proof IH1 s1 ss1 H1 H4.
       tauto.
    ++ sets_unfold in H4.
      destruct H4 as [ss11].
      destruct H4.
      pose proof eval_comlist_seq_err
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))]
      (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2
            (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss11.
      destruct H6.
      pose proof H6 H5.
      pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H4 as H10.
      destruct H8.
      +++
      simpl in H8.
      sets_unfold in H8.
      destruct H8.
      ++++
      destruct H8.
        -
        destruct H8; [tauto|].
        pose proof IH3 s1 ss1 ss11 H1 H4 H8.
        tauto.
        -
        unfold asgn_deref_sem_err in H8.
        destruct H8.
        destruct H8.
        unfold correspond in H10.
        destruct H10.
        destruct H11.
        pose proof H12 vcnt.
        destruct H13.
        rewrite <- H8 in H9.
        rewrite H9 in H14.
        tauto.
      ++++
      destruct H8.
      tauto.
    +++
    sets_unfold in H8.
    destruct H8 as [ss12].
    destruct H8.
    pose proof correspond_prop1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H10 H8.
    pose proof eval_comlist_seq_err (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) 
    ([SCAsgnVar (nat2Sname (S vcnt))
    (ex2se e2
       (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss12.
    destruct H12.
    pose proof H12 H9.
    destruct H14.
    ++++  pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H15 as [He21 [He22 He23]].
          pose proof He21 s1 ss12 H11 H14.
          tauto.
    ++++
      destruct H14 as [ss13].
      simpl in H14.
      sets_unfold in H14.
      destruct H14.
      pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H11 H14.
      destruct H15.
      - destruct H15.
        -- 
          destruct H15; [tauto|].
          pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H17 as [He21 [He22 He23]].
          pose proof He23 s1 ss12 ss13 H11 H14 H15.
          tauto.
        -- destruct H15.
          destruct H15.
          unfold correspond in H16.
          destruct H16.
          destruct H18.
          pose proof H19 (S vcnt).
          destruct H20.
          rewrite <- H15 in H17.
          rewrite H17 in H21.
          tauto.
      -   destruct H15.
          destruct H15.
          tauto.
  + pose proof H (S (S vcnt)) as H.
    destruct H as [IH1 [IH2 IH3]].
    rewrite Hp in H2.
    simpl.
    sets_unfold.
    unfold or_sem_err, NonSC_or. 
    pose proof eval_comlist_seq_err (ex2pre e1 (S (S vcnt))) 
    ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
         ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
         [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss1.
    destruct H.
    pose proof H H2.
    destruct H4.
    ++ pose proof IH1 s1 ss1 H1 H4.
       tauto.
    ++ sets_unfold in H4.
      destruct H4 as [ss11].
      destruct H4.
      pose proof eval_comlist_seq_err
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))]
      (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2
            (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss11.
      destruct H6.
      pose proof H6 H5.
      pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H4 as H10.
      destruct H8.
      +++
      simpl in H8.
      sets_unfold in H8.
      destruct H8.
      ++++
      destruct H8.
        -
        destruct H8; [tauto|].
        pose proof IH3 s1 ss1 ss11 H1 H4 H8.
        tauto.
        -
        unfold asgn_deref_sem_err in H8.
        destruct H8.
        destruct H8.
        unfold correspond in H10.
        destruct H10.
        destruct H11.
        pose proof H12 vcnt.
        destruct H13.
        rewrite <- H8 in H9.
        rewrite H9 in H14.
        tauto.
      ++++
      destruct H8.
      tauto.
    +++
    sets_unfold in H8.
    destruct H8 as [ss12].
    destruct H8.
    pose proof correspond_prop1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H10 H8.
    pose proof eval_comlist_seq_err (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) 
    ([SCAsgnVar (nat2Sname (S vcnt))
    (ex2se e2
       (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) ss12.
    destruct H12.
    pose proof H12 H9.
    destruct H14.
    ++++  pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H15 as [He21 [He22 He23]].
          pose proof He21 s1 ss12 H11 H14.
          tauto.
    ++++
      destruct H14 as [ss13].
      simpl in H14.
      sets_unfold in H14.
      destruct H14.
      pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H11 H14.
      destruct H15.
      - destruct H15.
        -- 
          destruct H15; [tauto|].
          pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))).
          destruct H17 as [He21 [He22 He23]].
          pose proof He23 s1 ss12 ss13 H11 H14 H15.
          tauto.
        -- destruct H15.
          destruct H15.
          unfold correspond in H16.
          destruct H16.
          destruct H18.
          pose proof H19 (S vcnt).
          destruct H20.
          rewrite <- H15 in H17.
          rewrite H17 in H21.
          tauto.
      -   destruct H15.
          destruct H15.
          tauto.
Qed.


Lemma Split_Serefine_err2_l_binop {NameX : Names} {NPX : NamesProperty}:
  forall (op : binop) (e1 e2 : expr),
  (forall (vcnt : nat), Serefine_err (ex2pre e1 vcnt) (ex2se e1 vcnt) e1)
  -> (forall (vcnt : nat), Serefine_err (ex2pre e2 vcnt) (ex2se e2 vcnt) e2)
  -> (forall (vcnt : nat), Serefine_err2_l (ex2pre (EBinop op e1 e2) vcnt) (ex2se (EBinop op e1 e2) vcnt) (EBinop op e1 e2)).
Proof.
  unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
  intros.
  destruct op; simpl; sets_unfold; tauto.
Qed.

Lemma Split_Serefine_err2_r_binop {NameX : Names} {NPX : NamesProperty}:
forall (op : binop) (e1 e2 : expr),
(forall (vcnt : nat), Serefine_err (ex2pre e1 vcnt) (ex2se e1 vcnt) e1)
-> (forall (vcnt : nat), Serefine_err (ex2pre e2 vcnt) (ex2se e2 vcnt) e2)
-> (forall (vcnt : nat), Serefine_err2_r (ex2pre (EBinop op e1 e2) vcnt) (ex2se (EBinop op e1 e2) vcnt) (EBinop op e1 e2)).
Proof.
  intros.
  unfold Serefine_err2_r.
  pose proof ex2pre_binop vcnt e1 e2 op.
  pose proof Split_Serefine_nrm e1 (S (S vcnt)) as [H1l H1r].
  pose proof Split_Serefine_nrm e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))) as [H2l H2r].
  destruct op.
  +
  intros.
  simpl.
  unfold or_sem_nrm, or_sem_err, NonSC_compute_nrm, NonSC_or, SC_or_compute_nrm.
  sets_unfold.
  rewrite H1 in H3.
  pose proof eval_comlist_seq_nrm 
    (ex2pre e1 (S (S vcnt)))
         ([SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e1 (S (S vcnt)))] ++
         [SCIf (genSECV (S vcnt))
            [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 1))]
            (ex2pre e2
               (nat_add (S (S vcnt))
                  (length (ex2pre e1 (S (S vcnt))))) ++
             [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2
                   (nat_add (S (S vcnt))
                      (length (ex2pre e1 (S (S vcnt))))))] ++
             [SCIf (genSECV (S vcnt))
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 1))]
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 0))]])]) ss1 ss2.
  destruct H5.
  pose proof H5 H3.
  sets_unfold in H7.
  destruct H7 as [ss11].
  destruct H7.
  pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H2 H7.
  pose proof eval_comlist_seq_nrm 
      [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e1 (S (S vcnt)))]
         [SCIf (genSECV (S vcnt))
            [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 1))]
            (ex2pre e2
               (nat_add (S (S vcnt))
                  (length (ex2pre e1 (S (S vcnt))))) ++
             [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2
                   (nat_add (S (S vcnt))
                      (length (ex2pre e1 (S (S vcnt))))))] ++
             [SCIf (genSECV (S vcnt))
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 1))]
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 0))]])] ss11 ss2.
  destruct H10.
  pose proof H10 H8.
  sets_unfold in H12.
  destruct H12 as [ss12].
  destruct H12.
  pose proof correspond_prop1 (S vcnt) (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H9 H12.
  simpl in H13.
  sets_unfold in H13.
  destruct H13.
  destruct H13.
  rewrite H15 in H13.
  destruct H13.
  ++
  destruct H13.
  destruct H13.
  unfold test_true in H13.
  sets_unfold in H13.
  destruct H13.
  rewrite <- H17 in H16.
  destruct H16.
  destruct H16.
  rewrite H18 in H16.
  destruct H16 as [i1[i2[?[?[?[?[?]]]]]]].
  revert H4.
  simpl.
  unfold deref_sem_err.
  sets_unfold.
  intros.
  destruct H4; [tauto|].
  destruct H4.
  destruct H4.
  pose proof H22 (nat2Sname vcnt).
  rewrite H4 in H25.
  rewrite H16 in H25.
  rewrite H25 in H21.
  rewrite H21 in H24.
  destruct H24; discriminate.
  ++
  destruct H13.
  destruct H13.
  unfold test_false in H13.
  sets_unfold in H13.
  destruct H13.
  assert ((Seval_r (genSECV (S vcnt))).(nrm) ss12 (Int64.repr 0)).
  {
    revert H13.
    simpl.
    tauto.
  }
  pose proof asgn_vcnt_ex2se_nrm_prop (ex2se e1 (S (S vcnt))) (S vcnt) ss11 ss12 H12 (Int64.repr 0) H18.
  pose proof H1r s1 ss1 ss11 (Int64.repr 0) H2 H7 H19.
  destruct H20; [|tauto].
  rewrite <- H17 in H16.
  pose proof eval_comlist_seq_nrm
    (ex2pre e2
            (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))
          ([SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2
                (S
                   (S
                      (nat_add vcnt
                         (length (ex2pre e1 (S (S vcnt)))))))),
          SCIf (genSECV (S vcnt))
            [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1))]
            [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0))]]) ss12 ss2.
  destruct H21.
  pose proof H21 H16.
  sets_unfold in H23.
  destruct H23 as [ss13].
  destruct H23.
  pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H14 H23.
  pose proof eval_comlist_seq_nrm 
    [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2
               (S
                  (S
                     (nat_add vcnt
                        (length (ex2pre e1 (S (S vcnt))))))))]
        [SCIf (genSECV (S vcnt))
           [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1))]
           [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0))]] ss13 ss2.
  destruct H26.
  pose proof H26 H24.
  sets_unfold in H28.
  destruct H28 as [ss14].
  destruct H28.
  pose proof correspond_prop1 (S vcnt) (ex2se e2
  (S
     (S
        (nat_add vcnt
           (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss14 H25 H28.
  simpl in H29.
  sets_unfold in H29.
  destruct H29.
  destruct H29.
  rewrite H31 in H29.
  destruct H29.
  +++
  destruct H29.
  destruct H29.
  unfold test_true in H29.
  sets_unfold in H29.
  destruct H29.
  rewrite <- H33 in H32.
  destruct H32.
  destruct H32.
  rewrite H34 in H32.
  destruct H32 as [i3[i4[?[?[?[?[?]]]]]]].
  revert H4.
  simpl.
  unfold deref_sem_err.
  sets_unfold.
  intros.
  destruct H4; [tauto|].
  destruct H4.
  destruct H4.
  destruct H29.
  pose proof H38 (nat2Sname vcnt).
  rewrite H4 in H41.
  rewrite H32 in H41.
  rewrite <- H41 in H40.
  rewrite H37 in H40.
  destruct H40; discriminate.
  +++
  destruct H29.
  destruct H29.
  unfold test_false in H29.
  sets_unfold in H29.
  destruct H29.
  rewrite <- H33 in H32.
  destruct H32.
  destruct H32.
  rewrite H34 in H32.
  destruct H32 as [i3[i4[?[?[?[?[?]]]]]]].
  revert H4.
  simpl.
  unfold deref_sem_err.
  sets_unfold.
  intros.
  destruct H4; [tauto|].
  destruct H4.
  destruct H4.
  destruct H29.
  pose proof H38 (nat2Sname vcnt).
  rewrite H4 in H41.
  rewrite H32 in H41.
  rewrite <- H41 in H40.
  rewrite H37 in H40.
  destruct H40; discriminate.
  +
  intros.
  simpl.
  unfold or_sem_nrm, or_sem_err, NonSC_compute_nrm, NonSC_or, SC_or_compute_nrm.
  sets_unfold.
  rewrite H1 in H3.
  pose proof eval_comlist_seq_nrm 
    (ex2pre e1 (S (S vcnt)))
         ([SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e1 (S (S vcnt)))] ++
         [SCIf (genSECV (S vcnt))
            (ex2pre e2
               (nat_add (S (S vcnt))
                  (length (ex2pre e1 (S (S vcnt))))) ++
             [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2
                   (nat_add (S (S vcnt))
                      (length (ex2pre e1 (S (S vcnt))))))] ++
             [SCIf (genSECV (S vcnt))
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 1))]
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 0))]])
              [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 0))]]) ss1 ss2.
  destruct H5.
  pose proof H5 H3.
  sets_unfold in H7.
  destruct H7 as [ss11].
  destruct H7.
  pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H2 H7.
  pose proof eval_comlist_seq_nrm 
      [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e1 (S (S vcnt)))]
         [SCIf (genSECV (S vcnt))
            (ex2pre e2
               (nat_add (S (S vcnt))
                  (length (ex2pre e1 (S (S vcnt))))) ++
             [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2
                   (nat_add (S (S vcnt))
                      (length (ex2pre e1 (S (S vcnt))))))] ++
             [SCIf (genSECV (S vcnt))
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 1))]
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 0))]])
              [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 0))]] ss11 ss2.
  destruct H10.
  pose proof H10 H8.
  sets_unfold in H12.
  destruct H12 as [ss12].
  destruct H12.
  pose proof correspond_prop1 (S vcnt) (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H9 H12.
  simpl in H13.
  sets_unfold in H13.
  destruct H13.
  destruct H13.
  rewrite H15 in H13.
  destruct H13.
  ++
  destruct H13.
  destruct H13.
  unfold test_true in H13.
  sets_unfold in H13.
  destruct H13.
  destruct H13.

  assert ((Seval_r (genSECV (S vcnt))).(nrm) ss12 x1).
  {
    revert H13.
    simpl.
    tauto.
  }
  pose proof asgn_vcnt_ex2se_nrm_prop (ex2se e1 (S (S vcnt))) (S vcnt) ss11 ss12 H12 x1 H18.
  pose proof H1r s1 ss1 ss11 x1 H2 H7 H19.
  destruct H20; [|tauto].
  rewrite <- H17 in H16.
  pose proof eval_comlist_seq_nrm
    (ex2pre e2
            (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))
          ([SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2
                (S
                   (S
                      (nat_add vcnt
                         (length (ex2pre e1 (S (S vcnt)))))))),
          SCIf (genSECV (S vcnt))
            [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1))]
            [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0))]]) ss12 ss2.
  destruct H21.
  pose proof H21 H16.
  sets_unfold in H23.
  destruct H23 as [ss13].
  destruct H23.
  pose proof correspond_prop2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 H14 H23.
  pose proof eval_comlist_seq_nrm 
    [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2
               (S
                  (S
                     (nat_add vcnt
                        (length (ex2pre e1 (S (S vcnt))))))))]
        [SCIf (genSECV (S vcnt))
           [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1))]
           [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0))]] ss13 ss2.
  destruct H26.
  pose proof H26 H24.
  sets_unfold in H28.
  destruct H28 as [ss14].
  destruct H28.
  pose proof correspond_prop1 (S vcnt) (ex2se e2
  (S
     (S
        (nat_add vcnt
           (length (ex2pre e1 (S (S vcnt)))))))) s1 ss13 ss14 H25 H28.
  simpl in H29.
  sets_unfold in H29.
  destruct H29.
  destruct H29.
  rewrite H31 in H29.
  destruct H29.
  +++
  destruct H29.
  destruct H29.
  unfold test_true in H29.
  sets_unfold in H29.
  destruct H29.
  rewrite <- H33 in H32.
  destruct H32.
  destruct H32.
  rewrite H34 in H32.
  destruct H32 as [i3[i4[?[?[?[?[?]]]]]]].
  revert H4.
  simpl.
  unfold deref_sem_err.
  sets_unfold.
  intros.
  destruct H4; [tauto|].
  destruct H4.
  destruct H4.
  destruct H29.
  pose proof H38 (nat2Sname vcnt).
  rewrite H4 in H41.
  rewrite H32 in H41.
  rewrite <- H41 in H40.
  rewrite H37 in H40.
  destruct H40; discriminate.
  +++
  destruct H29.
  destruct H29.
  unfold test_false in H29.
  sets_unfold in H29.
  destruct H29.
  rewrite <- H33 in H32.
  destruct H32.
  destruct H32.
  rewrite H34 in H32.
  destruct H32 as [i3[i4[?[?[?[?[?]]]]]]].
  revert H4.
  simpl.
  unfold deref_sem_err.
  sets_unfold.
  intros.
  destruct H4; [tauto|].
  destruct H4.
  destruct H4.
  destruct H29.
  pose proof H38 (nat2Sname vcnt).
  rewrite H4 in H41.
  rewrite H32 in H41.
  rewrite <- H41 in H40.
  rewrite H37 in H40.
  destruct H40; discriminate.
  ++
  destruct H13.
  destruct H13.
  unfold test_true in H13.
  sets_unfold in H13.
  destruct H13.
  rewrite <- H17 in H16.
  destruct H16.
  destruct H16.
  rewrite H18 in H16.
  destruct H16 as [i1[i2[?[?[?[?[?]]]]]]].
  revert H4.
  simpl.
  unfold deref_sem_err.
  sets_unfold.
  intros.
  destruct H4; [tauto|].
  destruct H4.
  destruct H4.
  pose proof H22 (nat2Sname vcnt).
  rewrite H4 in H25.
  rewrite H16 in H25.
  rewrite H25 in H21.
  rewrite H21 in H24.
  destruct H24; discriminate.
  + clear H1.
  revert H H0.
  unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
  intros H H0 s1 ss1 ss2 H1 H2 H3.
  pose proof H (S vcnt) as H.
  destruct H as [IH1 [IH2 IH3]].
  pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
  sets_unfold in Hp.
  pose proof correspond_prop1 as Hc1.
  pose proof correspond_prop2 as Hc2.
  pose proof Split_Serefine_nrm e1 as Hsen1.
  pose proof Split_Serefine_nrm e2 as Hsen2.
  unfold Serefine_nrm, Serefine_nrm_r in Hsen1, Hsen2.
  simpl in H2.
    assert (
    (Seval_comlist  
    (ex2pre e1 (S (S vcnt)) ++
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      (ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) ++
      [SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1 ss2).
    {
      simpl.
      tauto.
    }
    clear H2.
    pose proof midstate_binop vcnt e1 e2 ss1 ss2 H.
    destruct H2 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
    pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H2 as Hcm1.
    pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 Hcm1 H4 as Hcm2.
    pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 Hcm2 H5 as Hcm3.
    clear Hc1 Hc2.
    pose proof Hsen1 (S (S vcnt)) as Hsen1.
    pose proof Hsen2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) as Hsen2.
    destruct Hsen1 as [H100 Hsen1].
    destruct Hsen2 as [H200 Hsen2].
    clear H100 H200.
    pose proof Hsen1 s1 ss1 ss11 as Hsen1.
    pose proof Hsen2 s1 ss12 ss13 as Hsen2.
    revert H3.
    simpl.
    sets_unfold.
    intros.
    destruct H3.
    - destruct H3; [tauto|].
      unfold deref_sem_err in H3.
      destruct H3.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname vcnt).
      pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
      pose proof Hsen2 x2 Hcm2 H5 H8.
      sets_unfold in H4.
      destruct H4.
      destruct H4.
      rewrite H17 in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold var_sem_l, EDenote.nrm in H4.
      destruct H18.
      destruct H19.
      destruct H20.
      destruct H21.
      pose proof Hsen1 x5 H1 H2 H18.
      destruct H16, H23.
      * pose proof H21 (nat2Sname vcnt).
        rewrite H24 in H4.
        rewrite <- H14 in H3.
        rewrite H3 in H15.
        rewrite H4 in H15.
        rewrite H15 in H20.
        pose proof H11 (nat2Sname (S vcnt)).
        pose proof classic (ss13.(env) (nat2Sname (S vcnt)) = ss13.(env) (nat2Sname vcnt)).
        destruct H26.
        -- rewrite H26 in H6.
          rewrite H3 in H6.
          rewrite H6 in H13.
          rewrite H10 in H13.
          destruct H13; discriminate.
        -- pose proof H12 x.
           rewrite H6 in H26.
           rewrite H3 in H26.
           pose proof H27 H26.
           rewrite H28 in H20.
           rewrite H20 in H13.
           destruct H13; discriminate.
      * tauto.
      * tauto.
      * tauto.
    - destruct H3; [tauto|].
      destruct H3.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname (S vcnt)).
      rewrite H3 in H14.
      rewrite H6 in H14.
      rewrite <- H14 in H13.
      rewrite H10 in H13.
      destruct H13; discriminate.
  + clear H1.
  revert H H0.
  unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
  intros H H0 s1 ss1 ss2 H1 H2 H3.
  pose proof H (S vcnt) as H.
  destruct H as [IH1 [IH2 IH3]].
  pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
  sets_unfold in Hp.
  pose proof correspond_prop1 as Hc1.
  pose proof correspond_prop2 as Hc2.
  pose proof Split_Serefine_nrm e1 as Hsen1.
  pose proof Split_Serefine_nrm e2 as Hsen2.
  unfold Serefine_nrm, Serefine_nrm_r in Hsen1, Hsen2.
  simpl in H2.
  assert (
    (Seval_comlist  
    (ex2pre e1 (S (S vcnt)) ++
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      (ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) ++
      [SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1 ss2).
    {
      simpl.
      tauto.
    }
    clear H2.
    pose proof midstate_binop vcnt e1 e2 ss1 ss2 H.
    destruct H2 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
    pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H2 as Hcm1.
    pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 Hcm1 H4 as Hcm2.
    pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 Hcm2 H5 as Hcm3.
    clear Hc1 Hc2.
    pose proof Hsen1 (S (S vcnt)) as Hsen1.
    pose proof Hsen2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) as Hsen2.
    destruct Hsen1 as [H100 Hsen1].
    destruct Hsen2 as [H200 Hsen2].
    clear H100 H200.
    pose proof Hsen1 s1 ss1 ss11 as Hsen1.
    pose proof Hsen2 s1 ss12 ss13 as Hsen2.
    revert H3.
    simpl.
    sets_unfold.
    intros.
    destruct H3.
    - destruct H3; [tauto|].
      unfold deref_sem_err in H3.
      destruct H3.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname vcnt).
      pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
      pose proof Hsen2 x2 Hcm2 H5 H8.
      sets_unfold in H4.
      destruct H4.
      destruct H4.
      rewrite H17 in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold var_sem_l, EDenote.nrm in H4.
      destruct H18.
      destruct H19.
      destruct H20.
      destruct H21.
      pose proof Hsen1 x5 H1 H2 H18.
      destruct H16, H23.
      * pose proof H21 (nat2Sname vcnt).
        rewrite H24 in H4.
        rewrite <- H14 in H3.
        rewrite H3 in H15.
        rewrite H4 in H15.
        rewrite H15 in H20.
        pose proof H11 (nat2Sname (S vcnt)).
        pose proof classic (ss13.(env) (nat2Sname (S vcnt)) = ss13.(env) (nat2Sname vcnt)).
        destruct H26.
        -- rewrite H26 in H6.
          rewrite H3 in H6.
          rewrite H6 in H13.
          rewrite H10 in H13.
          destruct H13; discriminate.
        -- pose proof H12 x.
           rewrite H6 in H26.
           rewrite H3 in H26.
           pose proof H27 H26.
           rewrite H28 in H20.
           rewrite H20 in H13.
           destruct H13; discriminate.
      * tauto.
      * tauto.
      * tauto.
    - destruct H3; [tauto|].
      destruct H3.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname (S vcnt)).
      rewrite H3 in H14.
      rewrite H6 in H14.
      rewrite <- H14 in H13.
      rewrite H10 in H13.
      destruct H13; discriminate.
  + clear H1.
  revert H H0.
  unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
  intros H H0 s1 ss1 ss2 H1 H2 H3.
  pose proof H (S vcnt) as H.
  destruct H as [IH1 [IH2 IH3]].
  pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
  sets_unfold in Hp.
  pose proof correspond_prop1 as Hc1.
  pose proof correspond_prop2 as Hc2.
  pose proof Split_Serefine_nrm e1 as Hsen1.
  pose proof Split_Serefine_nrm e2 as Hsen2.
  unfold Serefine_nrm, Serefine_nrm_r in Hsen1, Hsen2.
  simpl in H2.
  assert (
    (Seval_comlist  
    (ex2pre e1 (S (S vcnt)) ++
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      (ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) ++
      [SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1 ss2).
    {
      simpl.
      tauto.
    }
    clear H2.
    pose proof midstate_binop vcnt e1 e2 ss1 ss2 H.
    destruct H2 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
    pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H2 as Hcm1.
    pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 Hcm1 H4 as Hcm2.
    pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 Hcm2 H5 as Hcm3.
    clear Hc1 Hc2.
    pose proof Hsen1 (S (S vcnt)) as Hsen1.
    pose proof Hsen2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) as Hsen2.
    destruct Hsen1 as [H100 Hsen1].
    destruct Hsen2 as [H200 Hsen2].
    clear H100 H200.
    pose proof Hsen1 s1 ss1 ss11 as Hsen1.
    pose proof Hsen2 s1 ss12 ss13 as Hsen2.
    revert H3.
    simpl.
    sets_unfold.
    intros.
    destruct H3.
    - destruct H3; [tauto|].
      unfold deref_sem_err in H3.
      destruct H3.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname vcnt).
      pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
      pose proof Hsen2 x2 Hcm2 H5 H8.
      sets_unfold in H4.
      destruct H4.
      destruct H4.
      rewrite H17 in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold var_sem_l, EDenote.nrm in H4.
      destruct H18.
      destruct H19.
      destruct H20.
      destruct H21.
      pose proof Hsen1 x5 H1 H2 H18.
      destruct H16, H23.
      * pose proof H21 (nat2Sname vcnt).
        rewrite H24 in H4.
        rewrite <- H14 in H3.
        rewrite H3 in H15.
        rewrite H4 in H15.
        rewrite H15 in H20.
        pose proof H11 (nat2Sname (S vcnt)).
        pose proof classic (ss13.(env) (nat2Sname (S vcnt)) = ss13.(env) (nat2Sname vcnt)).
        destruct H26.
        -- rewrite H26 in H6.
          rewrite H3 in H6.
          rewrite H6 in H13.
          rewrite H10 in H13.
          destruct H13; discriminate.
        -- pose proof H12 x.
           rewrite H6 in H26.
           rewrite H3 in H26.
           pose proof H27 H26.
           rewrite H28 in H20.
           rewrite H20 in H13.
           destruct H13; discriminate.
      * tauto.
      * tauto.
      * tauto.
    - destruct H3; [tauto|].
      destruct H3.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname (S vcnt)).
      rewrite H3 in H14.
      rewrite H6 in H14.
      rewrite <- H14 in H13.
      rewrite H10 in H13.
      destruct H13; discriminate.
  + clear H1.
  revert H H0.
  unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
  intros H H0 s1 ss1 ss2 H1 H2 H3.
  pose proof H (S vcnt) as H.
  destruct H as [IH1 [IH2 IH3]].
  pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
  sets_unfold in Hp.
  pose proof correspond_prop1 as Hc1.
  pose proof correspond_prop2 as Hc2.
  pose proof Split_Serefine_nrm e1 as Hsen1.
  pose proof Split_Serefine_nrm e2 as Hsen2.
  unfold Serefine_nrm, Serefine_nrm_r in Hsen1, Hsen2.
  simpl in H2.
  assert (
    (Seval_comlist  
    (ex2pre e1 (S (S vcnt)) ++
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      (ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) ++
      [SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1 ss2).
    {
      simpl.
      tauto.
    }
    clear H2.
    pose proof midstate_binop vcnt e1 e2 ss1 ss2 H.
    destruct H2 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
    pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H2 as Hcm1.
    pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 Hcm1 H4 as Hcm2.
    pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 Hcm2 H5 as Hcm3.
    clear Hc1 Hc2.
    pose proof Hsen1 (S (S vcnt)) as Hsen1.
    pose proof Hsen2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) as Hsen2.
    destruct Hsen1 as [H100 Hsen1].
    destruct Hsen2 as [H200 Hsen2].
    clear H100 H200.
    pose proof Hsen1 s1 ss1 ss11 as Hsen1.
    pose proof Hsen2 s1 ss12 ss13 as Hsen2.
    revert H3.
    simpl.
    sets_unfold.
    intros.
    destruct H3.
    - destruct H3; [tauto|].
      unfold deref_sem_err in H3.
      destruct H3.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname vcnt).
      pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
      pose proof Hsen2 x2 Hcm2 H5 H8.
      sets_unfold in H4.
      destruct H4.
      destruct H4.
      rewrite H17 in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold var_sem_l, EDenote.nrm in H4.
      destruct H18.
      destruct H19.
      destruct H20.
      destruct H21.
      pose proof Hsen1 x5 H1 H2 H18.
      destruct H16, H23.
      * pose proof H21 (nat2Sname vcnt).
        rewrite H24 in H4.
        rewrite <- H14 in H3.
        rewrite H3 in H15.
        rewrite H4 in H15.
        rewrite H15 in H20.
        pose proof H11 (nat2Sname (S vcnt)).
        pose proof classic (ss13.(env) (nat2Sname (S vcnt)) = ss13.(env) (nat2Sname vcnt)).
        destruct H26.
        -- rewrite H26 in H6.
          rewrite H3 in H6.
          rewrite H6 in H13.
          rewrite H10 in H13.
          destruct H13; discriminate.
        -- pose proof H12 x.
           rewrite H6 in H26.
           rewrite H3 in H26.
           pose proof H27 H26.
           rewrite H28 in H20.
           rewrite H20 in H13.
           destruct H13; discriminate.
      * tauto.
      * tauto.
      * tauto.
    - destruct H3; [tauto|].
      destruct H3.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname (S vcnt)).
      rewrite H3 in H14.
      rewrite H6 in H14.
      rewrite <- H14 in H13.
      rewrite H10 in H13.
      destruct H13; discriminate.
  + clear H1.
  revert H H0.
  unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
  intros H H0 s1 ss1 ss2 H1 H2 H3.
  pose proof H (S vcnt) as H.
  destruct H as [IH1 [IH2 IH3]].
  pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
  sets_unfold in Hp.
  pose proof correspond_prop1 as Hc1.
  pose proof correspond_prop2 as Hc2.
  pose proof Split_Serefine_nrm e1 as Hsen1.
  pose proof Split_Serefine_nrm e2 as Hsen2.
  unfold Serefine_nrm, Serefine_nrm_r in Hsen1, Hsen2.
  simpl in H2.
  assert (
    (Seval_comlist  
    (ex2pre e1 (S (S vcnt)) ++
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      (ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) ++
      [SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1 ss2).
    {
      simpl.
      tauto.
    }
    clear H2.
    pose proof midstate_binop vcnt e1 e2 ss1 ss2 H.
    destruct H2 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
    pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H2 as Hcm1.
    pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 Hcm1 H4 as Hcm2.
    pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 Hcm2 H5 as Hcm3.
    clear Hc1 Hc2.
    pose proof Hsen1 (S (S vcnt)) as Hsen1.
    pose proof Hsen2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) as Hsen2.
    destruct Hsen1 as [H100 Hsen1].
    destruct Hsen2 as [H200 Hsen2].
    clear H100 H200.
    pose proof Hsen1 s1 ss1 ss11 as Hsen1.
    pose proof Hsen2 s1 ss12 ss13 as Hsen2.
    revert H3.
    simpl.
    sets_unfold.
    intros.
    destruct H3.
    - destruct H3; [tauto|].
      unfold deref_sem_err in H3.
      destruct H3.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname vcnt).
      pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
      pose proof Hsen2 x2 Hcm2 H5 H8.
      sets_unfold in H4.
      destruct H4.
      destruct H4.
      rewrite H17 in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold var_sem_l, EDenote.nrm in H4.
      destruct H18.
      destruct H19.
      destruct H20.
      destruct H21.
      pose proof Hsen1 x5 H1 H2 H18.
      destruct H16, H23.
      * pose proof H21 (nat2Sname vcnt).
        rewrite H24 in H4.
        rewrite <- H14 in H3.
        rewrite H3 in H15.
        rewrite H4 in H15.
        rewrite H15 in H20.
        pose proof H11 (nat2Sname (S vcnt)).
        pose proof classic (ss13.(env) (nat2Sname (S vcnt)) = ss13.(env) (nat2Sname vcnt)).
        destruct H26.
        -- rewrite H26 in H6.
          rewrite H3 in H6.
          rewrite H6 in H13.
          rewrite H10 in H13.
          destruct H13; discriminate.
        -- pose proof H12 x.
           rewrite H6 in H26.
           rewrite H3 in H26.
           pose proof H27 H26.
           rewrite H28 in H20.
           rewrite H20 in H13.
           destruct H13; discriminate.
      * tauto.
      * tauto.
      * tauto.
    - destruct H3; [tauto|].
      destruct H3.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname (S vcnt)).
      rewrite H3 in H14.
      rewrite H6 in H14.
      rewrite <- H14 in H13.
      rewrite H10 in H13.
      destruct H13; discriminate.
  + clear H1.
  revert H H0.
  unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
  intros H H0 s1 ss1 ss2 H1 H2 H3.
  pose proof H (S vcnt) as H.
  destruct H as [IH1 [IH2 IH3]].
  pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
  sets_unfold in Hp.
  pose proof correspond_prop1 as Hc1.
  pose proof correspond_prop2 as Hc2.
  pose proof Split_Serefine_nrm e1 as Hsen1.
  pose proof Split_Serefine_nrm e2 as Hsen2.
  unfold Serefine_nrm, Serefine_nrm_r in Hsen1, Hsen2.
  simpl in H2.
  assert (
    (Seval_comlist  
    (ex2pre e1 (S (S vcnt)) ++
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      (ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) ++
      [SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1 ss2).
    {
      simpl.
      tauto.
    }
    clear H2.
    pose proof midstate_binop vcnt e1 e2 ss1 ss2 H.
    destruct H2 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
    pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H2 as Hcm1.
    pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 Hcm1 H4 as Hcm2.
    pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 Hcm2 H5 as Hcm3.
    clear Hc1 Hc2.
    pose proof Hsen1 (S (S vcnt)) as Hsen1.
    pose proof Hsen2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) as Hsen2.
    destruct Hsen1 as [H100 Hsen1].
    destruct Hsen2 as [H200 Hsen2].
    clear H100 H200.
    pose proof Hsen1 s1 ss1 ss11 as Hsen1.
    pose proof Hsen2 s1 ss12 ss13 as Hsen2.
    revert H3.
    simpl.
    sets_unfold.
    intros.
    destruct H3.
    - destruct H3; [tauto|].
      unfold deref_sem_err in H3.
      destruct H3.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname vcnt).
      pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
      pose proof Hsen2 x2 Hcm2 H5 H8.
      sets_unfold in H4.
      destruct H4.
      destruct H4.
      rewrite H17 in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold var_sem_l, EDenote.nrm in H4.
      destruct H18.
      destruct H19.
      destruct H20.
      destruct H21.
      pose proof Hsen1 x5 H1 H2 H18.
      destruct H16, H23.
      * pose proof H21 (nat2Sname vcnt).
        rewrite H24 in H4.
        rewrite <- H14 in H3.
        rewrite H3 in H15.
        rewrite H4 in H15.
        rewrite H15 in H20.
        pose proof H11 (nat2Sname (S vcnt)).
        pose proof classic (ss13.(env) (nat2Sname (S vcnt)) = ss13.(env) (nat2Sname vcnt)).
        destruct H26.
        -- rewrite H26 in H6.
          rewrite H3 in H6.
          rewrite H6 in H13.
          rewrite H10 in H13.
          destruct H13; discriminate.
        -- pose proof H12 x.
           rewrite H6 in H26.
           rewrite H3 in H26.
           pose proof H27 H26.
           rewrite H28 in H20.
           rewrite H20 in H13.
           destruct H13; discriminate.
      * tauto.
      * tauto.
      * tauto.
    - destruct H3; [tauto|].
      destruct H3.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname (S vcnt)).
      rewrite H3 in H14.
      rewrite H6 in H14.
      rewrite <- H14 in H13.
      rewrite H10 in H13.
      destruct H13; discriminate.
  + clear H1.
  revert H H0.
  unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
  intros H H0 s1 ss1 ss2 H1 H2 H3.
  pose proof H (S vcnt) as H.
  destruct H as [IH1 [IH2 IH3]].
  pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
  sets_unfold in Hp.
  pose proof correspond_prop1 as Hc1.
  pose proof correspond_prop2 as Hc2.
  pose proof Split_Serefine_nrm e1 as Hsen1.
  pose proof Split_Serefine_nrm e2 as Hsen2.
  unfold Serefine_nrm, Serefine_nrm_r in Hsen1, Hsen2.
  simpl in H2.
  assert (
    (Seval_comlist  
    (ex2pre e1 (S (S vcnt)) ++
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      (ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) ++
      [SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1 ss2).
    {
      simpl.
      tauto.
    }
    clear H2.
    pose proof midstate_binop vcnt e1 e2 ss1 ss2 H.
    destruct H2 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
    pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H2 as Hcm1.
    pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 Hcm1 H4 as Hcm2.
    pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 Hcm2 H5 as Hcm3.
    clear Hc1 Hc2.
    pose proof Hsen1 (S (S vcnt)) as Hsen1.
    pose proof Hsen2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) as Hsen2.
    destruct Hsen1 as [H100 Hsen1].
    destruct Hsen2 as [H200 Hsen2].
    clear H100 H200.
    pose proof Hsen1 s1 ss1 ss11 as Hsen1.
    pose proof Hsen2 s1 ss12 ss13 as Hsen2.
    revert H3.
    simpl.
    sets_unfold.
    intros.
    destruct H3.
    - destruct H3.
      ++ destruct H3; [tauto|].
      unfold deref_sem_err in H3.
      destruct H3.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname vcnt).
      pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
      pose proof Hsen2 x2 Hcm2 H5 H8.
      sets_unfold in H4.
      destruct H4.
      destruct H4.
      rewrite H17 in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold var_sem_l, EDenote.nrm in H4.
      destruct H18.
      destruct H19.
      destruct H20.
      destruct H21.
      pose proof Hsen1 x5 H1 H2 H18.
      destruct H16, H23.
      * pose proof H21 (nat2Sname vcnt).
        rewrite H24 in H4.
        rewrite <- H14 in H3.
        rewrite H3 in H15.
        rewrite H4 in H15.
        rewrite H15 in H20.
        pose proof H11 (nat2Sname (S vcnt)).
        pose proof classic (ss13.(env) (nat2Sname (S vcnt)) = ss13.(env) (nat2Sname vcnt)).
        destruct H26.
        -- rewrite H26 in H6.
          rewrite H3 in H6.
          rewrite H6 in H13.
          rewrite H10 in H13.
          destruct H13; discriminate.
        -- pose proof H12 x.
           rewrite H6 in H26.
           rewrite H3 in H26.
           pose proof H27 H26.
           rewrite H28 in H20.
           rewrite H20 in H13.
           destruct H13; discriminate.
        * tauto.
        * tauto.
        * tauto.
    ++ destruct H3; [tauto|].
      unfold deref_sem_err in H3.
      destruct H3.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname vcnt).
      pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
      pose proof Hsen2 x2 Hcm2 H5 H8.
      sets_unfold in H4.
      destruct H4.
      destruct H4.
      rewrite H17 in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold var_sem_l, EDenote.nrm in H4.
      destruct H18.
      destruct H19.
      destruct H20.
      destruct H21.
      pose proof Hsen1 x5 H1 H2 H18.
      destruct H16, H23.
      * pose proof H21 (nat2Sname vcnt).
        pose proof H11 (nat2Sname (S vcnt)).
        rewrite H25 in H6.
        rewrite H3 in H6.
        rewrite H6 in H13.
        rewrite H10 in H13.
        destruct H13; discriminate.
      * tauto.
      * tauto.
      * tauto.
    - destruct H3.
      destruct H3.
      destruct H3 as [H3 H50].
      destruct H3.
      destruct H50 as [H50 H51].
      destruct H50 as [x2 H52].
      unfold arith_sem1_err.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname vcnt).
      pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
      pose proof Hsen2 x5 Hcm2 H5 H8.
      sets_unfold in H4.
      destruct H4.
      destruct H4.
      rewrite H17 in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold var_sem_l, EDenote.nrm in H4.
      destruct H18.
      destruct H19.
      destruct H20.
      destruct H21.
      pose proof Hsen1 x8 H1 H2 H18.
      destruct H16, H23.
      * right.
        exists x8,x5.
        split; [tauto|].
        split; [tauto|].
        pose proof H21 (nat2Sname vcnt).
        rewrite H24 in H4.
        rewrite H4 in H15.
        rewrite H15 in H20.
        pose proof classic (ss13.(env) (nat2Sname (S vcnt)) = ss13.(env) (nat2Sname vcnt)).
        destruct H25.
        -- pose proof trans_prop2 (S vcnt) vcnt ss13.
           destruct H26.
           pose proof H27 H25.
           lia.
        -- pose proof H12 x1.
           rewrite H6 in H25.
           rewrite H3 in H14.
           rewrite H14 in H25.
           pose proof H26 H25.
           rewrite H13 in H27.
           rewrite H14 in H20.
           rewrite H20 in H27.
           pose proof some_val x8 x.
           destruct H28.
           pose proof H28 H27.
           rewrite H30.
           destruct H52.
           pose proof H11 (nat2Sname (S vcnt)).
           rewrite H31 in H33.
           rewrite H6 in H33.
           rewrite H33 in H10.
           rewrite H10 in H32.
           pose proof some_val x5 x0.
           destruct H34.
           pose proof H34 H32.
           rewrite H36.
           tauto.
      * tauto.
      * tauto.
      * tauto.
  + clear H1.
  revert H H0.
  unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
  intros H H0 s1 ss1 ss2 H1 H2 H3.
  pose proof H (S vcnt) as H.
  destruct H as [IH1 [IH2 IH3]].
  pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
  sets_unfold in Hp.
  pose proof correspond_prop1 as Hc1.
  pose proof correspond_prop2 as Hc2.
  pose proof Split_Serefine_nrm e1 as Hsen1.
  pose proof Split_Serefine_nrm e2 as Hsen2.
  unfold Serefine_nrm, Serefine_nrm_r in Hsen1, Hsen2.
  simpl in H2.
  assert (
    (Seval_comlist  
    (ex2pre e1 (S (S vcnt)) ++
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      (ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) ++
      [SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1 ss2).
    {
      simpl.
      tauto.
    }
    clear H2.
    pose proof midstate_binop vcnt e1 e2 ss1 ss2 H.
    destruct H2 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
    pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H2 as Hcm1.
    pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 Hcm1 H4 as Hcm2.
    pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 Hcm2 H5 as Hcm3.
    clear Hc1 Hc2.
    pose proof Hsen1 (S (S vcnt)) as Hsen1.
    pose proof Hsen2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) as Hsen2.
    destruct Hsen1 as [H100 Hsen1].
    destruct Hsen2 as [H200 Hsen2].
    clear H100 H200.
    pose proof Hsen1 s1 ss1 ss11 as Hsen1.
    pose proof Hsen2 s1 ss12 ss13 as Hsen2.
    revert H3.
    simpl.
    sets_unfold.
    intros.
    destruct H3.
    - destruct H3.
      ++ destruct H3; [tauto|].
      unfold deref_sem_err in H3.
      destruct H3.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname vcnt).
      pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
      pose proof Hsen2 x2 Hcm2 H5 H8.
      sets_unfold in H4.
      destruct H4.
      destruct H4.
      rewrite H17 in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold var_sem_l, EDenote.nrm in H4.
      destruct H18.
      destruct H19.
      destruct H20.
      destruct H21.
      pose proof Hsen1 x5 H1 H2 H18.
      destruct H16, H23.
      * pose proof H21 (nat2Sname vcnt).
        rewrite H24 in H4.
        rewrite <- H14 in H3.
        rewrite H3 in H15.
        rewrite H4 in H15.
        rewrite H15 in H20.
        pose proof H11 (nat2Sname (S vcnt)).
        pose proof classic (ss13.(env) (nat2Sname (S vcnt)) = ss13.(env) (nat2Sname vcnt)).
        destruct H26.
        -- rewrite H26 in H6.
          rewrite H3 in H6.
          rewrite H6 in H13.
          rewrite H10 in H13.
          destruct H13; discriminate.
        -- pose proof H12 x.
           rewrite H6 in H26.
           rewrite H3 in H26.
           pose proof H27 H26.
           rewrite H28 in H20.
           rewrite H20 in H13.
           destruct H13; discriminate.
        * tauto.
        * tauto.
        * tauto.
    ++ destruct H3; [tauto|].
      unfold deref_sem_err in H3.
      destruct H3.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname vcnt).
      pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
      pose proof Hsen2 x2 Hcm2 H5 H8.
      sets_unfold in H4.
      destruct H4.
      destruct H4.
      rewrite H17 in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold var_sem_l, EDenote.nrm in H4.
      destruct H18.
      destruct H19.
      destruct H20.
      destruct H21.
      pose proof Hsen1 x5 H1 H2 H18.
      destruct H16, H23.
      * pose proof H21 (nat2Sname vcnt).
        pose proof H11 (nat2Sname (S vcnt)).
        rewrite H25 in H6.
        rewrite H3 in H6.
        rewrite H6 in H13.
        rewrite H10 in H13.
        destruct H13; discriminate.
      * tauto.
      * tauto.
      * tauto.
    - destruct H3.
      destruct H3.
      destruct H3 as [H3 H50].
      destruct H3.
      destruct H50 as [H50 H51].
      destruct H50 as [x2 H52].
      unfold arith_sem1_err.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname vcnt).
      pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
      pose proof Hsen2 x5 Hcm2 H5 H8.
      sets_unfold in H4.
      destruct H4.
      destruct H4.
      rewrite H17 in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold var_sem_l, EDenote.nrm in H4.
      destruct H18.
      destruct H19.
      destruct H20.
      destruct H21.
      pose proof Hsen1 x8 H1 H2 H18.
      destruct H16, H23.
      * right.
        exists x8,x5.
        split; [tauto|].
        split; [tauto|].
        pose proof H21 (nat2Sname vcnt).
        rewrite H24 in H4.
        rewrite H4 in H15.
        rewrite H15 in H20.
        pose proof classic (ss13.(env) (nat2Sname (S vcnt)) = ss13.(env) (nat2Sname vcnt)).
        destruct H25.
        -- pose proof trans_prop2 (S vcnt) vcnt ss13.
           destruct H26.
           pose proof H27 H25.
           lia.
        -- pose proof H12 x1.
           rewrite H6 in H25.
           rewrite H3 in H14.
           rewrite H14 in H25.
           pose proof H26 H25.
           rewrite H13 in H27.
           rewrite H14 in H20.
           rewrite H20 in H27.
           pose proof some_val x8 x.
           destruct H28.
           pose proof H28 H27.
           rewrite H30.
           destruct H52.
           pose proof H11 (nat2Sname (S vcnt)).
           rewrite H31 in H33.
           rewrite H6 in H33.
           rewrite H33 in H10.
           rewrite H10 in H32.
           pose proof some_val x5 x0.
           destruct H34.
           pose proof H34 H32.
           rewrite H36.
           tauto.
      * tauto.
      * tauto.
      * tauto.
  + clear H1.
  revert H H0.
  unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
  intros H H0 s1 ss1 ss2 H1 H2 H3.
  pose proof H (S vcnt) as H.
  destruct H as [IH1 [IH2 IH3]].
  pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
  sets_unfold in Hp.
  pose proof correspond_prop1 as Hc1.
  pose proof correspond_prop2 as Hc2.
  pose proof Split_Serefine_nrm e1 as Hsen1.
  pose proof Split_Serefine_nrm e2 as Hsen2.
  unfold Serefine_nrm, Serefine_nrm_r in Hsen1, Hsen2.
  simpl in H2.
  assert (
    (Seval_comlist  
    (ex2pre e1 (S (S vcnt)) ++
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      (ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) ++
      [SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1 ss2).
    {
      simpl.
      tauto.
    }
    clear H2.
    pose proof midstate_binop vcnt e1 e2 ss1 ss2 H.
    destruct H2 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
    pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H2 as Hcm1.
    pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 Hcm1 H4 as Hcm2.
    pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 Hcm2 H5 as Hcm3.
    clear Hc1 Hc2.
    pose proof Hsen1 (S (S vcnt)) as Hsen1.
    pose proof Hsen2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) as Hsen2.
    destruct Hsen1 as [H100 Hsen1].
    destruct Hsen2 as [H200 Hsen2].
    clear H100 H200.
    pose proof Hsen1 s1 ss1 ss11 as Hsen1.
    pose proof Hsen2 s1 ss12 ss13 as Hsen2.
    revert H3.
    simpl.
    sets_unfold.
    intros.
    destruct H3.
    - destruct H3.
      ++ destruct H3; [tauto|].
      unfold deref_sem_err in H3.
      destruct H3.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname vcnt).
      pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
      pose proof Hsen2 x2 Hcm2 H5 H8.
      sets_unfold in H4.
      destruct H4.
      destruct H4.
      rewrite H17 in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold var_sem_l, EDenote.nrm in H4.
      destruct H18.
      destruct H19.
      destruct H20.
      destruct H21.
      pose proof Hsen1 x5 H1 H2 H18.
      destruct H16, H23.
      * pose proof H21 (nat2Sname vcnt).
        rewrite H24 in H4.
        rewrite <- H14 in H3.
        rewrite H3 in H15.
        rewrite H4 in H15.
        rewrite H15 in H20.
        pose proof H11 (nat2Sname (S vcnt)).
        pose proof classic (ss13.(env) (nat2Sname (S vcnt)) = ss13.(env) (nat2Sname vcnt)).
        destruct H26.
        -- rewrite H26 in H6.
          rewrite H3 in H6.
          rewrite H6 in H13.
          rewrite H10 in H13.
          destruct H13; discriminate.
        -- pose proof H12 x.
           rewrite H6 in H26.
           rewrite H3 in H26.
           pose proof H27 H26.
           rewrite H28 in H20.
           rewrite H20 in H13.
           destruct H13; discriminate.
        * tauto.
        * tauto.
        * tauto.
    ++ destruct H3; [tauto|].
      unfold deref_sem_err in H3.
      destruct H3.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname vcnt).
      pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
      pose proof Hsen2 x2 Hcm2 H5 H8.
      sets_unfold in H4.
      destruct H4.
      destruct H4.
      rewrite H17 in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold var_sem_l, EDenote.nrm in H4.
      destruct H18.
      destruct H19.
      destruct H20.
      destruct H21.
      pose proof Hsen1 x5 H1 H2 H18.
      destruct H16, H23.
      * pose proof H21 (nat2Sname vcnt).
        pose proof H11 (nat2Sname (S vcnt)).
        rewrite H25 in H6.
        rewrite H3 in H6.
        rewrite H6 in H13.
        rewrite H10 in H13.
        destruct H13; discriminate.
      * tauto.
      * tauto.
      * tauto.
    - destruct H3.
      destruct H3.
      destruct H3 as [H3 H50].
      destruct H3.
      destruct H50 as [H50 H51].
      destruct H50 as [x2 H52].
      unfold arith_sem1_err.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname vcnt).
      pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
      pose proof Hsen2 x5 Hcm2 H5 H8.
      sets_unfold in H4.
      destruct H4.
      destruct H4.
      rewrite H17 in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold var_sem_l, EDenote.nrm in H4.
      destruct H18.
      destruct H19.
      destruct H20.
      destruct H21.
      pose proof Hsen1 x8 H1 H2 H18.
      destruct H16, H23.
      * right.
        exists x8,x5.
        split; [tauto|].
        split; [tauto|].
        pose proof H21 (nat2Sname vcnt).
        rewrite H24 in H4.
        rewrite H4 in H15.
        rewrite H15 in H20.
        pose proof classic (ss13.(env) (nat2Sname (S vcnt)) = ss13.(env) (nat2Sname vcnt)).
        destruct H25.
        -- pose proof trans_prop2 (S vcnt) vcnt ss13.
           destruct H26.
           pose proof H27 H25.
           lia.
        -- pose proof H12 x1.
           rewrite H6 in H25.
           rewrite H3 in H14.
           rewrite H14 in H25.
           pose proof H26 H25.
           rewrite H13 in H27.
           rewrite H14 in H20.
           rewrite H20 in H27.
           pose proof some_val x8 x.
           destruct H28.
           pose proof H28 H27.
           rewrite H30.
           destruct H52.
           pose proof H11 (nat2Sname (S vcnt)).
           rewrite H31 in H33.
           rewrite H6 in H33.
           rewrite H33 in H10.
           rewrite H10 in H32.
           pose proof some_val x5 x0.
           destruct H34.
           pose proof H34 H32.
           rewrite H36.
           tauto.
      * tauto.
      * tauto.
      * tauto.
      + clear H1.
      revert H H0.
      unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
      intros H H0 s1 ss1 ss2 H1 H2 H3.
      pose proof H (S vcnt) as H.
      destruct H as [IH1 [IH2 IH3]].
      pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
      sets_unfold in Hp.
      pose proof correspond_prop1 as Hc1.
      pose proof correspond_prop2 as Hc2.
      pose proof Split_Serefine_nrm e1 as Hsen1.
      pose proof Split_Serefine_nrm e2 as Hsen2.
      unfold Serefine_nrm, Serefine_nrm_r in Hsen1, Hsen2.
      simpl in H2.
      assert (
        (Seval_comlist  
        (ex2pre e1 (S (S vcnt)) ++
          [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
          (ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) ++
          [SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1 ss2).
        {
          simpl.
          tauto.
        }
        clear H2.
        pose proof midstate_binop vcnt e1 e2 ss1 ss2 H.
        destruct H2 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
        pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H2 as Hcm1.
        pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 Hcm1 H4 as Hcm2.
        pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 Hcm2 H5 as Hcm3.
        clear Hc1 Hc2.
        pose proof Hsen1 (S (S vcnt)) as Hsen1.
        pose proof Hsen2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) as Hsen2.
        destruct Hsen1 as [H100 Hsen1].
        destruct Hsen2 as [H200 Hsen2].
        clear H100 H200.
        pose proof Hsen1 s1 ss1 ss11 as Hsen1.
        pose proof Hsen2 s1 ss12 ss13 as Hsen2.
        revert H3.
        simpl.
        sets_unfold.
        intros.
        destruct H3.
        - destruct H3.
          ++ destruct H3; [tauto|].
          unfold deref_sem_err in H3.
          destruct H3.
          unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
          asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
          sets_unfold in H6.
          destruct H6.
          destruct H6.
          rewrite H7 in H6.
          destruct H6.
          destruct H6.
          destruct H6.
          unfold var_sem_l, EDenote.nrm in H6.
          destruct H8.
          destruct H9.
          destruct H10.
          destruct H11.
          destruct H3.
          pose proof H11 (nat2Sname vcnt).
          pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
          pose proof Hsen2 x2 Hcm2 H5 H8.
          sets_unfold in H4.
          destruct H4.
          destruct H4.
          rewrite H17 in H4.
          destruct H4.
          destruct H4.
          destruct H4.
          unfold var_sem_l, EDenote.nrm in H4.
          destruct H18.
          destruct H19.
          destruct H20.
          destruct H21.
          pose proof Hsen1 x5 H1 H2 H18.
          destruct H16, H23.
          * pose proof H21 (nat2Sname vcnt).
            rewrite H24 in H4.
            rewrite <- H14 in H3.
            rewrite H3 in H15.
            rewrite H4 in H15.
            rewrite H15 in H20.
            pose proof H11 (nat2Sname (S vcnt)).
            pose proof classic (ss13.(env) (nat2Sname (S vcnt)) = ss13.(env) (nat2Sname vcnt)).
            destruct H26.
            -- rewrite H26 in H6.
              rewrite H3 in H6.
              rewrite H6 in H13.
              rewrite H10 in H13.
              destruct H13; discriminate.
            -- pose proof H12 x.
               rewrite H6 in H26.
               rewrite H3 in H26.
               pose proof H27 H26.
               rewrite H28 in H20.
               rewrite H20 in H13.
               destruct H13; discriminate.
            * tauto.
            * tauto.
            * tauto.
        ++ destruct H3; [tauto|].
          unfold deref_sem_err in H3.
          destruct H3.
          unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
          asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
          sets_unfold in H6.
          destruct H6.
          destruct H6.
          rewrite H7 in H6.
          destruct H6.
          destruct H6.
          destruct H6.
          unfold var_sem_l, EDenote.nrm in H6.
          destruct H8.
          destruct H9.
          destruct H10.
          destruct H11.
          destruct H3.
          pose proof H11 (nat2Sname vcnt).
          pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
          pose proof Hsen2 x2 Hcm2 H5 H8.
          sets_unfold in H4.
          destruct H4.
          destruct H4.
          rewrite H17 in H4.
          destruct H4.
          destruct H4.
          destruct H4.
          unfold var_sem_l, EDenote.nrm in H4.
          destruct H18.
          destruct H19.
          destruct H20.
          destruct H21.
          pose proof Hsen1 x5 H1 H2 H18.
          destruct H16, H23.
          * pose proof H21 (nat2Sname vcnt).
            pose proof H11 (nat2Sname (S vcnt)).
            rewrite H25 in H6.
            rewrite H3 in H6.
            rewrite H6 in H13.
            rewrite H10 in H13.
            destruct H13; discriminate.
          * tauto.
          * tauto.
          * tauto.
        - destruct H3.
          destruct H3.
          destruct H3 as [H3 H50].
          destruct H3.
          destruct H50 as [H50 H51].
          destruct H50 as [x2 H52].
          unfold arith_sem1_err.
          unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
          asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
          sets_unfold in H6.
          destruct H6.
          destruct H6.
          rewrite H7 in H6.
          destruct H6.
          destruct H6.
          destruct H6.
          unfold var_sem_l, EDenote.nrm in H6.
          destruct H8.
          destruct H9.
          destruct H10.
          destruct H11.
          destruct H3.
          pose proof H11 (nat2Sname vcnt).
          pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
          pose proof Hsen2 x5 Hcm2 H5 H8.
          sets_unfold in H4.
          destruct H4.
          destruct H4.
          rewrite H17 in H4.
          destruct H4.
          destruct H4.
          destruct H4.
          unfold var_sem_l, EDenote.nrm in H4.
          destruct H18.
          destruct H19.
          destruct H20.
          destruct H21.
          pose proof Hsen1 x8 H1 H2 H18.
          destruct H16, H23.
          * right.
            exists x8,x5.
            split; [tauto|].
            split; [tauto|].
            pose proof H21 (nat2Sname vcnt).
            rewrite H24 in H4.
            rewrite H4 in H15.
            rewrite H15 in H20.
            pose proof classic (ss13.(env) (nat2Sname (S vcnt)) = ss13.(env) (nat2Sname vcnt)).
            destruct H25.
            -- pose proof trans_prop2 (S vcnt) vcnt ss13.
               destruct H26.
               pose proof H27 H25.
               lia.
            -- pose proof H12 x1.
               rewrite H6 in H25.
               rewrite H3 in H14.
               rewrite H14 in H25.
               pose proof H26 H25.
               rewrite H13 in H27.
               rewrite H14 in H20.
               rewrite H20 in H27.
               pose proof some_val x8 x.
               destruct H28.
               pose proof H28 H27.
               rewrite H30.
               destruct H52.
               pose proof H11 (nat2Sname (S vcnt)).
               rewrite H31 in H33.
               rewrite H6 in H33.
               rewrite H33 in H10.
               rewrite H10 in H32.
               pose proof some_val x5 x0.
               destruct H34.
               pose proof H34 H32.
               rewrite H36.
               tauto.
          * tauto.
          * tauto.
          * tauto.
+ clear H1.
revert H H0.
unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
intros H H0 s1 ss1 ss2 H1 H2 H3.
pose proof H (S vcnt) as H.
destruct H as [IH1 [IH2 IH3]].
pose proof asgn_vcnt_ex2se_nrm_prop as Hp.
sets_unfold in Hp.
pose proof correspond_prop1 as Hc1.
pose proof correspond_prop2 as Hc2.
pose proof Split_Serefine_nrm e1 as Hsen1.
pose proof Split_Serefine_nrm e2 as Hsen2.
unfold Serefine_nrm, Serefine_nrm_r in Hsen1, Hsen2.
simpl in H2.
assert (
    (Seval_comlist  
    (ex2pre e1 (S (S vcnt)) ++
      [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      (ex2pre e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt)))))))) ++
      [SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))))])).(nrm) ss1 ss2).
    {
      simpl.
      tauto.
    }
    clear H2.
    pose proof midstate_binop vcnt e1 e2 ss1 ss2 H.
    destruct H2 as [ss11 [ss12 [ss13 [? [? [? ?]]]]]].
    pose proof Hc2 e1 (S (S vcnt)) s1 ss1 ss11 H1 H2 as Hcm1.
    pose proof Hc1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 Hcm1 H4 as Hcm2.
    pose proof Hc2 e2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) s1 ss12 ss13 Hcm2 H5 as Hcm3.
    clear Hc1 Hc2.
    pose proof Hsen1 (S (S vcnt)) as Hsen1.
    pose proof Hsen2 (S (S (nat_add vcnt (length (ex2pre e1 (S (S vcnt))))))) as Hsen2.
    destruct Hsen1 as [H100 Hsen1].
    destruct Hsen2 as [H200 Hsen2].
    clear H100 H200.
    pose proof Hsen1 s1 ss1 ss11 as Hsen1.
    pose proof Hsen2 s1 ss12 ss13 as Hsen2.
    revert H3.
    simpl.
    sets_unfold.
    intros.
    destruct H3.
    - destruct H3.
      ++ destruct H3; [tauto|].
      unfold deref_sem_err in H3.
      destruct H3.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname vcnt).
      pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
      pose proof Hsen2 x2 Hcm2 H5 H8.
      sets_unfold in H4.
      destruct H4.
      destruct H4.
      rewrite H17 in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold var_sem_l, EDenote.nrm in H4.
      destruct H18.
      destruct H19.
      destruct H20.
      destruct H21.
      pose proof Hsen1 x5 H1 H2 H18.
      destruct H16, H23.
      * pose proof H21 (nat2Sname vcnt).
        rewrite H24 in H4.
        rewrite <- H14 in H3.
        rewrite H3 in H15.
        rewrite H4 in H15.
        rewrite H15 in H20.
        pose proof H11 (nat2Sname (S vcnt)).
        pose proof classic (ss13.(env) (nat2Sname (S vcnt)) = ss13.(env) (nat2Sname vcnt)).
        destruct H26.
        -- rewrite H26 in H6.
          rewrite H3 in H6.
          rewrite H6 in H13.
          rewrite H10 in H13.
          destruct H13; discriminate.
        -- pose proof H12 x.
           rewrite H6 in H26.
           rewrite H3 in H26.
           pose proof H27 H26.
           rewrite H28 in H20.
           rewrite H20 in H13.
           destruct H13; discriminate.
        * tauto.
        * tauto.
        * tauto.
    ++ destruct H3; [tauto|].
      unfold deref_sem_err in H3.
      destruct H3.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname vcnt).
      pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
      pose proof Hsen2 x2 Hcm2 H5 H8.
      sets_unfold in H4.
      destruct H4.
      destruct H4.
      rewrite H17 in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold var_sem_l, EDenote.nrm in H4.
      destruct H18.
      destruct H19.
      destruct H20.
      destruct H21.
      pose proof Hsen1 x5 H1 H2 H18.
      destruct H16, H23.
      * pose proof H21 (nat2Sname vcnt).
        pose proof H11 (nat2Sname (S vcnt)).
        rewrite H25 in H6.
        rewrite H3 in H6.
        rewrite H6 in H13.
        rewrite H10 in H13.
        destruct H13; discriminate.
      * tauto.
      * tauto.
      * tauto.
    - destruct H3.
      destruct H3.
      destruct H3 as [H3 H50].
      destruct H3.
      destruct H50 as [H50 H51].
      destruct H50 as [x2 H52].
      unfold arith_sem1_err.
      unfold Seval_comlist, seq_sem, asgn_var_sem, skip_sem, CDenote.nrm, CDenote.err,
      asgn_deref_sem, asgn_deref_sem_nrm in H6, H4.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite H7 in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold var_sem_l, EDenote.nrm in H6.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H3.
      pose proof H11 (nat2Sname vcnt).
      pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H5.
      pose proof Hsen2 x5 Hcm2 H5 H8.
      sets_unfold in H4.
      destruct H4.
      destruct H4.
      rewrite H17 in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold var_sem_l, EDenote.nrm in H4.
      destruct H18.
      destruct H19.
      destruct H20.
      destruct H21.
      pose proof Hsen1 x8 H1 H2 H18.
      destruct H16, H23.
      * right.
        exists x8,x5.
        split; [tauto|].
        split; [tauto|].
        pose proof H21 (nat2Sname vcnt).
        rewrite H24 in H4.
        rewrite H4 in H15.
        rewrite H15 in H20.
        pose proof classic (ss13.(env) (nat2Sname (S vcnt)) = ss13.(env) (nat2Sname vcnt)).
        destruct H25.
        -- pose proof trans_prop2 (S vcnt) vcnt ss13.
           destruct H26.
           pose proof H27 H25.
           lia.
        -- pose proof H12 x1.
           rewrite H6 in H25.
           rewrite H3 in H14.
           rewrite H14 in H25.
           pose proof H26 H25.
           rewrite H13 in H27.
           rewrite H14 in H20.
           rewrite H20 in H27.
           pose proof some_val x8 x.
           destruct H28.
           pose proof H28 H27.
           rewrite H30.
           destruct H52.
           pose proof H11 (nat2Sname (S vcnt)).
           rewrite H31 in H33.
           rewrite H6 in H33.
           rewrite H33 in H10.
           rewrite H10 in H32.
           pose proof some_val x5 x0.
           destruct H34.
           pose proof H34 H32.
           rewrite H36.
           tauto.
      * tauto.
      * tauto.
      * tauto.
Qed.

Lemma Split_Serefine_err {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr) (vcnt : nat), 
    Serefine_err (ex2pre e vcnt) (ex2se e vcnt) e.
Proof.
    induction e.
    + unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
      simpl. 
      sets_unfold. 
      tauto.
    + unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
      simpl.
      sets_unfold.
      split; [tauto|].
      split; [tauto|].
      intros.
      destruct H1.
        - tauto.
        - right.
          rewrite <- H0 in H1.
          revert H1.
          unfold deref_sem_err.
          intros.
          destruct H1.
          destruct H1.
          exists x0.
          unfold correspond in H.
          destruct H.
          pose proof H x x0 as H.
          destruct H.
          pose proof H4 H1.
          split;[tauto|].
          pose proof mem_split s1 x0.
          destruct H6.
          * destruct H6 as [v].
            right.
            destruct H3.
            pose proof H3 x0 v H6.
            destruct H2.
            -- congruence.
            -- rewrite H8 in H2.
               rewrite H2 in H6.   
               tauto. 
          * tauto.
    + revert IHe1 IHe2.
      intros.
      unfold Serefine_err.
      pose proof Split_Serefine_err1_binop op e1 e2 IHe1 IHe2 vcnt.
      pose proof Split_Serefine_err2_l_binop op e1 e2 IHe1 IHe2 vcnt.
      pose proof Split_Serefine_err2_r_binop op e1 e2 IHe1 IHe2 vcnt.
      tauto.
    + revert IHe.
      intros.
      unfold Serefine_err.
      pose proof Split_Serefine_err1_unop e IHe vcnt op.
      pose proof Split_Serefine_err2_l_unop e IHe vcnt op.
      pose proof Split_Serefine_err2_r_unop e IHe vcnt op.
      tauto.
    + revert IHe.
      intros.
      unfold Serefine_err.
      pose proof Split_Serefine_err1_deref e IHe vcnt.
      pose proof Split_Serefine_err2_l_deref e IHe vcnt.
      pose proof Split_Serefine_err2_r_deref e IHe vcnt.
      tauto.
    + revert IHe.
      intros.
      unfold Serefine_err.
      pose proof Split_Serefine_err1_addrof e IHe vcnt.
      pose proof Split_Serefine_err2_l_addrof e IHe vcnt.
      pose proof Split_Serefine_err2_r_addrof e IHe vcnt.
      tauto.
Qed.

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
    forall (s1 ss1 ss2: state),
        (Seval_comlist cl).(nrm) ss1 ss2 ->
        correspond s1 ss1 ->
        ((exists (s2 : state), (eval_com c).(nrm) s1 s2 /\ correspond s2 ss2)
        \/ (eval_com c).(err) s1).

Definition Screfine_err {NameX : Names} (cl : Scomlist) (c : com): Prop :=
    forall (s1 ss1 : state),
        (Seval_comlist cl).(err) ss1 ->
        correspond s1 ss1 ->
        (eval_com c).(err) s1.

Definition Screfine_inf {NameX : Names} (cl : Scomlist) (c : com): Prop :=
    forall (s1 ss1 : state),
        (Seval_comlist cl).(inf) ss1 ->
        correspond s1 ss1 ->
        (eval_com c).(inf) s1
            \/ (eval_com c).(err) s1.

Record Screfine {NameX : Names} (cl : Scomlist) (c : com): Prop := {
    nrm_crefine:
        Screfine_nrm cl c;
    err_crefine:
        Screfine_err cl c;
    inf_crefine:
        Screfine_inf cl c;
}.

Lemma Split_crefine_nrm_Skip {NameX : Names} {NPX : NamesProperty}: 
    forall (vcnt : nat),
        Screfine_nrm (com2comlist CSkip vcnt) CSkip.
Proof.
    unfold Screfine_nrm.
    simpl.
    sets_unfold.
    intros.
    left.
    exists s1.
    split.
    reflexivity.
    rewrite <- H.
    tauto.
Qed.

Lemma Split_crefine_err_Skip {NameX : Names} {NPX : NamesProperty}: 
    forall (vcnt : nat),
        Screfine_err (com2comlist CSkip vcnt) CSkip.
Proof.
    unfold Screfine_err.
    simpl.
    sets_unfold.
    tauto.
Qed.

Lemma Split_crefine_inf_Skip {NameX : Names} {NPX : NamesProperty}: 
    forall (vcnt : nat),
        Screfine_inf (com2comlist CSkip vcnt) CSkip.
Proof.
    unfold Screfine_inf.
    simpl.
    sets_unfold.
    tauto.
Qed.


Definition midstate_asgnvar {NameX : Names}
    (vcnt : nat) (x : var_name) (e : expr) : Prop :=
    forall (ss1 ss3 : state),
    (Seval_comlist (com2comlist (CAsgnVar x e) vcnt)).(nrm) ss1 ss3
    -> exists (ss2 : state),
    (Seval_comlist (ex2pre e vcnt)).(nrm) ss1 ss2
    /\ (Seval_comlist [SCAsgnVar (name2Sname x) (ex2se e vcnt)]).(nrm) ss2 ss3.


Lemma midstate_asgnvar_correct {NameX : Names}: 
    forall (vcnt : nat) (x : var_name) (e : expr),
    midstate_asgnvar vcnt x e.
Proof.
    unfold midstate_asgnvar.
    intros.
    pose proof eval_comlist_seq_nrm (ex2pre e vcnt) [SCAsgnVar (name2Sname x) (ex2se e vcnt)] ss1 ss3 as Hm.
    destruct Hm.
    pose proof H0 H.
    sets_unfold in H2.
    destruct H2.
    exists x0.
    tauto.
Qed.

Definition construct_state (s : state) (i a : int64) : state :=
    {|
        env:= s.(env);
        mem:= fun (m : int64) =>
            match (Int64.eq i m) with
            | true => Some (Vint a)
            | false => s.(mem) m
            end;
    |}.

Lemma construct_asgnvar_sound: forall (s : state) (x : var_name) (e : expr) (i a : int64),
    s.(env) x = i -> 
    s.(mem) i <> None ->
    (eval_r e).(nrm) s a ->
    (eval_com (CAsgnVar x e)).(nrm) s (construct_state s i a).
Proof.
    intros.
    simpl.
    unfold asgn_deref_sem_nrm.
    exists i, a.
    split.
    tauto.
    split.
    tauto.
    split.
    tauto.
    unfold construct_state.
    simpl.
    split.
    pose proof Int64.eq_true i.
    rewrite H2.
    tauto.
    split.
    intros.
    tauto.
    intros.
    pose proof Int64.eq_false i p H2.
    rewrite H3.
    tauto.
Qed.

Lemma Split_crefine_nrm_AsgnVar_aux {NameX : Names} {NPX : NamesProperty}:
    forall (vcnt : nat) (x : var_name) (e : expr),
    forall (s1 ss1 ss2 ss3 : state),
    (Seval_comlist (ex2pre e vcnt)).(nrm) ss1 ss2
    -> (Seval_comlist [SCAsgnVar (name2Sname x) (ex2se e vcnt)]).(nrm) ss2 ss3
    -> correspond s1 ss1 
    -> correspond s1 ss2
    -> ((exists (s2 : state), (eval_com (CAsgnVar x e)).(nrm) s1 s2 /\ correspond s2 ss3)
        \/ (eval_com (CAsgnVar x e)).(err) s1).
Proof.
    intros.
    pose proof Split_Serefine_nrm e vcnt as Hse.
    unfold Serefine_nrm in Hse.
    destruct Hse as [H100 Hse].   
    unfold Serefine_nrm_r in Hse.
    revert H0 H1 H2.
    simpl.
    sets_unfold.
    intros.
    pose proof H1 as H51.
    pose proof H2 as H52.
    unfold asgn_deref_sem_nrm in H0.
    destruct H0.
    destruct H0.
    rewrite H3 in H0.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H4.
    destruct H5.
    destruct H6.
    destruct H7.
    destruct H1.
    destruct H9.
    destruct H2.
    destruct H11.
    pose proof Hse s1 ss1 ss2 x2 H51 H H4.
    destruct H13.
    + pose proof mem_split s1 x1.
      destruct H14.
      - destruct H14.
        left.
        exists (construct_state s1 x1 x2).
        pose proof H2 x x1.
        destruct H15.
        pose proof H16 H0.
        assert (s1.(mem) x1 <> None).
        {
            rewrite H14.
            discriminate.
        }
        pose proof construct_asgnvar_sound s1 x e x1 x2 H17 H18 H13.
        split.
        revert H19.
        simpl.
        tauto.
        unfold correspond, construct_state.
        simpl.
        split.
        split; intros.
        pose proof H2 x4 i.
        destruct H21.
        pose proof H21 H20.
        pose proof H7 (name2Sname x4).
        rewrite <- H24.
        tauto.
        pose proof H7 (name2Sname x4).
        destruct H21.
        pose proof H2 x4 i.
        destruct H21.
        pose proof H22 H20.
        tauto.
        split.
        intros.
        pose proof classic (x1 = a).
        destruct H21.
        rewrite H21 in H20.
        pose proof Int64.eq_true a.
        rewrite H22 in H20.
        rewrite H21 in H6.
        rewrite H6.
        tauto.
        pose proof Int64.eq_false x1 a H21.
        rewrite H22 in H20.
        pose proof H11 a v H20.
        pose proof H8 a H21.
        rewrite <- H24.
        tauto.
        intros.
        pose proof classic (x1 = ss3.(env) (nat2Sname vcnt0)).
        pose proof H7 (nat2Sname vcnt0).
        destruct H20.
        pose proof H12 vcnt0.
        rewrite H21 in H22.
        rewrite <- H20 in H22.
        destruct H22.
        rewrite H22 in H14.
        discriminate.
        pose proof Int64.eq_false x1 (ss3.(env) (nat2Sname vcnt0)) H20.
        rewrite H22.
        pose proof H12 vcnt0.
        destruct H23.
        rewrite H21 in H23.
        pose proof H8 (ss3.(env) (nat2Sname vcnt0)) H20.
        rewrite <- H25.
        rewrite H21 in H24.
        tauto. 
      - right.
        right.
        unfold asgn_deref_sem_err.
        exists x1.
        pose proof H2 x x1.
        destruct H15.
        pose proof H16 H0.
        tauto.
    + right.
      left.
      tauto.
Qed.

Lemma Split_crefine_nrm_AsgnVar {NameX : Names} {NPX : NamesProperty}:
    forall (vcnt : nat) (x : var_name) (e : expr),
    forall (s1 ss1 ss3 : state),
    (Seval_comlist (com2comlist (CAsgnVar x e) vcnt)).(nrm) ss1 ss3
    -> correspond s1 ss1 
    -> ((exists (s2 : state), (eval_com (CAsgnVar x e)).(nrm) s1 s2 /\ correspond s2 ss3)
        \/ (eval_com (CAsgnVar x e)).(err) s1).
Proof.
    intros vcnt x e s1 ss1 ss3.
    unfold com2comlist.
    intros.
    pose proof eval_comlist_seq_nrm (com2pre (CAsgnVar x e) vcnt) (com2sc (CAsgnVar x e) vcnt) ss1 ss3.
    destruct H1.
    pose proof H1 H.
    sets_unfold in H3.
    destruct H3 as [ss2].
    destruct H3.
    pose proof correspond_prop3_asgnvar x e vcnt s1 ss1 ss2 H0 H3.
    pose proof asgn_pre x e vcnt.
    pose proof asgn_sc x e vcnt.
    rewrite H6 in H3.
    rewrite H7 in H4.
    pose proof Split_crefine_nrm_AsgnVar_aux vcnt x e s1 ss1 ss2 ss3 H3 H4 H0 H5.
    tauto.
Qed.

Lemma Split_crefine_err_AsgnVar {NameX : Names} {NPX : NamesProperty}:
    forall (vcnt : nat) (x : var_name) (e : expr),
    forall (s1 ss1 : state),
    (Seval_comlist (com2comlist (CAsgnVar x e) vcnt)).(err) ss1
    -> correspond s1 ss1 
    -> (eval_com (CAsgnVar x e)).(err) s1.
Proof.
    intros vcnt x e s1 ss1.
    unfold com2comlist.
    intros.
    pose proof eval_comlist_seq_err (com2pre (CAsgnVar x e) vcnt) (com2sc (CAsgnVar x e) vcnt) ss1.
    destruct H1.
    pose proof H1 H.
    sets_unfold in H3.
    pose proof asgn_pre x e vcnt.
    pose proof asgn_sc x e vcnt.
    rewrite H4 in H3.
    rewrite H5 in H3.
    pose proof Split_Serefine_err e vcnt.
    unfold Serefine_err in H6.
    destruct H6 as [H6 [H7 H8]].
    destruct H3.
    + unfold Serefine_err1 in H6.
      pose proof H6 s1 ss1 H0 H3.
      destruct H9.
      simpl.
      sets_unfold.
      left.
      tauto.
    + destruct H3 as [ss2].
      destruct H3.
      pose proof correspond_prop2 e vcnt s1 ss1 ss2 H0 H3 as Hc2.
      unfold Serefine_err2_r in H8.
      revert H9.
      simpl.
      sets_unfold.
      intros.
      destruct H9.
      destruct H9.
      destruct H9.
      tauto.
      pose proof H8 s1 ss1 ss2 H0 H3 H9.
      left.
      tauto.
      revert H9.
      unfold asgn_deref_sem_err.
      intros.
      destruct H9.
      destruct H9.
      unfold correspond in Hc2.
      destruct Hc2 as [H11 [H12 H13]].
      pose proof H11 x x0.
      destruct H14.
      pose proof H15 H9.
      pose proof mem_split s1 x0.
      destruct H17.
      destruct H17 as [v].
      pose proof H12 x0 v H17.
      rewrite H10 in H18.
      discriminate.
      right.
      exists x0.
      tauto.
      destruct H9.
      destruct H9.
      tauto.
Qed.



Lemma never_inf_asgn {NameX : Names}: 
    forall (vcnt : nat) (se : Sexpr) (s : state),
        (Seval_comlist [SCAsgnVar (nat2Sname vcnt) se]).(inf) s
        -> False.
Proof.
    intros vcnt se s.
    simpl.
    sets_unfold.
    intros.
    destruct H; [tauto|].
    destruct H.
    destruct H.
    tauto.
Qed.

Lemma never_inf_binop {NameX : Names}: forall (op : binop) (e1 e2 : expr) (vcnt : nat) (s : state),
    (forall (vcnt : nat) (s : state), (Seval_comlist (ex2pre e1 vcnt)).(inf) s -> False) ->
    (forall (vcnt : nat) (s : state), (Seval_comlist (ex2pre e2 vcnt)).(inf) s -> False) ->
    (Seval_comlist (ex2pre (EBinop op e1 e2) vcnt)).(inf) s -> False.
Proof.
  intros.
  pose proof ex2pre_binop vcnt e1 e2 op.
  destruct op; rewrite H2 in H1.
  + pose proof eval_comlist_seq_inf
      (ex2pre e1 (S (S vcnt)))
         ([SCAsgnVar (nat2Sname (S vcnt)) (ex2se e1 (S (S vcnt)))] ++
         [SCIf (genSECV (S vcnt))
            [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1))]
            (ex2pre e2
               (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))) ++
             [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2
                   (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))] ++
             [SCIf (genSECV (S vcnt))
                [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1))]
                [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0))]])]) s.
    destruct H3.
    pose proof H3 H1.
    destruct H5.
    ++
    pose proof H (S (S vcnt)) s H5.
    tauto.
    ++
    sets_unfold in H5.
    destruct H5 as [s1].
    destruct H5.
    pose proof eval_comlist_seq_inf 
       [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e1 (S (S vcnt)))]
         [SCIf (genSECV (S vcnt))
            [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 1))]
            (ex2pre e2
               (nat_add (S (S vcnt))
                  (length (ex2pre e1 (S (S vcnt))))) ++
             [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2
                   (nat_add (S (S vcnt))
                      (length (ex2pre e1 (S (S vcnt))))))] ++
             [SCIf (genSECV (S vcnt))
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 1))]
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 0))]])] s1.
    destruct H7.
    pose proof H7 H6.
    destruct H9.
    +++
    pose proof never_inf_asgn (S vcnt) (ex2se e1 (S (S vcnt))) s1 H9.
    tauto.
    +++
    sets_unfold in H9.
    destruct H9 as [s2].
    destruct H9.
    simpl in H10.
    sets_unfold in H10.
    destruct H10.
    ++++
    destruct H10.
    -
    destruct H10.
    destruct H10.
    destruct H11; [tauto|].
    destruct H11.
    tauto.
    -
    destruct H10.
    destruct H10.
    unfold test_false in H10.
    sets_unfold in H10.
    destruct H10.
    rewrite <- H12 in H11.
    pose proof eval_comlist_seq_inf 
      (ex2pre e2
            (S
               (S
                  (nat_add vcnt
                     (length (ex2pre e1 (S (S vcnt))))))))
          ([SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2
                (S
                   (S
                      (nat_add vcnt
                         (length (ex2pre e1 (S (S vcnt)))))))),
          SCIf (genSECV (S vcnt))
            [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 1))]
            [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 0))]]) s2.
    destruct H13.
    pose proof H13 H11.
    destruct H15.
    --
    pose proof H0 (S
    (S
       (nat_add vcnt
          (length (ex2pre e1 (S (S vcnt))))))) s2 H15.
    tauto.
    --
    sets_unfold in H15.
    destruct H15 as [s3].
    destruct H15.
    pose proof eval_comlist_seq_inf
      [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2
               (S
                  (S
                     (nat_add vcnt
                        (length (ex2pre e1 (S (S vcnt))))))))]
         [SCIf (genSECV (S vcnt))
           [SCAsgnVar (nat2Sname vcnt)
              (SEConstOrVar (SEConst 1))]
           [SCAsgnVar (nat2Sname vcnt)
              (SEConstOrVar (SEConst 0))]] s3.
    destruct H17.
    pose proof H17 H16.
    destruct H19.
    ---
    pose proof never_inf_asgn (S vcnt) (ex2se e2
    (S
       (S
          (nat_add vcnt
             (length (ex2pre e1 (S (S vcnt)))))))) s3 H19.
    tauto.
    ---
    sets_unfold in H19.
    destruct H19 as [s4].
    destruct H19.
    simpl in H20.
    sets_unfold in H20.
    destruct H20.
    ----
    destruct H20.
    *
    destruct H20.
    destruct H20.
    destruct H21; [tauto|].
    destruct H21; tauto.
    *
    destruct H20.
    destruct H20.
    destruct H21; [tauto|].
    destruct H21; tauto.
    ----
    destruct H20.
    destruct H20.
    tauto.
    ++++
    destruct H10.
    destruct H10.
    tauto.
  + pose proof eval_comlist_seq_inf
      (ex2pre e1 (S (S vcnt)))
         ([SCAsgnVar (nat2Sname (S vcnt)) (ex2se e1 (S (S vcnt)))] ++
         [SCIf (genSECV (S vcnt))
            (ex2pre e2
               (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))) ++
             [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2
                   (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))] ++
             [SCIf (genSECV (S vcnt))
                [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 1))]
                [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0))]])
            [SCAsgnVar (nat2Sname vcnt) (SEConstOrVar (SEConst 0))]]) s.
    destruct H3.
    pose proof H3 H1.
    destruct H5.
    ++
    pose proof H (S (S vcnt)) s H5.
    tauto.
    ++
    sets_unfold in H5.
    destruct H5 as [s1].
    destruct H5.
    pose proof eval_comlist_seq_inf 
       [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e1 (S (S vcnt)))]
         [SCIf (genSECV (S vcnt))
            (ex2pre e2
               (nat_add (S (S vcnt))
                  (length (ex2pre e1 (S (S vcnt))))) ++
             [SCAsgnVar (nat2Sname (S vcnt))
                (ex2se e2
                   (nat_add (S (S vcnt))
                      (length (ex2pre e1 (S (S vcnt))))))] ++
             [SCIf (genSECV (S vcnt))
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 1))]
                [SCAsgnVar (nat2Sname vcnt)
                   (SEConstOrVar (SEConst 0))]])
            [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 0))]] s1.
    destruct H7.
    pose proof H7 H6.
    destruct H9.
    +++
    pose proof never_inf_asgn (S vcnt) (ex2se e1 (S (S vcnt))) s1 H9.
    tauto.
    +++
    sets_unfold in H9.
    destruct H9 as [s2].
    destruct H9.
    simpl in H10.
    sets_unfold in H10.
    destruct H10.
    ++++
    destruct H10.
    -
    destruct H10.
    destruct H10.
    unfold test_false in H10.
    sets_unfold in H10.
    destruct H10.
    rewrite <- H12 in H11.
    pose proof eval_comlist_seq_inf 
      (ex2pre e2
            (S
               (S
                  (nat_add vcnt
                     (length (ex2pre e1 (S (S vcnt))))))))
          ([SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2
                (S
                   (S
                      (nat_add vcnt
                         (length (ex2pre e1 (S (S vcnt)))))))),
          SCIf (genSECV (S vcnt))
            [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 1))]
            [SCAsgnVar (nat2Sname vcnt)
               (SEConstOrVar (SEConst 0))]]) s2.
    destruct H13.
    pose proof H13 H11.
    destruct H15.
    --
    pose proof H0 (S
    (S
       (nat_add vcnt
          (length (ex2pre e1 (S (S vcnt))))))) s2 H15.
    tauto.
    --
    sets_unfold in H15.
    destruct H15 as [s3].
    destruct H15.
    pose proof eval_comlist_seq_inf
      [SCAsgnVar (nat2Sname (S vcnt))
            (ex2se e2
               (S
                  (S
                     (nat_add vcnt
                        (length (ex2pre e1 (S (S vcnt))))))))]
         [SCIf (genSECV (S vcnt))
           [SCAsgnVar (nat2Sname vcnt)
              (SEConstOrVar (SEConst 1))]
           [SCAsgnVar (nat2Sname vcnt)
              (SEConstOrVar (SEConst 0))]] s3.
    destruct H17.
    pose proof H17 H16.
    destruct H19.
    ---
    pose proof never_inf_asgn (S vcnt) (ex2se e2
    (S
       (S
          (nat_add vcnt
             (length (ex2pre e1 (S (S vcnt)))))))) s3 H19.
    tauto.
    ---
    sets_unfold in H19.
    destruct H19 as [s4].
    destruct H19.
    simpl in H20.
    sets_unfold in H20.
    destruct H20.
    ----
    destruct H20.
    *
    destruct H20.
    destruct H20.
    destruct H21; [tauto|].
    destruct H21; tauto.
    *
    destruct H20.
    destruct H20.
    destruct H21; [tauto|].
    destruct H21; tauto.
    ----
    destruct H20.
    destruct H20.
    tauto.
    -
    destruct H10.
    destruct H10.
    destruct H11; [tauto|].
    destruct H11.
    tauto.
    ++++
    destruct H10.
    destruct H10.
    tauto.
  + pose proof eval_comlist_seq_inf 
      (ex2pre e1 (S (S vcnt))) 
      ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s.
    destruct H3.
    pose proof H3 H1.
    destruct H5.
    -
    pose proof H (S (S vcnt)) s H5.
    tauto.
    -
    sets_unfold in H5.
    destruct H5 as [s1].
    destruct H5.
    pose proof eval_comlist_seq_inf 
    [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S(S vcnt)))] 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
    [SCAsgnVar (nat2Sname (S vcnt))
       (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s1.
    destruct H7.
    pose proof H7 H6.
    destruct H9.
    pose proof never_inf_asgn vcnt (ex2se e1 (S (S vcnt))) s1 H9.
    tauto.
    sets_unfold in H9.
    destruct H9 as [s2].
    destruct H9.
    pose proof eval_comlist_seq_inf 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))
    [SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))] s2.
    destruct H11.
    pose proof H11 H10.
    destruct H13.
    pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) s2 H13.
    tauto.
    sets_unfold in H13.
    destruct H13 as [s4].
    destruct H13.
    pose proof never_inf_asgn (S vcnt) 
      (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) s4 H14.
    tauto.
  + pose proof eval_comlist_seq_inf 
      (ex2pre e1 (S (S vcnt))) 
      ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s.
    destruct H3.
    pose proof H3 H1.
    destruct H5.
    -
    pose proof H (S (S vcnt)) s H5.
    tauto.
    -
    sets_unfold in H5.
    destruct H5 as [s1].
    destruct H5.
    pose proof eval_comlist_seq_inf 
    [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S(S vcnt)))] 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
    [SCAsgnVar (nat2Sname (S vcnt))
       (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s1.
    destruct H7.
    pose proof H7 H6.
    destruct H9.
    pose proof never_inf_asgn vcnt (ex2se e1 (S (S vcnt))) s1 H9.
    tauto.
    sets_unfold in H9.
    destruct H9 as [s2].
    destruct H9.
    pose proof eval_comlist_seq_inf 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))
    [SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))] s2.
    destruct H11.
    pose proof H11 H10.
    destruct H13.
    pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) s2 H13.
    tauto.
    sets_unfold in H13.
    destruct H13 as [s4].
    destruct H13.
    pose proof never_inf_asgn (S vcnt) 
      (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) s4 H14.
    tauto.
  + pose proof eval_comlist_seq_inf 
      (ex2pre e1 (S (S vcnt))) 
      ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s.
    destruct H3.
    pose proof H3 H1.
    destruct H5.
    -
    pose proof H (S (S vcnt)) s H5.
    tauto.
    -
    sets_unfold in H5.
    destruct H5 as [s1].
    destruct H5.
    pose proof eval_comlist_seq_inf 
    [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S(S vcnt)))] 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
    [SCAsgnVar (nat2Sname (S vcnt))
       (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s1.
    destruct H7.
    pose proof H7 H6.
    destruct H9.
    pose proof never_inf_asgn vcnt (ex2se e1 (S (S vcnt))) s1 H9.
    tauto.
    sets_unfold in H9.
    destruct H9 as [s2].
    destruct H9.
    pose proof eval_comlist_seq_inf 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))
    [SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))] s2.
    destruct H11.
    pose proof H11 H10.
    destruct H13.
    pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) s2 H13.
    tauto.
    sets_unfold in H13.
    destruct H13 as [s4].
    destruct H13.
    pose proof never_inf_asgn (S vcnt) 
      (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) s4 H14.
    tauto.
  + pose proof eval_comlist_seq_inf 
      (ex2pre e1 (S (S vcnt))) 
      ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s.
    destruct H3.
    pose proof H3 H1.
    destruct H5.
    -
    pose proof H (S (S vcnt)) s H5.
    tauto.
    -
    sets_unfold in H5.
    destruct H5 as [s1].
    destruct H5.
    pose proof eval_comlist_seq_inf 
    [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S(S vcnt)))] 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
    [SCAsgnVar (nat2Sname (S vcnt))
       (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s1.
    destruct H7.
    pose proof H7 H6.
    destruct H9.
    pose proof never_inf_asgn vcnt (ex2se e1 (S (S vcnt))) s1 H9.
    tauto.
    sets_unfold in H9.
    destruct H9 as [s2].
    destruct H9.
    pose proof eval_comlist_seq_inf 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))
    [SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))] s2.
    destruct H11.
    pose proof H11 H10.
    destruct H13.
    pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) s2 H13.
    tauto.
    sets_unfold in H13.
    destruct H13 as [s4].
    destruct H13.
    pose proof never_inf_asgn (S vcnt) 
      (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) s4 H14.
    tauto.
  + pose proof eval_comlist_seq_inf 
      (ex2pre e1 (S (S vcnt))) 
      ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s.
    destruct H3.
    pose proof H3 H1.
    destruct H5.
    -
    pose proof H (S (S vcnt)) s H5.
    tauto.
    -
    sets_unfold in H5.
    destruct H5 as [s1].
    destruct H5.
    pose proof eval_comlist_seq_inf 
    [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S(S vcnt)))] 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
    [SCAsgnVar (nat2Sname (S vcnt))
       (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s1.
    destruct H7.
    pose proof H7 H6.
    destruct H9.
    pose proof never_inf_asgn vcnt (ex2se e1 (S (S vcnt))) s1 H9.
    tauto.
    sets_unfold in H9.
    destruct H9 as [s2].
    destruct H9.
    pose proof eval_comlist_seq_inf 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))
    [SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))] s2.
    destruct H11.
    pose proof H11 H10.
    destruct H13.
    pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) s2 H13.
    tauto.
    sets_unfold in H13.
    destruct H13 as [s4].
    destruct H13.
    pose proof never_inf_asgn (S vcnt) 
      (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) s4 H14.
    tauto.
  + pose proof eval_comlist_seq_inf 
      (ex2pre e1 (S (S vcnt))) 
      ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s.
    destruct H3.
    pose proof H3 H1.
    destruct H5.
    -
    pose proof H (S (S vcnt)) s H5.
    tauto.
    -
    sets_unfold in H5.
    destruct H5 as [s1].
    destruct H5.
    pose proof eval_comlist_seq_inf 
    [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S(S vcnt)))] 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
    [SCAsgnVar (nat2Sname (S vcnt))
       (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s1.
    destruct H7.
    pose proof H7 H6.
    destruct H9.
    pose proof never_inf_asgn vcnt (ex2se e1 (S (S vcnt))) s1 H9.
    tauto.
    sets_unfold in H9.
    destruct H9 as [s2].
    destruct H9.
    pose proof eval_comlist_seq_inf 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))
    [SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))] s2.
    destruct H11.
    pose proof H11 H10.
    destruct H13.
    pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) s2 H13.
    tauto.
    sets_unfold in H13.
    destruct H13 as [s4].
    destruct H13.
    pose proof never_inf_asgn (S vcnt) 
      (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) s4 H14.
    tauto.
  + pose proof eval_comlist_seq_inf 
      (ex2pre e1 (S (S vcnt))) 
      ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s.
    destruct H3.
    pose proof H3 H1.
    destruct H5.
    -
    pose proof H (S (S vcnt)) s H5.
    tauto.
    -
    sets_unfold in H5.
    destruct H5 as [s1].
    destruct H5.
    pose proof eval_comlist_seq_inf 
    [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S(S vcnt)))] 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
    [SCAsgnVar (nat2Sname (S vcnt))
       (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s1.
    destruct H7.
    pose proof H7 H6.
    destruct H9.
    pose proof never_inf_asgn vcnt (ex2se e1 (S (S vcnt))) s1 H9.
    tauto.
    sets_unfold in H9.
    destruct H9 as [s2].
    destruct H9.
    pose proof eval_comlist_seq_inf 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))
    [SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))] s2.
    destruct H11.
    pose proof H11 H10.
    destruct H13.
    pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) s2 H13.
    tauto.
    sets_unfold in H13.
    destruct H13 as [s4].
    destruct H13.
    pose proof never_inf_asgn (S vcnt) 
      (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) s4 H14.
    tauto.
  + pose proof eval_comlist_seq_inf 
      (ex2pre e1 (S (S vcnt))) 
      ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s.
    destruct H3.
    pose proof H3 H1.
    destruct H5.
    -
    pose proof H (S (S vcnt)) s H5.
    tauto.
    -
    sets_unfold in H5.
    destruct H5 as [s1].
    destruct H5.
    pose proof eval_comlist_seq_inf 
    [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S(S vcnt)))] 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
    [SCAsgnVar (nat2Sname (S vcnt))
       (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s1.
    destruct H7.
    pose proof H7 H6.
    destruct H9.
    pose proof never_inf_asgn vcnt (ex2se e1 (S (S vcnt))) s1 H9.
    tauto.
    sets_unfold in H9.
    destruct H9 as [s2].
    destruct H9.
    pose proof eval_comlist_seq_inf 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))
    [SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))] s2.
    destruct H11.
    pose proof H11 H10.
    destruct H13.
    pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) s2 H13.
    tauto.
    sets_unfold in H13.
    destruct H13 as [s4].
    destruct H13.
    pose proof never_inf_asgn (S vcnt) 
      (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) s4 H14.
    tauto.
  + pose proof eval_comlist_seq_inf 
      (ex2pre e1 (S (S vcnt))) 
      ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s.
    destruct H3.
    pose proof H3 H1.
    destruct H5.
    -
    pose proof H (S (S vcnt)) s H5.
    tauto.
    -
    sets_unfold in H5.
    destruct H5 as [s1].
    destruct H5.
    pose proof eval_comlist_seq_inf 
    [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S(S vcnt)))] 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
    [SCAsgnVar (nat2Sname (S vcnt))
       (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s1.
    destruct H7.
    pose proof H7 H6.
    destruct H9.
    pose proof never_inf_asgn vcnt (ex2se e1 (S (S vcnt))) s1 H9.
    tauto.
    sets_unfold in H9.
    destruct H9 as [s2].
    destruct H9.
    pose proof eval_comlist_seq_inf 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))
    [SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))] s2.
    destruct H11.
    pose proof H11 H10.
    destruct H13.
    pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) s2 H13.
    tauto.
    sets_unfold in H13.
    destruct H13 as [s4].
    destruct H13.
    pose proof never_inf_asgn (S vcnt) 
      (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) s4 H14.
    tauto.
  + pose proof eval_comlist_seq_inf 
      (ex2pre e1 (S (S vcnt))) 
      ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s.
    destruct H3.
    pose proof H3 H1.
    destruct H5.
    -
    pose proof H (S (S vcnt)) s H5.
    tauto.
    -
    sets_unfold in H5.
    destruct H5 as [s1].
    destruct H5.
    pose proof eval_comlist_seq_inf 
    [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S(S vcnt)))] 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
    [SCAsgnVar (nat2Sname (S vcnt))
       (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s1.
    destruct H7.
    pose proof H7 H6.
    destruct H9.
    pose proof never_inf_asgn vcnt (ex2se e1 (S (S vcnt))) s1 H9.
    tauto.
    sets_unfold in H9.
    destruct H9 as [s2].
    destruct H9.
    pose proof eval_comlist_seq_inf 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))
    [SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))] s2.
    destruct H11.
    pose proof H11 H10.
    destruct H13.
    pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) s2 H13.
    tauto.
    sets_unfold in H13.
    destruct H13 as [s4].
    destruct H13.
    pose proof never_inf_asgn (S vcnt) 
      (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) s4 H14.
    tauto.
  + pose proof eval_comlist_seq_inf 
      (ex2pre e1 (S (S vcnt))) 
      ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
      ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
      [SCAsgnVar (nat2Sname (S vcnt))
         (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s.
    destruct H3.
    pose proof H3 H1.
    destruct H5.
    -
    pose proof H (S (S vcnt)) s H5.
    tauto.
    -
    sets_unfold in H5.
    destruct H5 as [s1].
    destruct H5.
    pose proof eval_comlist_seq_inf 
    [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S(S vcnt)))] 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) ++
    [SCAsgnVar (nat2Sname (S vcnt))
       (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))]) s1.
    destruct H7.
    pose proof H7 H6.
    destruct H9.
    pose proof never_inf_asgn vcnt (ex2se e1 (S (S vcnt))) s1 H9.
    tauto.
    sets_unfold in H9.
    destruct H9 as [s2].
    destruct H9.
    pose proof eval_comlist_seq_inf 
    (ex2pre e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))
    [SCAsgnVar (nat2Sname (S vcnt))
             (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))))] s2.
    destruct H11.
    pose proof H11 H10.
    destruct H13.
    pose proof H0 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt)))))) s2 H13.
    tauto.
    sets_unfold in H13.
    destruct H13 as [s4].
    destruct H13.
    pose proof never_inf_asgn (S vcnt) 
      (ex2se e2 (S (nat_add (S vcnt) (length (ex2pre e1 (S (S vcnt))))))) s4 H14.
    tauto.
Qed.


Lemma never_inf_unop {NameX : Names}: forall (op : unop) (e : expr) (vcnt : nat) (s : state),
    (forall (vcnt : nat) (s : state), (Seval_comlist (ex2pre e vcnt)).(inf) s -> False)
    ->
    (Seval_comlist (ex2pre (EUnop op e) vcnt)).(inf) s -> False.
Proof.
    simpl.
    intros.
    pose proof eval_comlist_seq_inf 
        (ex2pre e (S vcnt))
        [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))] s as H2.
    pose proof never_inf_asgn vcnt (ex2se e (S vcnt)) as Ha.
    destruct H2.
    pose proof H1 H0.
    destruct H3.
    - pose proof H (S vcnt) s.
      tauto.
    - sets_unfold in H3.
      destruct H3 as [s1].
      destruct H3.
      pose proof Ha s1.
      tauto.
Qed.

Lemma never_inf_deref {NameX : Names}: forall (e : expr) (vcnt : nat) (s : state),
    (forall (vcnt : nat) (s : state), (Seval_comlist (ex2pre e vcnt)).(inf) s -> False)
    ->
    (Seval_comlist (ex2pre (EDeref e) vcnt)).(inf) s -> False.
Proof.
    simpl.
    intros.
    pose proof eval_comlist_seq_inf 
        (ex2pre e (S vcnt))
        [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))] s as H2.
    pose proof never_inf_asgn vcnt (ex2se e (S vcnt)) as Ha.
    destruct H2.
    pose proof H1 H0.
    destruct H3.
    - pose proof H (S vcnt) s.
      tauto.
    - sets_unfold in H3.
      destruct H3 as [s1].
      destruct H3.
      pose proof Ha s1.
      tauto.
Qed.

Lemma never_inf_addrof {NameX : Names}: forall (e : expr) (vcnt : nat) (s : state),
    (forall (vcnt : nat) (s : state), (Seval_comlist (ex2pre e vcnt)).(inf) s -> False)
    ->
    (Seval_comlist (ex2pre (EAddrOf e) vcnt)).(inf) s -> False.
Proof.
    simpl.
    intros.
    destruct e; simpl in H0; sets_unfold in H0.
    + tauto.
    + tauto.
    + tauto.
    + tauto.
    + assert ((Seval_comlist (ex2pre (EDeref e) vcnt)).(inf) s).
      {
        simpl.
        pose proof eval_comlist_seq_inf 
        (ex2pre e (S vcnt))
        [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))] s.
        destruct H1.
        assert ((Seval_comlist (ex2pre e (S vcnt))).(inf) s \/
        ((Seval_comlist (ex2pre e (S vcnt))).(nrm)
         ∘ (Seval_comlist
              [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))]).(inf))
          s).
        {
          tauto.
        }
        pose proof H2 H3.
        tauto. 
      }
      pose proof H vcnt s.
      tauto.
    + tauto.
Qed.


Lemma never_inf {NameX : Names}: forall (e : expr) (vcnt : nat) (s : state),
    (Seval_comlist (ex2pre e vcnt)).(inf) s -> False.
Proof.
    intros e.
    induction e.
    + tauto.
    + tauto.
    + intros; pose proof never_inf_binop op e1 e2 vcnt s; tauto.
    + intros; pose proof never_inf_unop op e vcnt s; tauto.
    + intros; pose proof never_inf_deref e vcnt s; tauto.
    + intros; pose proof never_inf_addrof e vcnt s; tauto.
Qed.

Lemma Split_crefine_inf_AsgnVar {NameX : Names} {NPX : NamesProperty}:
    forall (vcnt : nat) (x : var_name) (e : expr),
    forall (s1 ss1 : state),
    (Seval_comlist (com2comlist (CAsgnVar x e) vcnt)).(inf) ss1
    -> correspond s1 ss1 
    -> (eval_com (CAsgnVar x e)).(inf) s1
        \/ (eval_com (CAsgnVar x e)).(err) s1.
Proof.
    intros vcnt x e s1 ss1.
    unfold com2comlist.
    intros.
    pose proof eval_comlist_seq_inf (com2pre (CAsgnVar x e) vcnt) (com2sc (CAsgnVar x e) vcnt) ss1.
    destruct H1.
    pose proof H1 H.
    pose proof asgn_pre x e vcnt.
    pose proof asgn_sc x e vcnt.
    rewrite H4 in H3.
    rewrite H5 in H3.
    destruct H3.
    + pose proof never_inf e vcnt ss1 H3.
      tauto.
    + sets_unfold in H3.
      destruct H3 as [ss2].
      destruct H3.
      revert H6.
      simpl.
      sets_unfold.
      intros.
      destruct H6; [tauto|].
      destruct H6.
      destruct H6.
      tauto.
Qed.


Lemma construct_asgnderef_sound: forall (s : state) (e1 e2 : expr) (i a : int64),
    (eval_r e1).(nrm) s i ->
    s.(mem) i <> None ->
    (eval_r e2).(nrm) s a ->
    (eval_com (CAsgnDeref e1 e2)).(nrm) s (construct_state s i a).
Proof.
    intros.
    simpl.
    unfold asgn_deref_sem_nrm.
    exists i, a.
    split.
    tauto.
    split.
    tauto.
    split.
    tauto.
    unfold construct_state.
    simpl.
    split.
    pose proof Int64.eq_true i.
    rewrite H2.
    tauto.
    split.
    intros.
    tauto.
    intros.
    pose proof Int64.eq_false i p H2.
    rewrite H3.
    tauto.
Qed.

Lemma midstate_asgnderef_nrm {NameX : Names} {NPX : NamesProperty}:
  forall (vcnt : nat) (e1 e2 : expr),
    forall (s1 ss1 ss2 : state),
    correspond s1 ss1  ->
    (Seval_comlist (com2comlist (CAsgnDeref e1 e2) vcnt)).(nrm) ss1 ss2
    ->
    exists (ss11 ss12 ss13 ss14 : state),
    (Seval_comlist (ex2pre e1 (S (S vcnt)))).(nrm) ss1 ss11
    /\ (Seval_comlist [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))]).(nrm) ss11 ss12
    /\ (Seval_comlist (ex2pre e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))).(nrm) ss12 ss13
    /\ (Seval_comlist [SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2
       (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))]).(nrm) ss13 ss14
    /\ (Seval_comlist [SCAsgnDeref (genSEVar_n vcnt) (genSEVar_n (S vcnt))]).(nrm) ss14 ss2
    /\ correspond s1 ss11
    /\ correspond s1 ss12
    /\ correspond s1 ss13
    /\ correspond s1 ss14.
Proof.
  unfold com2comlist, com2pre, com2sc.
  intros.
  pose proof eval_comlist_seq_nrm (ex2pre e1 (S (S vcnt)) ++
  [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
  ex2pre e2
    (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))) ++
  [SCAsgnVar (nat2Sname (S vcnt))
     (ex2se e2
        (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))])
  [SCAsgnDeref (genSEVar_n vcnt) (genSEVar_n (S vcnt))] ss1 ss2.
  destruct H1.
  pose proof H1 H0.
  sets_unfold in H3.
  destruct H3 as [ss14].
  destruct H3.
  pose proof midstate_4_nrm vcnt e1 e2 ss1 ss14 H3.
  destruct H5 as [ss11 [ss12 [ss13 [? [? [? ]]]]]].
  exists ss11, ss12, ss13, ss14.
  pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H H5.
  pose proof correspond_prop1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H9 H6.
  pose proof correspond_prop2 e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))) s1 ss12 ss13 H10 H7.
  pose proof correspond_prop1 (S vcnt) (ex2se e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt)))))) s1 ss13 ss14 H11 H8.
  tauto.
Qed.

Lemma asgnderef_nrm_prop {NameX : Names} {NPX : NamesProperty}:
  forall (vcnt : nat) (ss14 ss2 : state),
    (Seval_comlist
      [SCAsgnDeref (genSEVar_n vcnt) (genSEVar_n (S vcnt))]).(nrm) ss14 ss2
    -> True .
Proof.
  simpl.
  unfold asgn_deref_sem_nrm, asgn_deref_sem_err, deref_sem_nrm.
  sets_unfold.
  intros.
  destruct H.
  destruct H.
  rewrite H0 in H.
  destruct H as [?[?[?[?[?[?[?]]]]]]].
  tauto.
Qed.



Lemma Split_crefine_nrm_AsgnDeref {NameX : Names} {NPX : NamesProperty}:
    forall (vcnt : nat) (e1 e2 : expr),
    forall (s1 ss1 ss2 : state),
    (Seval_comlist (com2comlist (CAsgnDeref e1 e2) vcnt)).(nrm) ss1 ss2
    -> correspond s1 ss1 
    -> ((exists (s2 : state), (eval_com (CAsgnDeref e1 e2)).(nrm) s1 s2 /\ correspond s2 ss2)
        \/ (eval_com (CAsgnDeref e1 e2)).(err) s1).
Proof.
  unfold com2comlist, com2pre, com2sc.
  intros.
  pose proof eval_comlist_seq_nrm (ex2pre e1 (S (S vcnt)) ++
  [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
  ex2pre e2
    (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))) ++
  [SCAsgnVar (nat2Sname (S vcnt))
     (ex2se e2
        (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))])
  [SCAsgnDeref (genSEVar_n vcnt) (genSEVar_n (S vcnt))] ss1 ss2.
  destruct H1.
  pose proof H1 H.
  sets_unfold in H3.
  destruct H3 as [ss14].
  destruct H3.

  simpl in H4.
  unfold asgn_deref_sem_nrm, asgn_deref_sem_err, deref_sem_nrm in H4.
  sets_unfold in H4.
  destruct H4.
  destruct H4.
  rewrite H5 in H4.
  destruct H4 as [?[?[?[?[?[?[?]]]]]]].
  destruct H4.
  destruct H4.
  destruct H6.
  destruct H6.

  pose proof Split_Serefine_nrm e1 as IH1.
  pose proof Split_Serefine_nrm e2 as IH2.

  pose proof midstate_prop_4_nrm vcnt e1 e2 x2 x3 x0 x1 s1 ss1 ss14 IH1 IH2 H3 H0 H4 H11 H6 H12.
  
  destruct H13 as [H13 H20].
  destruct H13.
  +
  destruct H13.
  pose proof mem_split s1 x0.
  destruct H15.
  ++
  destruct H15.
  left.
  exists (construct_state s1 x0 x1).
  assert (s1.(mem) x0 <> None).
  {
    rewrite H15.
    discriminate.
  }
  
  pose proof construct_asgnderef_sound s1 e1 e2 x0 x1 H13 H16 H14.
  split; [tauto|].
  revert H20.
  unfold correspond, construct_state.
  simpl.
  intros.
  destruct H20 as [?[?]].
  split.
  intros.
  pose proof H9 (name2Sname x5).
  rewrite <- H21.
  pose proof H18 x5 i.
  tauto. 
  split.
  intros a v.
  pose proof classic (x0 = a).
  destruct H21.
  +++
  rewrite H21.
  pose proof Int64.eq_true a.
  rewrite H22.
  rewrite H21 in H8.
  rewrite H8.
  tauto.
  +++
  pose proof Int64.eq_false x0 a H21.
  rewrite H22.
  intros.
  pose proof H19 a v H23.
  pose proof H10 a H21.
  rewrite <- H25.
  tauto.
  +++
  intros.
  pose proof classic (x0 = (ss2.(env) (nat2Sname vcnt0))).
  destruct H21.
  ++++
  pose proof H9 (nat2Sname vcnt0).
  rewrite <- H22 in H21.
  rewrite H21 in H15.
  pose proof H20 vcnt0.
  rewrite H15 in H23.
  destruct H23.
  discriminate.
  ++++
  pose proof Int64.eq_false x0 (ss2.(env) (nat2Sname vcnt0)) H21.
  rewrite H22.
  pose proof H10 (ss2.(env) (nat2Sname vcnt0)) H21.
  pose proof H20 vcnt0.
  pose proof H9 (nat2Sname vcnt0).
  rewrite <- H25.
  split; [tauto|].
  rewrite <- H25 in H23.
  destruct H23. 
  tauto.
  ++
  right.
  simpl.
  sets_unfold.
  right.
  unfold asgn_deref_sem_err.
  exists x0.
  tauto.
  +
  right.
  simpl.
  sets_unfold.
  tauto.
Qed.


Lemma Split_crefine_err_AsgnDeref {NameX : Names} {NPX : NamesProperty}:
    forall (vcnt : nat) (e1 e2 : expr),
    forall (s1 ss1 : state),
    (Seval_comlist (com2comlist (CAsgnDeref e1 e2) vcnt)).(err) ss1
    -> correspond s1 ss1 
    -> (eval_com (CAsgnDeref e1 e2)).(err) s1.
Proof.
    unfold com2comlist, com2pre, com2sc.
    intros.
    simpl.
    sets_unfold.
    pose proof Split_Serefine_err e1 (S (S vcnt)) as [H101 [H102 H103]].
    pose proof Split_Serefine_err e2 (nat_add (S (S vcnt))
    (length (ex2pre e1 (S (S vcnt))))) as [H201 [H202 H203]].
    pose proof eval_comlist_seq_err (ex2pre e1 (S (S vcnt)) ++
    [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
    ex2pre e2
      (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))) ++
    [SCAsgnVar (nat2Sname (S vcnt))
       (ex2se e2
          (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))])
    [SCAsgnDeref (genSEVar_n vcnt) (genSEVar_n (S vcnt))] ss1.
    destruct H1.
    pose proof H1 H.
    pose proof Split_Serefine_nrm e1 (S (S vcnt)) as [H1l H1r].
    destruct H3.
    +
    pose proof eval_comlist_seq_err (ex2pre e1 (S (S vcnt)))
    ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
    ex2pre e2
      (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))) ++
    [SCAsgnVar (nat2Sname (S vcnt))
       (ex2se e2
          (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))]) ss1.
    destruct H4.
    pose proof H4 H3.
    destruct H6.
    ++
    pose proof H101 s1 ss1 H0 H6.
    destruct H7.
    tauto.
    ++
    sets_unfold in H6.
    destruct H6 as [ss11].
    destruct H6.
    pose proof eval_comlist_seq_err
    [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] 
    (ex2pre e2
      (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))) ++
    [SCAsgnVar (nat2Sname (S vcnt))
       (ex2se e2
          (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))]) ss11.
    destruct H8.
    pose proof H8 H7.
    pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H0 H6.
    pose proof H1r s1.
    destruct H10.
    +++
    simpl in H10.
    sets_unfold in H10.
    destruct H10.
    ++++
    destruct H10.
    -
    destruct H10; [tauto|].
    pose proof H103 s1 ss1 ss11 H0 H6 H10.
    tauto.
    -
    right.
    revert H10 H11.
    unfold asgn_deref_sem_err, correspond.
    intros.
    destruct H10.
    destruct H10.
    destruct H11.
    destruct H14.
    pose proof H15 vcnt.
    destruct H16.
    rewrite <- H10 in H13.
    rewrite H13 in H17.
    tauto.
    ++++
    destruct H10.
    tauto.
    +++
    sets_unfold in H10.
    destruct H10 as [ss12].
    destruct H10.
    pose proof correspond_prop1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H11 H10.
    pose proof eval_comlist_seq_err
      (ex2pre e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt)))))) 
       [SCAsgnVar (nat2Sname (S vcnt))
       (ex2se e2
          (nat_add (S (S vcnt))
             (length (ex2pre e1 (S (S vcnt))))))] ss12.
    destruct H15.
    pose proof H15 H13.
    destruct H17.
    ++++
    pose proof H201 s1 ss12 H14 H17.
    tauto.
    ++++
    sets_unfold in H17.
    destruct H17 as [ss13].
    destruct H17.
    pose proof correspond_prop2 e2 (nat_add (S (S vcnt))
    (length (ex2pre e1 (S (S vcnt))))) s1 ss12 ss13 H14 H17.
    revert H18 H19.
    simpl.
    unfold asgn_deref_sem_err, correspond.
    sets_unfold.
    intros.
    destruct H18.
    -
    destruct H18.
    --
    destruct H18; [tauto|].
    pose proof H203 s1 ss12 ss13 H14 H17 H18.
    tauto.
    --
    destruct H18.
    destruct H18.
    destruct H19.
    destruct H21.
    rewrite <- H18 in H20.
    pose proof H22 (S vcnt).
    destruct H23.
    rewrite H20 in H24.
    tauto.
    -
    destruct H18.
    destruct H18.
    tauto.
    +
    sets_unfold in H3.
    destruct H3 as [ss14].
    destruct H3.
    pose proof midstate_cor_4_nrm vcnt e1 e2 s1 ss1 ss14 H3 H0.
    destruct H5 as[ss11[ss12[ss13[?[?[?[?[?[?[?[?[?]]]]]]]]]]]].
    revert H4.
    simpl.
    sets_unfold.
    unfold deref_sem_err, asgn_deref_sem_err, deref_sem_nrm, asgn_deref_sem_nrm.
    intros.
    destruct H4.
    ++
    destruct H4.
    +++
    destruct H4.
    ++++
    destruct H4; [tauto|].
    destruct H4.
    destruct H4.
    pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H7.
    pose proof greater_vcnt2 vcnt ss13 ss14 e1 e2 H8.
    simpl in H6.
    unfold asgn_deref_sem_nrm in H6.
    sets_unfold in H6.
    destruct H6.
    destruct H6.
    rewrite H18 in H6.
    destruct H6 as [?[?[?[?[?[?[?]]]]]]].
    pose proof H22 (nat2Sname vcnt).
    rewrite <- H4 in H15.
    rewrite <- H17 in H15.
    rewrite <- H16 in H15.
    rewrite <- H24 in H15.
    rewrite H6 in H15.
    rewrite H21 in H15.
    destruct H15; discriminate.
    ++++
    destruct H4; [tauto|].
    destruct H4.
    destruct H4.
    simpl in H8.
    unfold asgn_deref_sem_nrm in H8.
    sets_unfold in H8.
    destruct H8.
    destruct H8.
    rewrite H16 in H8.
    destruct H8 as [?[?[?[?[?[?[?]]]]]]].
    pose proof H20 (nat2Sname (S vcnt)).
    rewrite <- H4 in H15.
    rewrite <- H22 in H15.
    rewrite H8 in H15.
    rewrite H19 in H15.
    destruct H15; discriminate.
    +++
    destruct H4.
    destruct H4.
    destruct H4.
    destruct H4.
    pose proof greater_vcnt1 vcnt ss12 ss13 e1 e2 H7.
    pose proof greater_vcnt2 vcnt ss13 ss14 e1 e2 H8.
    pose proof asgn_vcnt_ex2se_nrm_prop (ex2se e1 (S (S vcnt))) vcnt ss11 ss12 H6 as H25.
    simpl in H6.
    unfold asgn_deref_sem_nrm in H6.
    sets_unfold in H6.
    destruct H6.
    destruct H6.
    rewrite H19 in H6.
    destruct H6 as [?[?[?[?[?[?[?]]]]]]].
    pose proof H23 (nat2Sname vcnt).
    rewrite <- H4 in H16.
    rewrite <- H18 in H16.
    rewrite <- H17 in H16.
    assert ((Seval_r (genSECV vcnt)).(nrm) ss12 x).
    {
      simpl.
      unfold deref_sem_nrm.
      exists (ss12.(env) (nat2Sname vcnt)).
      tauto.
    }
    pose proof H25 x H27.
    pose proof H1r s1 ss1 ss11 x H0 H5 H28.
    destruct H29; [|tauto].
    right.
    exists x.
    split; [tauto|].
    pose proof mem_split s1 x.
    destruct H30; [|tauto].
    destruct H30.
    pose proof H13 x x4 H30.
    rewrite H31 in H15.
    discriminate.
    ++
    destruct H4.
    destruct H4.
    tauto.
Qed.

Lemma Split_crefine_inf_AsgnDeref {NameX : Names} {NPX : NamesProperty}:
    forall (vcnt : nat) (e1 e2 : expr),
    forall (s1 ss1 : state),
    (Seval_comlist (com2comlist (CAsgnDeref e1 e2) vcnt)).(inf) ss1 
    -> correspond s1 ss1 
    -> (eval_com (CAsgnDeref e1 e2)).(inf) s1
        \/ (eval_com (CAsgnDeref e1 e2)).(err) s1.
Proof.
  unfold com2comlist, com2pre, com2sc.
  intros.
  pose proof eval_comlist_seq_inf (ex2pre e1 (S (S vcnt)) ++
  [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
  ex2pre e2
    (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))) ++
  [SCAsgnVar (nat2Sname (S vcnt))
     (ex2se e2
        (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))])
  [SCAsgnDeref (genSEVar_n vcnt) (genSEVar_n (S vcnt))] ss1.
  destruct H1.
  pose proof H1 H.
  destruct H3.
  +
  pose proof eval_comlist_seq_inf (ex2pre e1 (S (S vcnt)))
  ([SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] ++
  ex2pre e2
    (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))) ++
  [SCAsgnVar (nat2Sname (S vcnt))
     (ex2se e2
        (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))]) ss1.
  destruct H4.
  pose proof H4 H3.
  destruct H6.
  ++
  pose proof never_inf e1 (S (S vcnt)) ss1 H6.
  tauto.
  ++
  sets_unfold in H6.
  destruct H6 as [ss11].
  destruct H6.
  pose proof eval_comlist_seq_inf 
  [SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt)))] 
  (ex2pre e2
    (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))) ++
  [SCAsgnVar (nat2Sname (S vcnt))
     (ex2se e2
        (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))]) ss11.
  destruct H8.
  pose proof H8 H7.
  pose proof correspond_prop2 e1 (S (S vcnt)) s1 ss1 ss11 H0 H6.
  destruct H10.
  +++
  pose proof never_inf_asgn vcnt (ex2se e1 (S (S vcnt))) ss11 H10.
  tauto.
  +++
  sets_unfold in H10.
  destruct H10 as [ss12].
  destruct H10.
  pose proof correspond_prop1 vcnt (ex2se e1 (S (S vcnt))) s1 ss11 ss12 H11 H10.
  pose proof eval_comlist_seq_inf
    (ex2pre e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt)))))) 
     [SCAsgnVar (nat2Sname (S vcnt))
     (ex2se e2
        (nat_add (S (S vcnt))
           (length (ex2pre e1 (S (S vcnt))))))] ss12.
  destruct H14.
  pose proof H14 H12.
  destruct H16.
  ++++
  pose proof never_inf e2 (nat_add (S (S vcnt))
  (length (ex2pre e1 (S (S vcnt))))) ss12 H16.
  tauto.
  ++++
  sets_unfold in H16.
  destruct H16 as [ss13].
  destruct H16.
  pose proof never_inf_asgn (S vcnt) (ex2se e2
  (nat_add (S (S vcnt))
     (length (ex2pre e1 (S (S vcnt)))))) ss13 H17.
  tauto.
  +
  sets_unfold in H3.
  destruct H3 as [ss14].
  destruct H3.
  simpl in H4.
  sets_unfold in H4.
  destruct H4; [tauto|].
  destruct H4.
  tauto.
Qed.

Lemma midstate_CSeq {NameX : Names}: forall (c1 c2 : com) (vcnt : nat),
    com2comlist (CSeq c1 c2) vcnt = 
    (com2comlist c1 vcnt) ++ (com2comlist c2 (nat_add vcnt (length (com2comlist c1 vcnt)))).
Proof.
    intros.
    unfold com2comlist.
    simpl.
    pose proof seq_length (com2pre c1 vcnt) (com2sc c1 vcnt).
    rewrite H.
    pose proof seq_asso (com2pre c1 vcnt) (com2sc c1 vcnt) 
    (com2pre c2 (nat_add vcnt (nat_add (length (com2pre c1 vcnt)) (length (com2sc c1 vcnt))))
    ++ com2sc c2 (nat_add vcnt (nat_add (length (com2pre c1 vcnt)) (length (com2sc c1 vcnt))))).
    rewrite <- H0.
    reflexivity.
Qed.


Lemma Split_crefine_nrm_Seq_aux {NameX : Names} {NPX : NamesProperty}:
    forall (c1 c2 : com),
    (forall vcnt : nat, Screfine_nrm (com2comlist c1 vcnt) c1) ->
    (forall vcnt : nat, Screfine_nrm (com2comlist c2 vcnt) c2) ->
    forall vcnt : nat, Screfine_nrm (com2comlist (CSeq c1 c2) vcnt) (CSeq c1 c2).
Proof.
    intros c1 c2.
    unfold Screfine_nrm.
    intros IH1 IH2 vcnt s1 ss1 ss3 ? ?.
    pose proof midstate_CSeq c1 c2 vcnt.
    rewrite H1 in H.
    pose proof eval_comlist_seq_nrm (com2comlist c1 vcnt) (com2comlist c2 (nat_add vcnt (length (com2comlist c1 vcnt)))) ss1 ss3.
    destruct H2.
    pose proof H2 H.
    sets_unfold in H4.
    destruct H4 as [ss2].
    destruct H4.
    pose proof IH1 vcnt s1 ss1 ss2 H4 H0.
    destruct H6.
    + destruct H6 as [s2].
      destruct H6.
      pose proof IH2 ((nat_add vcnt (length (com2comlist c1 vcnt)))) s2 ss2 ss3 H5 H7.
      destruct H8.
      - destruct H8 as [s3].
        destruct H8.
        left.
        exists s3.
        simpl.
        split; [|tauto].
        sets_unfold.
        exists s2.
        tauto.
      - right.
        simpl.
        sets_unfold.
        right.
        exists s2.
        tauto.
    + right. 
      simpl.
      sets_unfold.
      left.
      tauto.
Qed.

Lemma Split_crefine_err_Seq_aux {NameX : Names} {NPX : NamesProperty}:
    forall (c1 c2 : com),
    (forall vcnt : nat, Screfine (com2comlist c1 vcnt) c1) ->
    (forall vcnt : nat, Screfine (com2comlist c2 vcnt) c2) ->
    forall vcnt : nat, Screfine_err (com2comlist (CSeq c1 c2) vcnt) (CSeq c1 c2).
Proof.
    intros c1 c2.
    unfold Screfine_err.
    intros IH1 IH2 vcnt s1 ss1 ? ?.
    pose proof IH1 vcnt as IH1.
    destruct IH1 as [H01 H02 H03].
    unfold Screfine_nrm in H01.
    unfold Screfine_err in H02.
    pose proof midstate_CSeq c1 c2 vcnt.
    rewrite H1 in H.
    pose proof eval_comlist_seq_err (com2comlist c1 vcnt) (com2comlist c2 (nat_add vcnt (length (com2comlist c1 vcnt)))) ss1.
    destruct H2.
    pose proof H2 H.
    sets_unfold in H4.
    simpl.
    sets_unfold.
    destruct H4.
    + pose proof H02 s1 ss1 H4 H0.  
      simpl.
      tauto.
    + 
    destruct H4 as [ss2].
    destruct H4.
    pose proof H01 s1 ss1 ss2 H4 H0.
    destruct H6.
    - destruct H6 as [s2].
      destruct H6.
      pose proof IH2 ((nat_add vcnt (length (com2comlist c1 vcnt)))).
      destruct H8 as [H10 H11 H12].
      unfold Screfine_err in H11.
      pose proof H11 s2 ss2 H5 H7.
      right.
      exists s2.
      tauto.
    - tauto.
Qed.

Lemma Split_crefine_inf_Seq_aux {NameX : Names} {NPX : NamesProperty}:
    forall (c1 c2 : com),
    (forall vcnt : nat, Screfine (com2comlist c1 vcnt) c1) ->
    (forall vcnt : nat, Screfine (com2comlist c2 vcnt) c2) ->
    forall vcnt : nat, Screfine_inf (com2comlist (CSeq c1 c2) vcnt) (CSeq c1 c2).
Proof.
    intros c1 c2.
    unfold Screfine_inf.
    intros IH1 IH2 vcnt s1 ss1 ? ?.
    pose proof IH1 vcnt as IH1.
    destruct IH1 as [H01 H02 H03].
    unfold Screfine_nrm in H01.
    unfold Screfine_inf in H03.
    pose proof midstate_CSeq c1 c2 vcnt.
    rewrite H1 in H.
    pose proof eval_comlist_seq_inf (com2comlist c1 vcnt) (com2comlist c2 (nat_add vcnt (length (com2comlist c1 vcnt)))) ss1.
    destruct H2.
    pose proof H2 H.
    sets_unfold in H4.
    simpl.
    sets_unfold.
    destruct H4.
    + pose proof H03 s1 ss1 H4 H0.  
      simpl.
      tauto.
    + 
    destruct H4 as [ss2].
    destruct H4.
    pose proof H01 s1 ss1 ss2 H4 H0.
    destruct H6.
    - destruct H6 as [s2].
      destruct H6.
      pose proof IH2 ((nat_add vcnt (length (com2comlist c1 vcnt)))).
      destruct H8 as [H10 H11 H12].
      unfold Screfine_inf in H12.
      pose proof H12 s2 ss2 H5 H7.
      destruct H8.
      left.
      right.
      exists s2.
      tauto.
      right.
      right.
      exists s2.
      tauto.
    - tauto.
Qed.

Lemma preandsc {NameX : Names}: forall (vcnt : nat) (c : com),
    com2pre c vcnt ++ com2sc c vcnt = com2comlist c vcnt.
Proof.
    unfold com2comlist.
    reflexivity.
Qed.

Lemma Split_crefine_nrm_If_aux {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr) (c1 c2 : com),
    (forall vcnt : nat,
    Screfine_nrm (com2comlist c1 vcnt) c1) ->
   (forall vcnt : nat,
    Screfine_nrm (com2comlist c2 vcnt) c2) ->
   forall vcnt : nat,
   Screfine_nrm (com2comlist (CIf e c1 c2) vcnt) (CIf e c1 c2).
Proof.
    intros.
    unfold Screfine_nrm.
    intros s1 ss1 ss3.
    unfold com2comlist.
    simpl.
    intros.
    pose proof eval_comlist_seq_nrm (ex2pre e vcnt) 
    [SCIf (ex2se e vcnt) 
        (com2pre c1 (nat_add vcnt (length (ex2pre e vcnt))) ++
            com2sc c1 (nat_add vcnt (length (ex2pre e vcnt))))
        (com2pre c2 (nat_add (nat_add vcnt (length (ex2pre e vcnt))) 
                (nat_add (length (com2pre c1 (nat_add vcnt (length (ex2pre e vcnt)))))
                    (length (com2sc c1 (nat_add vcnt (length (ex2pre e vcnt))))))) ++
            com2sc c2 (nat_add (nat_add vcnt (length (ex2pre e vcnt)))
                (nat_add (length (com2pre c1 (nat_add vcnt (length (ex2pre e vcnt)))))
                    (length  (com2sc c1 (nat_add vcnt (length (ex2pre e vcnt))))))))] ss1 ss3.
    destruct H3.
    pose proof H3 H1.
    sets_unfold in H5.
    destruct H5 as [ss2].
    destruct H5.
    pose proof correspond_prop2 e vcnt s1 ss1 ss2 H2 H5.
    revert H6.
    simpl.
    sets_unfold.
    intros.
    destruct H6.
    destruct H6.
    rewrite H8 in H6.
    destruct H6.
    + destruct H6.
      unfold test_true in H6.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite <- H10 in H9.
      destruct H6.
      destruct H6.
      pose proof H (nat_add vcnt (length (ex2pre e vcnt))).
      unfold Screfine_nrm in H12.
      pose proof preandsc (nat_add vcnt (length (ex2pre e vcnt))) c1.
      rewrite H13 in H9.
      pose proof H12 s1 ss2 ss3 H9 H7.
      pose proof Split_Serefine_nrm e vcnt.
      unfold Serefine_nrm, Serefine_nrm_r in H15.
      destruct H15 as [H100 H15].
      pose proof H15 s1 ss1 ss2 x1 H2 H5 H6.
      destruct H16.
      - destruct H14.
        --  left.
            destruct H14 as [s2].
            exists s2.
            split; [|tauto].
            left.
            exists s1.
            split.
            unfold test_true.
            sets_unfold.
            split; [|tauto].
            exists x1.
            tauto.
            tauto.
        --  right.
            left.
            right.
            exists s1.
            split; [|tauto].
            unfold test_true.
            sets_unfold.
            split; [|tauto].
            exists x1.
            tauto.
      - right.
        left.
        tauto.
    + destruct H6.
      unfold test_false in H6.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      rewrite <- H10 in H9.
      pose proof H0 (nat_add (nat_add vcnt (length (ex2pre e vcnt)))
      (nat_add
         (length (com2pre c1 (nat_add vcnt (length (ex2pre e vcnt)))))
         (length (com2sc c1 (nat_add vcnt (length (ex2pre e vcnt))))))).
      unfold Screfine_nrm in H11.
      pose proof preandsc (nat_add (nat_add vcnt (length (ex2pre e vcnt)))
      (nat_add
         (length (com2pre c1 (nat_add vcnt (length (ex2pre e vcnt)))))
         (length (com2sc c1 (nat_add vcnt (length (ex2pre e vcnt))))))) c2.
      rewrite H12 in H9.
      pose proof H11 s1 ss2 ss3 H9 H7.
      pose proof Split_Serefine_nrm e vcnt.
      unfold Serefine_nrm, Serefine_nrm_r in H14.
      destruct H14 as [H14 H15].
      pose proof H15 s1 ss1 ss2 (Int64.repr 0) H2 H5 H6.
      destruct H16.
      - destruct H13.
        --  left.
            destruct H13 as [s2].
            exists s2.
            split; [|tauto].
            right.
            exists s1.
            split.
            unfold test_false.
            sets_unfold.
            tauto.
            tauto.
        --  right.
            right.
            exists s1.
            split; [|tauto].
            unfold test_false.
            sets_unfold.
            tauto.
      - right.
        left.
        tauto.
Qed.

Lemma Split_crefine_err_If_aux {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr) (c1 c2 : com),
    (forall vcnt : nat,
    Screfine (com2comlist c1 vcnt) c1) ->
   (forall vcnt : nat,
    Screfine (com2comlist c2 vcnt) c2) ->
   forall vcnt : nat,
   Screfine_err (com2comlist (CIf e c1 c2) vcnt) (CIf e c1 c2).
Proof.
    intros.
    unfold Screfine_err.
    intros s1 ss1.
    unfold com2comlist.
    simpl.
    intros.
    sets_unfold.
    pose proof eval_comlist_seq_err (ex2pre e vcnt) 
    [SCIf (ex2se e vcnt) 
        (com2pre c1 (nat_add vcnt (length (ex2pre e vcnt))) ++
            com2sc c1 (nat_add vcnt (length (ex2pre e vcnt))))
        (com2pre c2 (nat_add (nat_add vcnt (length (ex2pre e vcnt))) 
                (nat_add (length (com2pre c1 (nat_add vcnt (length (ex2pre e vcnt)))))
                    (length (com2sc c1 (nat_add vcnt (length (ex2pre e vcnt))))))) ++
            com2sc c2 (nat_add (nat_add vcnt (length (ex2pre e vcnt)))
                (nat_add (length (com2pre c1 (nat_add vcnt (length (ex2pre e vcnt)))))
                    (length  (com2sc c1 (nat_add vcnt (length (ex2pre e vcnt))))))))] ss1.
    destruct H3.
    pose proof H3 H1.
    sets_unfold in H5.
    pose proof H (nat_add vcnt (length (ex2pre e vcnt))) as [H100 H101 H102].
    pose proof H0 (nat_add (nat_add vcnt (length (ex2pre e vcnt))) (nat_add
       (length (com2pre c1 (nat_add vcnt (length (ex2pre e vcnt)))))
       (length (com2sc c1 (nat_add vcnt (length (ex2pre e vcnt))))))) as [H110 H111 H112].
    unfold Screfine_nrm in H100.
    unfold Screfine_err in H101, H111.
    pose proof Split_Serefine_err e vcnt as [H200 [H201 H202]].
    pose proof Split_Serefine_nrm e vcnt as [H300 H301].
    destruct H5.
    + unfold Serefine_err1 in H200.
      pose proof H200 s1 ss1 H2 H5 as [? ?].
      tauto.
    + 
    destruct H5 as [ss2].
    destruct H5.
    pose proof correspond_prop2 e vcnt s1 ss1 ss2 H2 H5.
    revert H6.
    simpl.
    sets_unfold.
    intros.
    destruct H6 as [[[H6|H6]|H6]|H6].
    - unfold Serefine_err2_r in H202.
      pose proof H202 s1 ss1 ss2 H2 H5 H6.
      tauto.
    - destruct H6 as [ss3]. 
      destruct H6.
      pose proof preandsc (nat_add vcnt (length (ex2pre e vcnt))) c1.
      rewrite H9 in H8.
      revert H6.
      unfold test_true.
      sets_unfold.
      intros.
      destruct H6.
      pose proof H7.
      rewrite H10 in H7.
      pose proof H101 s1 ss3 H8 H7.
      destruct H6.
      destruct H6.
      unfold Serefine_nrm_r in H301.
      pose proof H301 s1 ss1 ss2 x H2 H5 H6.
      destruct H14.
      left.
      right.
      exists s1.
      split; [|tauto].
      split; [|tauto].
      exists x.
      tauto.
      tauto.
    - destruct H6 as [ss3]. 
      destruct H6.
      pose proof preandsc (nat_add (nat_add vcnt (length (ex2pre e vcnt))) (nat_add
      (length (com2pre c1 (nat_add vcnt (length (ex2pre e vcnt)))))
      (length (com2sc c1 (nat_add vcnt (length (ex2pre e vcnt))))))) c2.
      rewrite H9 in H8.
      revert H6.
      unfold test_false.
      sets_unfold.
      intros.
      destruct H6.
      pose proof H7.
      rewrite H10 in H7.
      pose proof H111 s1 ss3 H8 H7.
      unfold Serefine_nrm_r in H301.
      pose proof H301 s1 ss1 ss2 (Int64.repr 0) H2 H5 H6.
      destruct H13.
      right.
      exists s1.
      tauto.
      tauto.
    - destruct H6.
      destruct H6.
      tauto.
Qed.

Lemma Split_crefine_inf_If_aux {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr) (c1 c2 : com),
    (forall vcnt : nat,
    Screfine (com2comlist c1 vcnt) c1) ->
   (forall vcnt : nat,
    Screfine (com2comlist c2 vcnt) c2) ->
   forall vcnt : nat,
   Screfine_inf (com2comlist (CIf e c1 c2) vcnt) (CIf e c1 c2).
Proof.
    intros.
    unfold Screfine_inf.
    intros s1 ss1.
    unfold com2comlist.
    simpl.
    intros.
    sets_unfold.
    pose proof eval_comlist_seq_inf (ex2pre e vcnt) 
    [SCIf (ex2se e vcnt) 
        (com2pre c1 (nat_add vcnt (length (ex2pre e vcnt))) ++
            com2sc c1 (nat_add vcnt (length (ex2pre e vcnt))))
        (com2pre c2 (nat_add (nat_add vcnt (length (ex2pre e vcnt))) 
                (nat_add (length (com2pre c1 (nat_add vcnt (length (ex2pre e vcnt)))))
                    (length (com2sc c1 (nat_add vcnt (length (ex2pre e vcnt))))))) ++
            com2sc c2 (nat_add (nat_add vcnt (length (ex2pre e vcnt)))
                (nat_add (length (com2pre c1 (nat_add vcnt (length (ex2pre e vcnt)))))
                    (length  (com2sc c1 (nat_add vcnt (length (ex2pre e vcnt))))))))] ss1.
    destruct H3.
    pose proof H3 H1.
    sets_unfold in H5.
    pose proof H (nat_add vcnt (length (ex2pre e vcnt))) as [H100 H101 H102].
    pose proof H0 (nat_add (nat_add vcnt (length (ex2pre e vcnt))) (nat_add
       (length (com2pre c1 (nat_add vcnt (length (ex2pre e vcnt)))))
       (length (com2sc c1 (nat_add vcnt (length (ex2pre e vcnt))))))) as [H110 H111 H112].
    unfold Screfine_nrm in H100.
    unfold Screfine_inf in H102, H112.
    pose proof Split_Serefine_err e vcnt as [H200 [H201 H202]].
    pose proof Split_Serefine_nrm e vcnt as [H300 H301].
    destruct H5.
    + pose proof never_inf e vcnt ss1.
      tauto.
    + 
    destruct H5 as [ss2].
    destruct H5.
    pose proof correspond_prop2 e vcnt s1 ss1 ss2 H2 H5.
    revert H6.
    simpl.
    sets_unfold.
    intros.
    destruct H6 as [[H6|H6]|H6].
    - destruct H6 as [ss3]. 
      destruct H6.
      pose proof preandsc (nat_add vcnt (length (ex2pre e vcnt))) c1.
      rewrite H9 in H8.
      revert H6.
      unfold test_true.
      sets_unfold.
      intros.
      destruct H6.
      pose proof H7.
      rewrite H10 in H7.
      pose proof H102 s1 ss3 H8 H7.
      destruct H6.
      destruct H6.
      unfold Serefine_nrm_r in H301.
      pose proof H301 s1 ss1 ss2 x H2 H5 H6.
      destruct H14; [|tauto].
      destruct H12.
      --  left.
          left.
          exists s1.
          split; [|tauto].
          split; [|tauto].
          exists x.
          tauto.
      --  right.
          left.
          right.
          exists s1.
          split; [|tauto].
          split; [|tauto].
          exists x.
          tauto.
    - destruct H6 as [ss3]. 
      destruct H6.
      pose proof preandsc (nat_add (nat_add vcnt (length (ex2pre e vcnt))) (nat_add
      (length (com2pre c1 (nat_add vcnt (length (ex2pre e vcnt)))))
      (length (com2sc c1 (nat_add vcnt (length (ex2pre e vcnt))))))) c2.
      rewrite H9 in H8.
      revert H6.
      unfold test_false.
      sets_unfold.
      intros.
      destruct H6.
      pose proof H7.
      rewrite H10 in H7.
      pose proof H112 s1 ss3 H8 H7.
      unfold Serefine_nrm_r in H301.
      pose proof H301 s1 ss1 ss2 (Int64.repr 0) H2 H5 H6.
      destruct H13; [|tauto].
      destruct H12.
      --  left.
          right.
          exists s1.
          tauto.
      --  right.
          right.
          exists s1.
          tauto.
    - destruct H6.
      destruct H6.
      tauto.
Qed.

Lemma split_while_nrm {NameX : Names} {NPX : NamesProperty}:
    forall (n0 : nat) (c : com) (e : expr) (s11 ss21 ss29 : state),
        (forall (vcnt : nat), Screfine_nrm (com2comlist c vcnt) c) ->
        correspond s11 ss21 ->
        (forall (vcnt : nat),
        (exists (ss209 : state), correspond s11 ss209 /\
        (Seval_comlist (ex2pre e vcnt)).(nrm) ss209 ss21) ->
        boundedLB_nrm (Seval_r (ex2se e vcnt))
        (Seval_comlist
            (com2pre c (nat_add vcnt (length (ex2pre e vcnt))) ++
            com2sc c (nat_add vcnt (length (ex2pre e vcnt))) ++
            ex2pre e vcnt))
        n0 ss21 ss29 ->
        (exists s19 : state,
            (exists i : nat, boundedLB_nrm (eval_r e) (eval_com c) i s11 s19) /\
            correspond s19 ss29) \/
            (exists i : nat, boundedLB_err (eval_r e) (eval_com c) i s11))
    .
Proof.
    induction n0.
        + simpl.
          sets_unfold.
          intros.
          tauto.
        + simpl.
          sets_unfold.
          intros c e0 ? ? ? Hv ? vcnt0 ? ?.
          destruct H0 as [ss209].
          destruct H1.
          - destruct H1 as [ss22].
            destruct H1.
            pose proof Split_Serefine_nrm e0 vcnt0 as H200.
            unfold Serefine_nrm, Serefine_nrm_r in H200.
            destruct H200 as [H300 H200].
            unfold test_true in H1.
            sets_unfold in H1.
            destruct H1 as [H1 H13].
            destruct H1.
            destruct H1 as [H1 H203].
            destruct H0 as [H0 H202].
            pose proof H200 s11 ss209 ss21 x H0 H202 H1 as H205.
            destruct H205 as [H205 | H205]; [|
                right;
                exists 1%nat;
                simpl;
                sets_unfold;
                right;
                tauto].
            destruct H2 as [ss25].
            destruct H2.
            pose proof eval_comlist_seq_nrm 
                (com2pre c (nat_add vcnt0 (length (ex2pre e0 vcnt0)))) 
                (com2sc c (nat_add vcnt0 (length (ex2pre e0 vcnt0))) ++
                ex2pre e0 vcnt0)
                ss22 ss25.
            destruct H4.
            pose proof H4 H2.
            sets_unfold in H6.
            destruct H6 as [ss23].
            destruct H6.
            pose proof eval_comlist_seq_nrm
                (com2sc c (nat_add vcnt0 (length (ex2pre e0 vcnt0))))
                (ex2pre e0 vcnt0)
                ss23 ss25.
            destruct H8.
            pose proof H8 H7.
            sets_unfold in H10.
            destruct H10 as [ss24].
            destruct H10.
            pose proof Hv as H101.
            unfold Screfine_nrm, com2comlist in Hv.
            assert ((Seval_comlist
            (com2pre c (nat_add vcnt0 (length (ex2pre e0 vcnt0))) ++
             com2sc c (nat_add vcnt0 (length (ex2pre e0 vcnt0))))).(nrm)
            ss22 ss24).
            {
                pose proof eval_comlist_seq_nrm 
                (com2pre c (nat_add vcnt0 (length (ex2pre e0 vcnt0))))
                (com2sc c (nat_add vcnt0 (length (ex2pre e0 vcnt0)))) 
                ss22 ss24.
                destruct H12.
                sets_unfold in H14.
                apply H14.
                exists ss23.
                tauto.
            }
            rewrite H13 in H.
            pose proof Hv (nat_add vcnt0 (length (ex2pre e0 vcnt0))) 
                s11 ss22 ss24 H12 H.
            destruct H14.
            --  destruct H14 as [s12].
                destruct H14.
                pose proof correspond_prop2 e0 vcnt0 s12 ss24 ss25 H15 H11.
                pose proof IHn0 c e0 s12 ss25 ss29 H101 H16.
                assert (exists (ss209 : state),
                correspond s12 ss209 /\ (Seval_comlist (ex2pre e0 vcnt0)).(nrm) ss209 ss25).
                {
                    exists ss24.
                    tauto.
                }
                pose proof H17 vcnt0 H18 H3.
                destruct H19.
                * destruct H19 as [s19].
                  destruct H19.
                  destruct H19 as [n].
                  left.
                  exists s19.
                  split; [|tauto].
                  exists (S n).
                  simpl.
                  sets_unfold.
                  left.
                  exists s11.
                  split.
                  unfold test_true.
                  simpl.
                  sets_unfold.
                  split.
                  exists x.
                  tauto.
                  tauto.
                  exists s12.
                  tauto.
                * destruct H19 as [n].
                  right.
                  exists (S n).
                  simpl.
                  sets_unfold.
                  left.
                  exists s11.
                  split.
                  unfold test_true.
                  simpl.
                  sets_unfold.
                  split.
                  exists x.
                  tauto.
                  tauto.
                  left.
                  exists s12.
                  tauto.
            --  right.
                exists 1%nat.
                simpl.
                sets_unfold.
                pose proof Split_Serefine_nrm e0 vcnt0.
                unfold Serefine_nrm, Serefine_nrm_r in H15.
                destruct H15.
                pose proof H16 s11 ss209 ss21 x H0 H202 H1.
                destruct H17.
                * left.
                  exists s11.
                  split.
                  unfold test_true.
                  simpl.
                  sets_unfold.
                  split; [|tauto].
                  exists x.
                  tauto.
                  tauto.
                * tauto.                
          - revert H1.
            unfold test_false.
            simpl.
            sets_unfold.
            intros.
            destruct H1.
            rewrite <- H2.
            sets_unfold.
            destruct H0.
            pose proof Split_Serefine_nrm e0 vcnt0.
            unfold Serefine_nrm, Serefine_nrm_r in H4.
            destruct H4.
            pose proof H5 s11 ss209 ss21 (Int64.repr 0) H0 H3 H1.
            destruct H6.
            --  left.
                exists s11.
                split; [| tauto].
                exists 1%nat.
                simpl.
                sets_unfold.
                right.
                unfold test_false.
                sets_unfold.
                tauto.
            --  right.
                exists 1%nat.
                simpl.
                sets_unfold.
                right.
                tauto.
Qed.

Lemma Split_crefine_nrm_While_aux {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr) (c : com),
    ((forall (vcnt : nat), Screfine_nrm (com2comlist c vcnt) c) ->
    (forall (vcnt : nat), 
        Screfine_nrm (com2comlist (CWhile e c) vcnt) (CWhile e c))).
Proof.
    intros.
    unfold com2comlist.
    simpl.
    unfold Screfine_nrm.
    intros s1 ss1 ss3.
    pose proof eval_comlist_seq_nrm (ex2pre e vcnt)
    [SCWhile (ex2se e vcnt)
    (com2pre c (nat_add vcnt (length (ex2pre e vcnt))) ++
     com2sc c (nat_add vcnt (length (ex2pre e vcnt))) ++
     ex2pre e vcnt)]
        ss1 ss3.
    destruct H0.
    intros.
    pose proof H0 H2.
    sets_unfold in H4.
    revert H4.
    simpl.
    sets_unfold.
    intros.
    destruct H4 as [ss2].
    destruct H4.
    destruct H5.
    destruct H5.
    rewrite H6 in H5.
    destruct H5 as [n].
    pose proof correspond_prop2 e vcnt s1 ss1 ss2 H3 H4.
    assert (exists ss209 : state,
    correspond s1 ss209 /\
    (Seval_comlist (ex2pre e vcnt)).(nrm) ss209 ss2).
    {
        exists ss1.
        tauto.
    }
    pose proof split_while_nrm n c e s1 ss2 ss3 H H7 vcnt H8 H5.
    tauto.
Qed.

Lemma split_while_err {NameX : Names} {NPX : NamesProperty}:
    forall (n0 : nat) (c : com) (e : expr) (s11 ss21 : state),
        (forall (vcnt : nat), Screfine (com2comlist c vcnt) c) ->
        correspond s11 ss21 ->
        (forall (vcnt : nat),
        (exists (ss209 : state), correspond s11 ss209 /\
        (Seval_comlist (ex2pre e vcnt)).(nrm) ss209 ss21) ->
        boundedLB_err (Seval_r (ex2se e vcnt))
        (Seval_comlist
            (com2pre c (nat_add vcnt (length (ex2pre e vcnt))) ++
            com2sc c (nat_add vcnt (length (ex2pre e vcnt))) ++
            ex2pre e vcnt))
        n0 ss21
        -> (exists i : nat, boundedLB_err (eval_r e) (eval_com c) i s11))
    .
Proof.
    induction n0.
        + simpl.
          sets_unfold.
          intros.
          tauto.
        + simpl.
          sets_unfold.
          intros c e0 ? ? Hv ? vcnt0 ? ?.
          destruct H0 as [ss209].
          destruct H1.
          - destruct H1 as [ss22].
            destruct H1.
            pose proof Split_Serefine_nrm e0 vcnt0 as H200.
            unfold Serefine_nrm, Serefine_nrm_r in H200.
            destruct H200 as [H300 H200].
            unfold test_true in H1.
            sets_unfold in H1.
            destruct H1 as [H1 H13].
            destruct H1.
            destruct H1 as [H1 H203].
            destruct H0 as [H0 H202].
            pose proof H200 s11 ss209 ss21 x H0 H202 H1 as H205.
            destruct H205 as [H205 | H205]; [|
                exists 1%nat;
                simpl;
                sets_unfold;
                right;
                tauto].
            destruct H2.
            * 
            destruct H2 as [ss25].
            destruct H2.
            pose proof eval_comlist_seq_nrm 
                (com2pre c (nat_add vcnt0 (length (ex2pre e0 vcnt0)))) 
                (com2sc c (nat_add vcnt0 (length (ex2pre e0 vcnt0))) ++
                ex2pre e0 vcnt0)
                ss22 ss25.
            destruct H4.
            pose proof H4 H2.
            sets_unfold in H6.
            destruct H6 as [ss23].
            destruct H6.
            pose proof eval_comlist_seq_nrm
                (com2sc c (nat_add vcnt0 (length (ex2pre e0 vcnt0))))
                (ex2pre e0 vcnt0)
                ss23 ss25.
            destruct H8.
            pose proof H8 H7.
            sets_unfold in H10.
            destruct H10 as [ss24].
            destruct H10.
            pose proof Hv as H101.
            unfold Screfine_nrm, com2comlist in Hv.
            assert ((Seval_comlist
            (com2pre c (nat_add vcnt0 (length (ex2pre e0 vcnt0))) ++
             com2sc c (nat_add vcnt0 (length (ex2pre e0 vcnt0))))).(nrm)
            ss22 ss24).
            {
                pose proof eval_comlist_seq_nrm 
                (com2pre c (nat_add vcnt0 (length (ex2pre e0 vcnt0))))
                (com2sc c (nat_add vcnt0 (length (ex2pre e0 vcnt0)))) 
                ss22 ss24.
                destruct H12.
                sets_unfold in H14.
                apply H14.
                exists ss23.
                tauto.
            }
            rewrite H13 in H.
            pose proof Hv (nat_add vcnt0 (length (ex2pre e0 vcnt0))) as [H110 H111 H112].
            pose proof H110 s11 ss22 ss24 H12 H.
            destruct H14.
            **  destruct H14 as [s12].
                destruct H14.
                pose proof correspond_prop2 e0 vcnt0 s12 ss24 ss25 H15 H11.
                pose proof IHn0 c e0 s12 ss25 H101 H16.
                assert (exists (ss209 : state),
                correspond s12 ss209 /\ (Seval_comlist (ex2pre e0 vcnt0)).(nrm) ss209 ss25).
                {
                    exists ss24.
                    tauto.
                }
                pose proof H17 vcnt0 H18 H3.
                destruct H19 as [n].
                exists (S n).
                simpl.
                sets_unfold.
                left.
                exists s11.
                split.
                unfold test_true.
                simpl.
                sets_unfold.
                split; [|tauto].
                exists x.
                tauto.
                left.
                exists s12.
                tauto.
            **  exists 1%nat.
                simpl.
                sets_unfold.
                pose proof Split_Serefine_nrm e0 vcnt0.
                unfold Serefine_nrm, Serefine_nrm_r in H15.
                destruct H15.
                pose proof H16 s11 ss209 ss21 x H0 H202 H1.
                destruct H17; [|tauto].
                left.
                exists s11.
                split.
                unfold test_true.
                simpl.
                sets_unfold.
                split; [|tauto].
                exists x.
                tauto.
                tauto.
          * 
          pose proof preandsc (nat_add vcnt0 (length (ex2pre e0 vcnt0))) c.
          pose proof seq_asso (com2pre c (nat_add vcnt0 (length (ex2pre e0 vcnt0))))
            (com2sc c (nat_add vcnt0 (length (ex2pre e0 vcnt0))))
            (ex2pre e0 vcnt0).
          rewrite <- H4 in H2.
          rewrite H3 in H2.
          pose proof eval_comlist_seq_err
              ((com2pre c (nat_add vcnt0 (length (ex2pre e0 vcnt0)))) ++
              com2sc c (nat_add vcnt0 (length (ex2pre e0 vcnt0))))
              (ex2pre e0 vcnt0)
              ss22.
          destruct H5.
          pose proof H5 H2.
          destruct H7.
          **
          rewrite H3 in H7.
          pose proof Hv (nat_add vcnt0 (length (ex2pre e0 vcnt0))) as [H110 H111 H112].
          unfold Screfine_err in H111.
          pose proof H.
          rewrite H13 in H8.
          pose proof H111 s11 ss22 H7 H8.
          exists 1%nat.
          simpl.
          sets_unfold.
          left.
          exists s11.
          unfold test_true.
          simpl.
          sets_unfold.
          split.
          split; [|tauto].
          exists x.
          tauto.
          tauto.
          **
          sets_unfold in H7.
          destruct H7 as [ss24].
          destruct H7.
          rewrite H3 in H7.
          pose proof Hv (nat_add vcnt0 (length (ex2pre e0 vcnt0))) as [H110 H111 H112].
          unfold Screfine_nrm in H110.
          pose proof H.
          rewrite H13 in H9.
          pose proof H110 s11 ss22 ss24 H7 H9.
          pose proof Split_Serefine_err e0 vcnt0 as [H120 [H121 H122]].
          unfold Serefine_err1 in H120.
          destruct H10.
          ***
          destruct H10 as [s12].
          destruct H10.
          exists 2%nat.
          simpl.
          sets_unfold.
          left.
          exists s11.
          unfold test_true.
          simpl.
          sets_unfold.
          split.
          split; [|tauto].
          exists x.
          tauto.
          left.
          exists s12.
          split; [tauto|].
          pose proof H120 s12 ss24 H11 H8 as [? ?].
          tauto.
          ***
          exists 1%nat.
          simpl.
          unfold test_true.
          simpl.
          sets_unfold.
          left.
          exists s11.
          split.
          split; [|tauto].
          exists x.
          tauto.
          tauto.
          - pose proof Split_Serefine_err e0 vcnt0 as [H100 [H101 H102]].
            unfold Serefine_err2_r in H102.
            destruct H0.
            pose proof H102 s11 ss209 ss21 H0 H2 H1.
            exists 1%nat.
            simpl.
            sets_unfold.
            tauto.
Qed.

Lemma Split_crefine_err_While_aux {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr) (c : com),
    ((forall (vcnt : nat), Screfine (com2comlist c vcnt) c) ->
    (forall (vcnt : nat), 
        Screfine_err (com2comlist (CWhile e c) vcnt) (CWhile e c))).
Proof.
    intros.
    unfold com2comlist.
    simpl.
    unfold Screfine_err.
    intros s1 ss1.
    pose proof eval_comlist_seq_err (ex2pre e vcnt)
    [SCWhile (ex2se e vcnt)
    (com2pre c (nat_add vcnt (length (ex2pre e vcnt))) ++
     com2sc c (nat_add vcnt (length (ex2pre e vcnt))) ++
     ex2pre e vcnt)]
        ss1.
    destruct H0.
    intros.
    pose proof H0 H2.
    sets_unfold in H4.
    revert H4.
    simpl.
    sets_unfold.
    intros.
    destruct H4 as [H4 | H4].
    + 
    exists 1%nat.
    simpl.
    sets_unfold.
    pose proof Split_Serefine_err e vcnt as [? [? ?]].
    unfold Serefine_err1 in H5.
    pose proof H5 s1 ss1 H3 H4 as [? ?].
    tauto.
    + 
    destruct H4 as [ss2].
    destruct H4.
    destruct H5 as [H5 | H5].
    - 
    destruct H5 as [n].
    pose proof correspond_prop2 e vcnt s1 ss1 ss2 H3 H4.
    assert (exists ss209 : state,
    correspond s1 ss209 /\
    (Seval_comlist (ex2pre e vcnt)).(nrm) ss209 ss2).
    {
        exists ss1.
        tauto.
    }
    pose proof split_while_err n c e s1 ss2 H H6 vcnt H7 H5.
    tauto.
    - destruct H5.
      destruct H5.
      tauto.
Qed.

Lemma test_true_unfold: 
  forall (D0 : EDenote) (s1 s2 : state),
    test_true D0 s1 s2 ->
    s1 = s2 /\ (exists i : int64, D0.(nrm) s1 i /\ Int64.signed i <> 0).
Proof.
  intros ? ? ?.
  unfold test_true.
  sets_unfold.
  tauto.
Qed.

Fixpoint spe_inf
           (e: EDenote)
           (pre c : CDenote)
           (n: nat): state -> state -> Prop :=
  match n with
  | O => Rels.id
  | S n0 =>
     (pre.(nrm) ∘ test_true e ∘ c.(nrm) ∘ (spe_inf e pre c n0))
  end.

Definition construct_chain {NameX : Names} {NPX : NamesProperty}
  (e : expr) (c : com) (vcnt : nat) (s1 ss10 : state): state -> Prop :=
  (fun x => exists (i : nat) (ssn0 ssn1 : state), 
    spe_inf (Seval_r (ex2se e vcnt)) (Seval_comlist (ex2pre e vcnt))
      (Seval_comlist (com2comlist c (nat_add vcnt (length (ex2pre e vcnt)))))
      i ss10 ssn0  
    /\ correspond x ssn0 /\ (Seval_comlist (ex2pre e vcnt)).(nrm) ssn0 ssn1 
    /\ ~ (exists m : nat, boundedLB_err (eval_r e) (eval_com c) m x)
    /\ (Sets.general_union (is_inf (Seval_r (ex2se e vcnt))
       (Seval_comlist
          (com2comlist c (nat_add vcnt (length (ex2pre e vcnt))) ++
           ex2pre e vcnt)))) ssn1).

Lemma is_inf_append {NameX : Names} {NPX : NamesProperty}:
  forall (e : expr) (c : com) (vcnt n : nat) (ss10 ssn0 ssn1 : state),
    Sets.general_union
    (is_inf (Seval_r (ex2se e vcnt))
       (Seval_comlist
          (com2comlist c
             (nat_add vcnt (length (ex2pre e vcnt))) ++
           ex2pre e vcnt))) ssn1
    ->  spe_inf (Seval_r (ex2se e vcnt)) (Seval_comlist (ex2pre e vcnt))
    (Seval_comlist (com2comlist c (nat_add vcnt (length (ex2pre e vcnt)))))
    n ss10 ssn0
    ->  (Seval_comlist (ex2pre e vcnt)).(nrm) ssn0 ssn1
    ->  (exists (ss11 : state), 
        (Seval_comlist (ex2pre e vcnt)).(nrm) ss10 ss11
        /\ Sets.general_union
            (is_inf (Seval_r (ex2se e vcnt))
            (Seval_comlist
              (com2comlist c
              (nat_add vcnt (length (ex2pre e vcnt))) ++
              ex2pre e vcnt))) ss11).
Proof.
  induction n.
  + simpl.
    sets_unfold.
    intros.
    rewrite H0.
    exists ssn1.
    tauto.
  + simpl.
    sets_unfold.
    intros.
    destruct H0 as [ss11].
    destruct H0.
    destruct H2 as [ss12].
    destruct H2.
    pose proof test_true_unfold (Seval_r (ex2se e vcnt)) ss11 ss12 H2.
    destruct H4.
    rewrite <- H4 in H2, H3.
    destruct H5.
    destruct H5.
    destruct H3 as [ss20].
    destruct H3.
    sets_unfold in IHn.
    pose proof IHn ss20 ssn0 ssn1 H H7 H1.
    exists ss11.
    split; [tauto|].
    destruct H8 as [ss21].
    destruct H8.
    destruct H9.
    exists (fun x => x0 x \/ x = ss11).
    revert H9.
    unfold is_inf.
    sets_unfold.
    intros.
    split; [|tauto].
    intros.
    destruct H10.
    ++
    destruct H9.
    pose proof H9 a H10.
    destruct H12.
    destruct H12.
    exists x1.
    split; [tauto|].
    destruct H13.
    +++
    left.
    destruct H13.
    exists x2.
    tauto.
    +++
    tauto.
    ++
    rewrite H10.
    exists ss11.
    split; [tauto|].
    left.
    exists ss21.
    split; [|tauto].
    pose proof eval_comlist_seq_nrm 
      (com2comlist c (nat_add vcnt (length (ex2pre e vcnt))))
      (ex2pre e vcnt) ss11 ss21.
    destruct H11.
    sets_unfold in H12.
    apply H12.
    exists ss20.
    tauto.
Qed.


Lemma split_while_inf {NameX : Names} {NPX : NamesProperty}:
  forall (e : expr) (c : com),
    (forall (vcnt : nat), Screfine (com2comlist c vcnt) c) ->
      forall (vcnt : nat) (s1 ss11 : state),
      (exists (ss10 : state), correspond s1 ss10 
        /\ (Seval_comlist (ex2pre e vcnt)).(nrm) ss10 ss11) ->
      (Seval_comlist
          [SCWhile (ex2se e vcnt)
            (com2pre c (nat_add vcnt (length (ex2pre e vcnt))) ++
              com2sc c (nat_add vcnt (length (ex2pre e vcnt))) ++
              ex2pre e vcnt)]).(inf) ss11 ->
      (eval_com (CWhile e c)).(inf) s1 \/
      (eval_com (CWhile e c)).(err) s1
      .
Proof.
    simpl.
    sets_unfold.
    intros.
    destruct H0 as [ss10].
    destruct H0 as [H0 H90].
    pose proof correspond_prop2 e vcnt s1 ss10 ss11 H0 H90.
    pose proof H (nat_add vcnt (length (ex2pre e vcnt))) as [H200 H201 H202].
    unfold Screfine_nrm in H200.
    unfold Screfine_err in H201.
    unfold Screfine_inf in H202.
    pose proof seq_asso 
      (com2pre c (nat_add vcnt (length (ex2pre e vcnt))))
      (com2sc c (nat_add vcnt (length (ex2pre e vcnt))))
      (ex2pre e vcnt).
    pose proof preandsc (nat_add vcnt (length (ex2pre e vcnt))) c.
    rewrite <- H3 in H1.
    rewrite H4 in H1.
    destruct H1 as [H1 | H1]; [|destruct H1; destruct H1; tauto].
    pose proof classic (exists i : nat, boundedLB_err (eval_r e) (eval_com c) i s1) as H6.
    destruct H6 as [H6 | H6]; [tauto|].
    left.
    pose proof Split_Serefine_nrm e vcnt as [Hl Hr].
    unfold Serefine_nrm_r in Hr.
    exists (construct_chain e c vcnt s1 ss10).
    unfold construct_chain.
    split.
    *
    intros sn H7.
    destruct H7 as [n H7].
    revert s1 ss10 ss11 H0 H90 H1 H2 H6 H7.
    induction n.
    +
    simpl.
    sets_unfold.
    intros.
    destruct H7 as [ssn0 [ssn1]].
    destruct H5.
    rewrite H5.
    destruct H7.
    destruct H8.
    destruct H9 as [H20].
    destruct H9.
    revert H9.
    unfold is_inf.
    sets_unfold.
    intros.
    destruct H9.
    pose proof H9 ssn1 H10.
    destruct H11 as [ssn2].
    destruct H11.
    pose proof test_true_unfold (Seval_r (ex2se e vcnt)) ssn1 ssn2 H11.
    destruct H13.
    rewrite <- H13 in H11, H12.
    destruct H14.
    destruct H14.
    pose proof Hr sn ssn0 ssn1 x0 H7 H8 H14.
    destruct H16.
    ++
    assert (test_true (eval_r e) sn sn).
    {
      unfold test_true; sets_unfold; split; [|tauto].
      exists x0.
      tauto.
    }
    exists sn.
    split; [tauto|].
    pose proof correspond_prop2 e vcnt sn ssn0 ssn1 H7 H8 as H25.
    destruct H12.
    +++
    destruct H12 as [ssn5].
    destruct H12.
    pose proof eval_comlist_seq_nrm 
      (com2comlist c (nat_add vcnt (length (ex2pre e vcnt))))
      (ex2pre e vcnt) ssn1 ssn5.
    destruct H19.
    pose proof H19 H12.
    sets_unfold in H22.
    destruct H22 as [ssn4].
    destruct H22.
    pose proof H200 sn ssn1 ssn4 H22 H25.
    destruct H24.
    ++++
    destruct H24 as [s2].
    destruct H24.
    left.
    exists s2.
    split; [tauto|].
    exists 1%nat, ssn4, ssn5.
    simpl.
    sets_unfold.
    split.
    -
    exists ssn1.
    split; [tauto|].
    exists ssn1.
    split; [tauto|].
    exists ssn4.
    tauto.
    -
    split; [tauto|].
    split; [tauto|].
    assert (~ (exists m : nat, boundedLB_err (eval_r e) (eval_com c) m s2)).
    {
      pose proof classic (exists m : nat, boundedLB_err (eval_r e) (eval_com c) m s2).
      destruct H27; [|tauto].
      assert (exists m : nat, boundedLB_err (eval_r e) (eval_com c) m sn).
      {
        destruct H27 as [m].
        exists (S m).
        simpl.
        sets_unfold.
        left.
        exists sn. 
        split; [tauto|].
        left.
        exists s2.
        tauto.
      }
      tauto.
    }
    split; [tauto|].
    exists x.
    split; [|tauto].
    tauto.
    ++++
    assert (exists m : nat, boundedLB_err (eval_r e) (eval_com c) m sn).
    {
      exists 1%nat.
      simpl.
      sets_unfold.
      left.
      exists sn.
      tauto. 
    }
    tauto.
    +++
    pose proof eval_comlist_seq_inf 
      (com2comlist c (nat_add vcnt (length (ex2pre e vcnt))))
      (ex2pre e vcnt) ssn1.
    destruct H18.
    pose proof H18 H12.
    destruct H21.
    ++++
    pose proof H202 sn ssn1 H21 H25.
    destruct H22; [tauto|].
    assert (exists m : nat, boundedLB_err (eval_r e) (eval_com c) m sn).
    {
      exists 1%nat.
      simpl.
      sets_unfold.
      left.
      exists sn.
      tauto. 
    }
    tauto.
    ++++
    sets_unfold in H21.
    destruct H21 as [ssn4].
    destruct H21.
    pose proof never_inf e vcnt ssn4 H22.
    tauto.
    ++
    assert (exists m : nat, boundedLB_err (eval_r e) (eval_com c) m sn).
    {
      exists 1%nat.
      simpl.
      sets_unfold.
      tauto.
    }
    tauto.
    +
    simpl.
    sets_unfold.
    intros.
    destruct H1.
    destruct H1.
    destruct H7 as [ssn0 [ssn1]].
    destruct H7.
    destruct H8 as [? [? ?]].
    destruct H7 as [ss18].
    destruct H7.
    destruct H11 as [ss19].
    destruct H11.
    destruct H12 as [ss20].
    destruct H12.
    destruct H10 as [H40 H10].
    pose proof correspond_prop2 e vcnt s1 ss10 ss18 H0 H7.
    pose proof test_true_unfold (Seval_r (ex2se e vcnt)) ss18 ss19 H11.
    destruct H15 as [? [? ?]].
    destruct H16.
    rewrite <- H15 in H11, H12.
    pose proof H200 s1 ss18 ss20 H12 H14.
    assert (test_true (eval_r e) s1 s1).
    {
      pose proof Hr s1 ss10 ss18 x0 H0 H7 H16.
      unfold test_true; sets_unfold; split; [|tauto].
      destruct H19.
      +
      exists x0.
      tauto.
      +
      assert (exists i : nat, boundedLB_err (eval_r e) (eval_com c) i s1).
      {
        exists 1%nat.
        simpl.
        sets_unfold.
        tauto.
      }
      tauto.
    }
    destruct H18.
    ++
    destruct H18 as [s2].
    destruct H18.
    destruct H10.
    destruct H10.
    assert (Sets.general_union
    (is_inf (Seval_r (ex2se e vcnt))
       (Seval_comlist
          (com2comlist c
             (nat_add vcnt (length (ex2pre e vcnt))) ++
           ex2pre e vcnt))) ssn1).
    {
      sets_unfold.
      exists x1.
      tauto.
    }
    pose proof is_inf_append e c vcnt n ss20 ssn0 ssn1 H22 H13 H9.
    destruct H23 as [ss21].
    destruct H23.
    pose proof correspond_prop2 e vcnt s2 ss20 ss21 H20 H23.
    sets_unfold in H24.
    assert (~(exists i : nat, boundedLB_err (eval_r e) (eval_com c) i s2)).
    {
      pose proof classic (exists i : nat, boundedLB_err (eval_r e) (eval_com c) i s2).
      destruct H26; [|tauto].
      destruct H26 as [i].
      assert (exists i : nat, boundedLB_err (eval_r e) (eval_com c) i s1).
      {
        exists (S i).
        simpl.
        sets_unfold.
        left.
        exists s1.
        split; [tauto|].
        left.
        exists s2.
        tauto.
      }
      tauto.
    }
    assert (exists ssn0 ssn1 : state,
    spe_inf (Seval_r (ex2se e vcnt))
      (Seval_comlist (ex2pre e vcnt))
      (Seval_comlist
         (com2comlist c
            (nat_add vcnt (length (ex2pre e vcnt))))) n ss20
      ssn0 /\
    correspond sn ssn0 /\
    (Seval_comlist (ex2pre e vcnt)).(nrm) ssn0 ssn1 /\
    ~ (exists m : nat, boundedLB_err (eval_r e) (eval_com c) m sn) /\
    Sets.general_union
      (is_inf (Seval_r (ex2se e vcnt))
         (Seval_comlist
            (com2comlist c
               (nat_add vcnt (length (ex2pre e vcnt))) ++
             ex2pre e vcnt))) ssn1).
    {
      exists ssn0, ssn1.
      tauto.
    }
    pose proof IHn s2 ss20 ss21 H20 H23 H24 H25 H26 H27.
    sets_unfold in H28.
    destruct H28.
    destruct H28.
    pose proof test_true_unfold (eval_r e) sn x2 H28.
    destruct H30.
    destruct H31.
    destruct H31.
    rewrite <- H30 in H28, H29.
    exists sn.
    split; [tauto|].
    destruct H29; [|tauto].
    destruct H29 as [sm].
    destruct H29.
    left.
    exists sm. 
    split; [tauto|].
    destruct H33 as [i [ssm0 [ssm1]]].
    exists (S i), ssm0, ssm1.
    simpl.
    sets_unfold.
    split; [|tauto].
    exists ss18.
    split; [tauto|].
    exists ss18.
    split; [tauto|].
    exists ss20.
    tauto.
    ++
    assert (exists i : nat, boundedLB_err (eval_r e) (eval_com c) i s1).
    {
      exists 1%nat.
      simpl.
      sets_unfold.
      left.
      exists s1.
      tauto.
    }
    tauto.
    *
    exists 0%nat, ss10, ss11.
    simpl.
    sets_unfold.
    tauto.
Qed.

Lemma Split_crefine_inf_While_aux {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr) (c : com),
    ((forall (vcnt : nat), Screfine (com2comlist c vcnt) c) ->
    (forall (vcnt : nat), 
        Screfine_inf (com2comlist (CWhile e c) vcnt) (CWhile e c))).
Proof.
  unfold Screfine_inf.
  intros.
  unfold com2comlist, com2pre in H0.
  pose proof eval_comlist_seq_inf (ex2pre e vcnt) (com2sc (CWhile e c) vcnt) ss1.
  destruct H2.
  pose proof H2 H0.
  destruct H4.
  +
  pose proof never_inf e vcnt ss1 H4.
  tauto.
  +
  sets_unfold in H4.
  destruct H4 as [ss11].
  destruct H4.
  assert (exists (ss10 : state), correspond s1 ss10 
  /\ (Seval_comlist (ex2pre e vcnt)).(nrm) ss10 ss11).
  {
    exists ss1.
    tauto.
  }
  assert ((Seval_comlist
  [SCWhile (ex2se e vcnt)
    (com2pre c (nat_add vcnt (length (ex2pre e vcnt))) ++
      com2sc c (nat_add vcnt (length (ex2pre e vcnt))) ++
      ex2pre e vcnt)]).(inf) ss11).
  {
    revert H5.
    simpl.
    tauto.
  }
  pose proof split_while_inf e c H vcnt s1 ss11 H6 H7.
  tauto.
Qed.

Theorem Split_expr_crefine {NameX : Names} {NPX : NamesProperty}: 
    forall (c : com) (vcnt : nat),
        Screfine (com2comlist c vcnt) c.
Proof.
    intros c.
    induction c.
    + split.
      apply Split_crefine_nrm_Skip.
      apply Split_crefine_err_Skip.
      apply Split_crefine_inf_Skip.
    + split.
      intros.
      unfold Screfine_nrm.
      pose proof Split_crefine_nrm_AsgnVar vcnt x e.
      tauto.
      intros.
      unfold Screfine_err.
      pose proof Split_crefine_err_AsgnVar vcnt x e.
      tauto.
      intros.
      unfold Screfine_inf.
      pose proof Split_crefine_inf_AsgnVar vcnt x e.
      tauto.
    + split.
      intros.
      unfold Screfine_nrm.
      pose proof Split_crefine_nrm_AsgnDeref vcnt e1 e2.
      tauto.
      intros.
      unfold Screfine_err.
      pose proof Split_crefine_err_AsgnDeref vcnt e1 e2.
      tauto.
      intros.
      unfold Screfine_inf.
      pose proof Split_crefine_inf_AsgnDeref vcnt e1 e2.
      tauto.
    + split.
      assert (forall vcnt : nat, Screfine_nrm (com2comlist c1 vcnt) c1).
      {
        intros.
        pose proof IHc1 vcnt0 as [? ? ?].
        tauto.
      }
      assert (forall vcnt : nat, Screfine_nrm (com2comlist c2 vcnt) c2).
      {
        intros.
        pose proof IHc2 vcnt0 as [? ? ?].
        tauto.
      }
      pose proof Split_crefine_nrm_Seq_aux c1 c2 H H0 vcnt.
      tauto.
      pose proof Split_crefine_err_Seq_aux c1 c2 IHc1 IHc2 vcnt.
      tauto.
      pose proof Split_crefine_inf_Seq_aux c1 c2 IHc1 IHc2 vcnt.
      tauto.
    + split.
      assert (forall vcnt : nat, Screfine_nrm (com2comlist c1 vcnt) c1).
      {
        intros.
        pose proof IHc1 vcnt0 as [? ? ?].
        tauto.
      }
      assert (forall vcnt : nat, Screfine_nrm (com2comlist c2 vcnt) c2).
      {
        intros.
        pose proof IHc2 vcnt0 as [? ? ?].
        tauto.
      }
      pose proof Split_crefine_nrm_If_aux e c1 c2 H H0 vcnt.
      tauto.
      pose proof Split_crefine_err_If_aux e c1 c2 IHc1 IHc2 vcnt.
      tauto.
      pose proof Split_crefine_inf_If_aux e c1 c2 IHc1 IHc2 vcnt.
      tauto.
    + split.
      assert (forall vcnt : nat, Screfine_nrm (com2comlist c vcnt) c).
      {
        intros.
        pose proof IHc vcnt0 as [? ? ?].
        tauto.
      }
      pose proof Split_crefine_nrm_While_aux e c H vcnt.
      tauto.
      pose proof Split_crefine_err_While_aux e c IHc vcnt.
      tauto.
      pose proof Split_crefine_inf_While_aux e c IHc vcnt.
      tauto.
Qed.
