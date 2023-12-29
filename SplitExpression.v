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
    trans_prop2 : forall (x : nat) (y : nat) , (x = y) <-> (nat2Sname x = nat2Sname y);
    trans_prop3 : forall (x : var_name) (y : nat) , name2Sname x <> nat2Sname y;
}.


Definition correspond {NameX : Names} (s ss : state) : Prop :=
    (forall (x : var_name) (i : int64), s.(env) x = i <-> ss.(env) (name2Sname x) = i)
    /\ (forall (a : int64) (v : val), s.(mem) a = Some v -> ss.(mem) a = Some v)
    /\ (forall (vcnt : nat), s.(mem) (ss.(env) (nat2Sname vcnt)) = None 
                            /\ ss.(mem) (ss.(env) (nat2Sname vcnt)) <> None).

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
            (ex2pre e1 (S vcnt)) ++
            [(SCIf (ex2se e1 (S vcnt)) 
                ((ex2pre e2 (nat_add (S vcnt) (length (ex2pre e1 (S vcnt)))))
                ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e2 (nat_add (S vcnt) (length (ex2pre e1 (S vcnt))))))])
                [(SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S vcnt)))])]
        | OOr =>
            (ex2pre e1 (S vcnt)) ++
            [(SCIf (ex2se e1 (S vcnt)) 
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
            ++ (ex2pre e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt))))))
            ++ [(SCAsgnVar (nat2Sname vcnt) (ex2se e1 (S (S vcnt))))]
            ++ [(SCAsgnVar (nat2Sname (S vcnt)) (ex2se e2 (nat_add (S (S vcnt)) (length (ex2pre e1 (S (S vcnt)))))))]
        end
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
            [(SCAsgnDeref (SEConst c) (genSEVar_n vcnt))]
        | EVar v, _ =>
            [(SCAsgnDeref (genSEVar v) (genSEVar_n vcnt))]   
        | _ , EConst c =>
            [(SCAsgnDeref (genSEVar_n vcnt) (SEConst c))]
        | _ , EVar v =>
            [(SCAsgnDeref (genSEVar_n vcnt) (genSEVar v))] 
        | _, _ =>
            [(SCAsgnDeref (genSEVar_n vcnt) (genSEVar_n (S vcnt)))]
        end
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
    forall (e : expr) (op : unop) (vcnt : nat),
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
    forall (e : expr) (vcnt : nat),
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
    forall (e : expr) (vcnt : nat),
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
    pose proof ex2pre_deref e vcnt.
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
    pose proof ex2pre_addrof e vcnt.
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
    pose proof ex2pre_unop e op vcnt.
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
    intros e op.
    pose proof ex2pre_unop e op.
    destruct e.
    + simpl; tauto.
    + simpl; tauto.
    + intros.
      pose proof H vcnt.
      rewrite H3 in H2.
      pose proof eval_comlist_seq_nrm 
        (ex2pre (EBinop op0 e1 e2) (S vcnt))
        [SCAsgnVar (nat2Sname vcnt) (ex2se (EBinop op0 e1 e2) (S vcnt))] ss1 ss2.
      destruct H4.
      pose proof H4 H2.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      pose proof H0 (S vcnt) s1 ss1 x H1 H6.
      pose proof correspond_prop1 vcnt (ex2se (EBinop op0 e1 e2) (S vcnt)) s1 x ss2 H8 H7.
      tauto.
    + intros.
      pose proof H vcnt.
      rewrite H3 in H2.
      pose proof eval_comlist_seq_nrm 
        (ex2pre (EUnop op0 e) (S vcnt))
        [SCAsgnVar (nat2Sname vcnt) (ex2se (EUnop op0 e) (S vcnt))] ss1 ss2.
      destruct H4.
      pose proof H4 H2.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      pose proof H0 (S vcnt) s1 ss1 x H1 H6.
      pose proof correspond_prop1 vcnt (ex2se (EUnop op0 e) (S vcnt)) s1 x ss2 H8 H7.
      tauto.
    + intros.
      pose proof H vcnt.
      rewrite H3 in H2.
      pose proof eval_comlist_seq_nrm 
        (ex2pre (EDeref e) (S vcnt))
        [SCAsgnVar (nat2Sname vcnt) (ex2se (EDeref e) (S vcnt))] ss1 ss2.
      destruct H4.
      pose proof H4 H2.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      pose proof H0 (S vcnt) s1 ss1 x H1 H6.
      pose proof correspond_prop1 vcnt (ex2se (EDeref e) (S vcnt)) s1 x ss2 H8 H7.
      tauto.
    + intros.
      pose proof H vcnt.
      rewrite H3 in H2.
      pose proof eval_comlist_seq_nrm 
        (ex2pre (EAddrOf e) (S vcnt))
        [SCAsgnVar (nat2Sname vcnt) (ex2se (EAddrOf e) (S vcnt))] ss1 ss2.
      destruct H4.
      pose proof H4 H2.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      pose proof H0 (S vcnt) s1 ss1 x H1 H6.
      pose proof correspond_prop1 vcnt (ex2se (EAddrOf e) (S vcnt)) s1 x ss2 H8 H7.
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
    intros e.
    pose proof ex2pre_deref e.
    destruct e.
    + simpl; tauto.
    + simpl; tauto.
    + intros.
      pose proof H vcnt.
      rewrite H3 in H2.
      pose proof eval_comlist_seq_nrm 
        (ex2pre (EBinop op e1 e2) (S vcnt))
        [SCAsgnVar (nat2Sname vcnt) (ex2se (EBinop op e1 e2) (S vcnt))] ss1 ss2.
      destruct H4.
      pose proof H4 H2.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      pose proof H0 (S vcnt) s1 ss1 x H1 H6.
      pose proof correspond_prop1 vcnt (ex2se (EBinop op e1 e2) (S vcnt)) s1 x ss2 H8 H7.
      tauto.
    + intros.
      pose proof H vcnt.
      rewrite H3 in H2.
      pose proof eval_comlist_seq_nrm 
        (ex2pre (EUnop op e) (S vcnt))
        [SCAsgnVar (nat2Sname vcnt) (ex2se (EUnop op e) (S vcnt))] ss1 ss2.
      destruct H4.
      pose proof H4 H2.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      pose proof H0 (S vcnt) s1 ss1 x H1 H6.
      pose proof correspond_prop1 vcnt (ex2se (EUnop op e) (S vcnt)) s1 x ss2 H8 H7.
      tauto.
    + intros.
      pose proof H vcnt.
      rewrite H3 in H2.
      pose proof eval_comlist_seq_nrm 
        (ex2pre (EDeref e) (S vcnt))
        [SCAsgnVar (nat2Sname vcnt) (ex2se (EDeref e) (S vcnt))] ss1 ss2.
      destruct H4.
      pose proof H4 H2.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      pose proof H0 (S vcnt) s1 ss1 x H1 H6.
      pose proof correspond_prop1 vcnt (ex2se (EDeref e) (S vcnt)) s1 x ss2 H8 H7.
      tauto.
    + intros.
      pose proof H vcnt.
      rewrite H3 in H2.
      pose proof eval_comlist_seq_nrm 
        (ex2pre (EAddrOf e) (S vcnt))
        [SCAsgnVar (nat2Sname vcnt) (ex2se (EAddrOf e) (S vcnt))] ss1 ss2.
      destruct H4.
      pose proof H4 H2.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      pose proof H0 (S vcnt) s1 ss1 x H1 H6.
      pose proof correspond_prop1 vcnt (ex2se (EAddrOf e) (S vcnt)) s1 x ss2 H8 H7.
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
    pose proof ex2pre_addrof e.
    destruct e.
    + simpl; tauto.
    + simpl; tauto.
    + intros.
      pose proof H vcnt.
      rewrite H3 in H2.
      pose proof eval_comlist_seq_nrm 
        (ex2pre (EBinop op e1 e2) (S vcnt))
        [SCAsgnVar (nat2Sname vcnt) (ex2se (EBinop op e1 e2) (S vcnt))] ss1 ss2.
      destruct H4.
      pose proof H4 H2.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      pose proof H0 (S vcnt) s1 ss1 x H1 H6.
      pose proof correspond_prop1 vcnt (ex2se (EBinop op e1 e2) (S vcnt)) s1 x ss2 H8 H7.
      tauto.
    + intros.
      pose proof H vcnt.
      rewrite H3 in H2.
      pose proof eval_comlist_seq_nrm 
        (ex2pre (EUnop op e) (S vcnt))
        [SCAsgnVar (nat2Sname vcnt) (ex2se (EUnop op e) (S vcnt))] ss1 ss2.
      destruct H4.
      pose proof H4 H2.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      pose proof H0 (S vcnt) s1 ss1 x H1 H6.
      pose proof correspond_prop1 vcnt (ex2se (EUnop op e) (S vcnt)) s1 x ss2 H8 H7.
      tauto.
    + intros.
      pose proof H vcnt.
      rewrite H3 in H2.
      pose proof eval_comlist_seq_nrm 
        (ex2pre (EDeref e) (S vcnt))
        [SCAsgnVar (nat2Sname vcnt) (ex2se (EDeref e) (S vcnt))] ss1 ss2.
      destruct H4.
      pose proof H4 H2.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      pose proof H0 (S vcnt) s1 ss1 x H1 H6.
      pose proof correspond_prop1 vcnt (ex2se (EDeref e) (S vcnt)) s1 x ss2 H8 H7.
      tauto.
    + intros.
      pose proof H vcnt.
      rewrite H3 in H2.
      pose proof eval_comlist_seq_nrm 
        (ex2pre (EAddrOf e) (S vcnt))
        [SCAsgnVar (nat2Sname vcnt) (ex2se (EAddrOf e) (S vcnt))] ss1 ss2.
      destruct H4.
      pose proof H4 H2.
      sets_unfold in H6.
      destruct H6.
      destruct H6.
      pose proof H0 (S vcnt) s1 ss1 x H1 H6.
      pose proof correspond_prop1 vcnt (ex2se (EAddrOf e) (S vcnt)) s1 x ss2 H8 H7.
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
Admitted.


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
    forall (e : expr) (vcnt : nat) (s2 s3 : state),
    match e with
    | EConst c => True
    | EVar x => True
    | _ => (Seval_comlist
        [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))]).(nrm) s2 s3
        -> (Seval_r (genSECV vcnt)).(nrm) s3 ⊆ (Seval_r (ex2se e (S vcnt))).(nrm) s2
    end.
Proof.
    intros.
    unfold Seval_comlist, seq_sem, asgn_var_sem, asgn_deref_sem, asgn_deref_sem_nrm, skip_sem, CDenote.nrm.
    unfold var_sem_l.
    simpl.
    sets_unfold.
    destruct e.
    + tauto.
    + tauto.
    + unfold deref_sem_nrm.
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
    + unfold deref_sem_nrm.
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
    + unfold deref_sem_nrm.
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
    + unfold deref_sem_nrm.
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
    forall (e : expr) (vcnt : nat) (s ss2 : state),
    match e with
    | EConst c => True
    | EVar x => True
    | _ =>
        correspond s ss2 -> 
        (Seval_comlist
        [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))]).(err) ss2
        -> (Seval_r (ex2se e (S vcnt))).(err) ss2
    end.
Proof.
    intros.
    unfold Seval_comlist, seq_sem, asgn_var_sem, asgn_deref_sem, skip_sem, asgn_deref_sem_nrm, asgn_deref_sem_err,
        CDenote.nrm, CDenote.err, var_sem_l.
    sets_unfold.
    destruct e.
    + tauto.
    + tauto.
    + unfold correspond.
      intros H0 H.
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
    + unfold correspond.
      intros H0 H.
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
    + unfold correspond.
      intros H0 H.
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
    + unfold correspond.
      intros H0 H.
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

Lemma Split_Serefine_nrm_r_deref {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr),
    (forall (vcnt : nat), Serefine_nrm_l (ex2pre e vcnt) (ex2se e vcnt) e)
    -> 
    (forall (vcnt : nat), Serefine_nrm_r (ex2pre e vcnt) (ex2se e vcnt) e)
    ->
    forall (vcnt : nat), Serefine_nrm_r (ex2pre (EDeref e) vcnt) (ex2se (EDeref e) vcnt) (EDeref e).
Proof.
    unfold Serefine_nrm_r.
    intros e IHel IHe vcnt s1 ss1 ss3 a ? ? ?.
    pose proof midstate_deref_nrm e vcnt ss1 ss3 H0 as Hm.
    pose proof asgn_vcnt_ex2se_nrm_prop e vcnt as Hp.
    sets_unfold in Hp.
    pose proof ex2se_deref e vcnt as Hd.
    pose proof deref4 e vcnt ss3 a H1 as Hd4.
    pose proof deref7 e vcnt as Hd7.
    pose proof correspond_prop1 as Hc1.
    pose proof correspond_prop2 as Hc2.
    pose proof Hc1 vcnt (ex2se e (S vcnt)) as Hc1.
    pose proof Hc2 e as Hc2.
    destruct e.
    + revert H H0 H1.
      unfold correspond.
      simpl.
      sets_unfold.
      unfold deref_sem_nrm.
      intros.
      destruct H1.
      pose proof mem_split s1 x.
      destruct H2.
      - left.
        destruct H2 as [v].
        exists x.
        split.
        tauto.
        destruct H1.
        rewrite <- H0 in H3.
        destruct H.
        destruct H4.
        pose proof H4 x v H2.
        rewrite H2.
        rewrite <- H6.
        tauto.
      - right.
        right.
        unfold deref_sem_err.
        exists x.
        split.
        destruct H1.
        tauto.
        left.
        tauto.
    + revert H H0 H1.
      simpl.
      sets_unfold.
      intros H H1.
      rewrite H1 in H.
      pose proof deref_nrm_prop1 s1 ss3 x a H.
      revert H0.
      simpl.
      sets_unfold.
      tauto.
    + destruct Hm as [ss2].
      destruct H2.
      pose proof Hp ss2 ss3 H3. 
      pose proof Hd4 Hd as Hd4.
      destruct Hd4.
      pose proof H4 x H5.
      pose proof Hc2 (S vcnt) s1 ss1 ss2 H H2.
      pose proof Hc1 s1 ss2 ss3 H7 H3.
      pose proof IHe (S vcnt) s1 ss1 ss2 x H H2 H6.
      rewrite Hd in H1.
      pose proof Hd7 x a s1 ss3.
      tauto.
    + destruct Hm as [ss2].
      destruct H2.
      pose proof Hp ss2 ss3 H3. 
      pose proof Hd4 Hd as Hd4.
      destruct Hd4.
      pose proof H4 x H5.
      pose proof Hc2 (S vcnt) s1 ss1 ss2 H H2.
      pose proof Hc1 s1 ss2 ss3 H7 H3.
      pose proof IHe (S vcnt) s1 ss1 ss2 x H H2 H6.
      rewrite Hd in H1.
      pose proof Hd7 x a s1 ss3.
      tauto.
    + destruct Hm as [ss2].
      destruct H2.
      pose proof Hp ss2 ss3 H3. 
      pose proof Hd4 Hd as Hd4.
      destruct Hd4.
      pose proof H4 x H5.
      pose proof Hc2 (S vcnt) s1 ss1 ss2 H H2.
      pose proof Hc1 s1 ss2 ss3 H7 H3.
      pose proof IHe (S vcnt) s1 ss1 ss2 x H H2 H6.
      rewrite Hd in H1.
      pose proof Hd7 x a s1 ss3.
      tauto.
    + destruct Hm as [ss2].
      destruct H2.
      pose proof Hp ss2 ss3 H3. 
      pose proof Hd4 Hd as Hd4.
      destruct Hd4.
      pose proof H4 x H5.
      pose proof Hc2 (S vcnt) s1 ss1 ss2 H H2.
      pose proof Hc1 s1 ss2 ss3 H7 H3.
      pose proof IHe (S vcnt) s1 ss1 ss2 x H H2 H6.
      rewrite Hd in H1.
      pose proof Hd7 x a s1 ss3.
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
    intros e IHel IHe vcnt s1 ss1 ss3 a ? ? ?.
    pose proof midstate_deref_nrm e vcnt ss1 ss3 H0 as Hm.
    pose proof correspond_prop1 as Hc1.
    pose proof correspond_prop2 as Hc2.
    pose proof Hc1 vcnt (ex2se e (S vcnt)) as Hc1.
    pose proof Hc2 e as Hc2.
    pose proof asgn_vcnt_ex2se_nrm_prop e vcnt as He.
    sets_unfold in He.
    revert H H0 H1.
    simpl.
    sets_unfold.
    unfold correspond, deref_sem_nrm, deref_sem_err.
    destruct e.
    + tauto.
    + intros.
      rewrite H0 in H.
      destruct H1.
      destruct H1.
      destruct H.
      destruct H3.
      pose proof H x x0.
      destruct H5.
      pose proof H6 H1.
      pose proof mem_split s1 x0.
      destruct H8.
      - destruct H8.
        left.
        exists x0.
        split.
        tauto.
        pose proof H3 x0 x1 H8.
        rewrite H8.
        rewrite H9 in H2.
        tauto.
      - right.
        right.
        exists x0.
        split.
        apply H7.
        left.
        tauto.
    + intros.
      destruct Hm as [ss2].
      destruct H2.
      pose proof Hc2 (S vcnt) s1 ss1 ss2 H H2.
      pose proof Hc1 s1 ss2 ss3 H4 H3.
      assert ((Seval_l (SEDeref (genSEVar_n vcnt))).(nrm) ss3 a = (Seval_r (genSECV vcnt)).(nrm) ss3 a).
      {
        simpl.
        reflexivity.
      }
      rewrite H6 in H1.
      pose proof He ss2 ss3 H3 a H1.
      pose proof IHe (S vcnt) s1 ss1 ss2 a H H2 H7.
      tauto.
    + intros.
      destruct Hm as [ss2].
      destruct H2.
      pose proof Hc2 (S vcnt) s1 ss1 ss2 H H2.
      pose proof Hc1 s1 ss2 ss3 H4 H3.
      assert ((Seval_l (SEDeref (genSEVar_n vcnt))).(nrm) ss3 a = (Seval_r (genSECV vcnt)).(nrm) ss3 a).
      {
        simpl.
        reflexivity.
      }
      rewrite H6 in H1.
      pose proof He ss2 ss3 H3 a H1.
      pose proof IHe (S vcnt) s1 ss1 ss2 a H H2 H7.
      tauto.
    + intros.
      destruct Hm as [ss2].
      destruct H2.
      pose proof Hc2 (S vcnt) s1 ss1 ss2 H H2.
      pose proof Hc1 s1 ss2 ss3 H4 H3.
      assert ((Seval_l (SEDeref (genSEVar_n vcnt))).(nrm) ss3 a = (Seval_r (genSECV vcnt)).(nrm) ss3 a).
      {
        simpl.
        reflexivity.
      }
      rewrite H6 in H1.
      pose proof He ss2 ss3 H3 a H1.
      pose proof IHe (S vcnt) s1 ss1 ss2 a H H2 H7.
      tauto.
    + intros.
      destruct Hm as [ss2].
      destruct H2.
      pose proof Hc2 (S vcnt) s1 ss1 ss2 H H2.
      pose proof Hc1 s1 ss2 ss3 H4 H3.
      assert ((Seval_l (SEDeref (genSEVar_n vcnt))).(nrm) ss3 a = (Seval_r (genSECV vcnt)).(nrm) ss3 a).
      {
        simpl.
        reflexivity.
      }
      rewrite H6 in H1.
      pose proof He ss2 ss3 H3 a H1.
      pose proof IHe (S vcnt) s1 ss1 ss2 a H H2 H7.
      tauto.
Qed.

Lemma Split_Serefine_nrm {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr) (vcnt : nat), 
    Serefine_nrm (ex2pre e vcnt) (ex2se e vcnt) e.
Proof.
    induction e.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
Admitted.

Lemma Split_Serefine_err1_deref {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr),
    (forall (vcnt : nat), Serefine_err (ex2pre e vcnt) (ex2se e vcnt) e)
    ->
    forall (vcnt : nat), Serefine_err1 (ex2pre (EDeref e) vcnt) (ex2se (EDeref e) vcnt) (EDeref e).
Proof.
    unfold Serefine_err, Serefine_err1, Serefine_err2_l, Serefine_err2_r.
    intros.
    pose proof H (S vcnt) as H.
    destruct H as [IH1 [IH2 IH3]].
    pose proof ex2pre_deref e vcnt as Hd.
    pose proof midstate_deref_nrm e vcnt as Hm.
    pose proof eval_comlist_seq_err (ex2pre e (S vcnt)) 
        [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))] ss1 as Hs.
    pose proof deref_err_r e s1 as Herr.
    destruct Hs as [Hs1 Hs2].
    pose proof asgn_vcnt_ex2se_err_prop e as He.
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
    + rewrite Hd in H1.
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
    + rewrite Hd in H1.
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
    + rewrite Hd in H1.
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
    + rewrite Hd in H1.
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
    pose proof ex2pre_deref e vcnt as Hd.
    pose proof midstate_deref_nrm e vcnt as Hm.
    pose proof eval_comlist_seq_nrm (ex2pre e (S vcnt)) 
        [SCAsgnVar (nat2Sname vcnt) (ex2se e (S vcnt))] ss1 ss3 as Hs.
    pose proof deref_err_r e s1 as Herr.
    destruct Hs as [Hs1 Hs2].
    pose proof asgn_vcnt_ex2se_nrm_prop e as He.
    pose proof correspond_prop1 as Hc1.
    pose proof correspond_prop2 as Hc2.
    pose proof Hc1 vcnt (ex2se e (S vcnt)) as Hc1.
    pose proof Hc2 e as Hc2.
    destruct e.
    + revert H2.
      simpl.
      tauto.
    + rewrite Hd in H1.
      revert H1 H2.
      simpl.
      sets_unfold.
      intros.
      destruct H2; [tauto|].
      right.
      revert H.
      unfold deref_sem_err.
      intros.
      destruct H.
      destruct H.
      exists x0.
      rewrite H1 in H0.
      unfold correspond in H0.
      destruct H0 as [H3 [H4 H5]].
      pose proof H3 x x0.
      destruct H0.
      pose proof H6 H.
      split.
      tauto.
      pose proof mem_split s1 x0.
      destruct H8.
      destruct H8 as [v].
      pose proof H4 x0 v H8.
      destruct H2.
      rewrite H2 in H9.
      discriminate.
      right.
      rewrite H8.
      rewrite <- H9.
      tauto.
      left.
      tauto.
    + rewrite Hd in H1.
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
    + rewrite Hd in H1.
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
    + rewrite Hd in H1.
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
    + rewrite Hd in H1.
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
    pose proof ex2pre_deref e vcnt as Hd.
    pose proof asgn_vcnt_ex2se_nrm_prop e vcnt as Hp.
    sets_unfold in Hp.
    pose proof ex2se_deref e vcnt as Hdse.
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
    destruct e.
    + rewrite Hd in H1.
      revert H2 H1.
      simpl.
      sets_unfold.
      unfold deref_sem_err.
      intros.
      destruct H2.
      left; tauto.
      destruct H.
      destruct H.
      right.
      exists x.
      split.
      tauto.
      rewrite <- H1 in H2.
      pose proof correspond_prop0 s1 ss1 x H0 H2.
      tauto.
    + rewrite Hd in H1.
      revert H1 H2.
      simpl.
      sets_unfold.
      unfold deref_sem_err.
      intros.
      rewrite <- H1 in H2.
      destruct H2.
      destruct H.
      tauto.
      left.
      destruct H.
      destruct H.
      right.
      exists x0.
      pose proof correspond_prop0 s1 ss1 x0 H0 H2.
      unfold correspond in H0.
      destruct H0 as [? [? ?]].
      pose proof H0 x x0.
      destruct H6.
      split; tauto.
      destruct H.
      revert H.
      unfold deref_sem_nrm.
      intros.
      destruct H.
      destruct H.
      destruct H.
      pose proof mem_split s1 x1.
      destruct H4.
      destruct H4 as [v].
      pose proof correspond_prop0 s1 ss1 x0 H0 as Hc0.
      destruct H0 as [? [? ?]].
      pose proof H5 x1 v H4.
      pose proof H0 x x1.
      destruct H8.
      pose proof H9 H.
      right.
      exists x0.
      split.
      exists x1.
      split.
      tauto.
      rewrite H4.
      rewrite <- H7.
      tauto.
      tauto.
      left.
      right.
      exists x1.
      destruct H0 as [? [? ?]].
      pose proof H0 x x1.
      destruct H7.
      pose proof H8 H.
      split.
      tauto.
      tauto.
    + rewrite Hd in H1.
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
    + rewrite Hd in H1.
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
    + rewrite Hd in H1.
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
    + rewrite Hd in H1.
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
        
Lemma Split_Serefine_err {NameX : Names} {NPX : NamesProperty}:
    forall (e : expr) (vcnt : nat), 
    Serefine_err (ex2pre e vcnt) (ex2se e vcnt) e.
Proof.
    induction e.
    + admit.
    + admit.
    + admit.
    + admit.
    + revert IHe.
      intros.
      unfold Serefine_err.
      pose proof Split_Serefine_err1_deref e IHe vcnt.
      pose proof Split_Serefine_err2_l_deref e IHe vcnt.
      pose proof Split_Serefine_err2_r_deref e IHe vcnt.
      tauto.
    + admit.
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
    forall (s1 ss1 ss2: state),
        (Seval_comlist cl).(nrm) ss1 ss2 ->
        correspond s1 ss1 ->
        ((exists (s2 : state), (eval_com c).(nrm) s1 s2 /\ correspond s2 ss2)
        \/ (eval_com c).(err) s1).

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
    unfold asgn_deref_sem_nrm, correspond in H0.
    intros.
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

Lemma never_inf {NameX : Names}: forall (e : expr) (vcnt : nat) (s : state),
    (Seval_comlist (ex2pre e vcnt)).(inf) s -> False.
Proof.
    intros e vcnt s.
    destruct e; simpl; sets_unfold.
    + tauto.
    + tauto.
Admitted.

Lemma Split_crefine_inf_AsgnVar {NameX : Names} {NPX : NamesProperty}:
    forall (vcnt : nat) (x : var_name) (e : expr),
    forall (s1 ss1 : state),
    (Seval_comlist (com2comlist (CAsgnVar x e) vcnt)).(inf) ss1
    -> correspond s1 ss1 
    -> (eval_com (CAsgnVar x e)).(err) s1
        \/ (eval_com (CAsgnVar x e)).(inf) s1.
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

Lemma Split_crefine_nrm_AsgnDeref {NameX : Names} {NPX : NamesProperty}:
    forall (vcnt : nat) (e1 e2 : expr),
    forall (s1 ss1 ss2 : state),
    (Seval_comlist (com2comlist (CAsgnDeref e1 e2) vcnt)).(nrm) ss1 ss2
    -> correspond s1 ss1 
    -> ((exists (s2 : state), (eval_com (CAsgnDeref e1 e2)).(nrm) s1 s2 /\ correspond s2 ss2)
        \/ (eval_com (CAsgnDeref e1 e2)).(err) s1).
Admitted.

Lemma Split_crefine_err_AsgnDeref {NameX : Names} {NPX : NamesProperty}:
    forall (vcnt : nat) (e1 e2 : expr),
    forall (s1 ss1 : state),
    (Seval_comlist (com2comlist (CAsgnDeref e1 e2) vcnt)).(err) ss1
    -> correspond s1 ss1 
    -> (eval_com (CAsgnDeref e1 e2)).(err) s1.
Admitted.

Lemma Split_crefine_inf_AsgnDeref {NameX : Names} {NPX : NamesProperty}:
    forall (vcnt : nat) (e1 e2 : expr),
    forall (s1 ss1 : state),
    (Seval_comlist (com2comlist (CAsgnDeref e1 e2) vcnt)).(inf) ss1 
    -> correspond s1 ss1 
    -> (eval_com (CAsgnDeref e1 e2)).(err) s1
        \/ (eval_com (CAsgnDeref e1 e2)).(inf) s1.
Admitted.

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

Fixpoint iterLB_nrm
           (D0: EDenote)
           (D1: CDenote)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => test_false D0
  | (S n) => test_true D0 ∘ D1.(nrm) ∘ iterLB_nrm D0 D1 n
  end.

Lemma bounded_in_iter: forall (D0: EDenote) (D1: CDenote),
    ⋃ (boundedLB_nrm D0 D1) ⊆ ⋃ (iterLB_nrm D0 D1).
Proof.
    sets_unfold.
    intros D0 D1 s1 s2 ?.
    destruct H as [n].
    revert s1 s2 H.
    induction n.
    + simpl.
      sets_unfold.
      tauto.
    + simpl.
      sets_unfold.
      intros.
      destruct H.
      - destruct H as [s11].
        destruct H.
        destruct H0 as [s12].
        destruct H0.
        pose proof IHn s12 s2 H1.
        destruct H2 as [n0].
        exists (S n0).
        simpl.
        sets_unfold.
        exists s11.
        split.
        tauto.
        exists s12.
        tauto.
      - exists 0%nat.
        simpl.
        tauto.
Qed.

Lemma iter_in_bounded: forall (D0: EDenote) (D1: CDenote),
    ⋃ (iterLB_nrm D0 D1) ⊆ ⋃ (boundedLB_nrm D0 D1).
Proof.
    sets_unfold.
    intros ? ? s1 s2 ?.
    destruct H as [n].
    revert s1 s2 H.
    induction n.
    + simpl.
      intros.
      exists 1%nat.
      simpl.
      sets_unfold.
      tauto.
    + simpl.
      sets_unfold.
      intros.
      destruct H as [s11].
      destruct H.
      destruct H0 as [s12].
      destruct H0.
      pose proof IHn s12 s2 H1.
      destruct H2 as [n0].
      exists (S n0).
      simpl.
      sets_unfold.
      left.
      exists s11.
      split.
      tauto.
      exists s12.
      tauto.
Qed.

Lemma iter_eq_bounded: forall (D0: EDenote) (D1: CDenote) (s1 s2 : state),
    ⋃ (iterLB_nrm D0 D1) s1 s2 <-> ⋃ (boundedLB_nrm D0 D1) s1 s2.
Proof.
    pose proof iter_in_bounded.
    pose proof bounded_in_iter.
    revert H H0.
    sets_unfold.
    intros.
    split; intros.
    + pose proof H D0 D1 s1 s2 H1.
      tauto.
    + pose proof H0 D0 D1 s1 s2 H1.
      tauto.
Qed.


Lemma split_while_prop1 {NameX : Names} {NPX : NamesProperty}:
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
    pose proof split_while_prop1 n c e s1 ss2 ss3 H H7 vcnt H8 H5.
    tauto.
Qed.

Lemma Split_crefine_nrm {NameX : Names} {NPX : NamesProperty}: 
    forall (c : com) (vcnt : nat),
        Screfine_nrm (com2comlist c vcnt) c.
Proof.
    induction c.
    + apply Split_crefine_nrm_Skip.
    + intros.
      unfold Screfine_nrm.
      pose proof Split_crefine_nrm_AsgnVar vcnt x e.
      tauto.
    + intros.
      unfold Screfine_nrm.
      pose proof Split_crefine_nrm_AsgnDeref vcnt e1 e2.
      tauto.
    + revert IHc1 IHc2.
      pose proof Split_crefine_nrm_Seq_aux c1 c2.
      tauto.
    + revert IHc1 IHc2.
      pose proof Split_crefine_nrm_If_aux e c1 c2.
      tauto.
    + revert IHc.
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



