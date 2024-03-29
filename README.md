# CS2612 大作业：表达式拆分正确性证明

## 运行环境

将文件夹中的代码和编译文件放在`./cs2612-aut2023/pl/`下即可成功运行

## 题目概述

考虑 WhileD 语言的表达式拆分，使得拆分后每条赋值语句至多进行一步运算或者一步读写操作。在coq证明器中定义拆分后的程序语法与程序语义，使用精化关系定义拆分的正确性，并证明这一结论。

- 要求 1：证明对 WhileD 语言中的表达式进行表达式拆分后结果的正确性，证明赋值语句进行表达式拆分时的正确性。
- 要求 2：证明顺序执行语句与 if 语句进行表达式拆分时的正确性。
- 要求 3：证明 while 循环语句进行表达式拆分时的正确性并基于上面结论证明所有语句进行拆分时的正确性。

## 核心思路

### 1.表达式拆分过程

**表达式 `e` 拆分**

​	对于WhileD语言中的表达式e，经过ex2pre和ex2se函数分别得到WhileDS语言中的拆分预处理语句pre和拆分后表达式se。

**程序语句 `c` 拆分**

​	对于WhileD语言中的程序语句c，经过com2comlist函数对c中的所有表达式做拆分，得到WhileDS语言中的表达式列表cl

### 2.通过精化关系描述正确性

**表达式 `e` 精化关系**

- nrm情形：拆分前程序状态s1对应拆分后程序状态ss1，如果拆分后的表达式求值成功，即程序从状态ss1经过语句列表pre成功到达ss2，并且se在ss2上求值成功，值为i，那么，要么e在s1上求值成功且值为i，要么e在s1上求值出错
- err情形：拆分前程序状态s1对应拆分后程序状态ss1，如果拆分后的表达式求值出错，即程序在状态ss1上执行语句列表pre的过程中出错，或者程序从状态ss1经过语句列表pre成功到达ss2，并且se在ss2上求值出错，那么，e在s1上求值出错

**程序语句 `c` 精化关系**

- nrm情形：拆分前程序状态s1对应拆分后程序状态ss1，如果cl在ss1上运行成功终止，即程序从状态ss1经过cl成功到达ss2，那么，要么c在s1上运行出错，要么s1经过c成功到达s2，且s2与ss2对应

* err情形：拆分前程序状态s1对应拆分后程序状态ss1，如果cl在ss1上运行出错，那么，c在s1上运行出错
* inf情形：拆分前程序状态s1对应拆分后程序状态ss1，如果cl在ss1上运行不终止，那么，要么c在s1上运行不终止，要么c在s1上运行出错

## 具体实现

**辅助定义**

​	为便于描述拆分后程序语句command list的行为，本项目采取了自行实现的列表和对其基本的求长度、加减法功能，具体标记如下：

```c
Notation "x :: l" := (cons x l).	#程序语句连接入列表
Notation "[]" := nil.				#空列表
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).	#多语句连接
Notation "x ++ y" := (app x y).		# 列表间连接
```

​	其中关于command list也补充了部分引理：

- `eval_comlist_seq_nrm`：comlist的合并的正常执行可被拆分为两个comlist的正常顺序执行
- `eval_comlist_seq_err`：comlist的合并的出错可被拆分为第一个`cl1`出错或第一个`cl1`正常执行但第二个`cl2`出错
- `eval_comlist_seq_inf`：comlist的合并的`inf` 可被拆分为第一个`cl1`为`inf` 或第一个`cl1`正常执行但第二个`cl2`为`inf` 

**表达式拆分语法定义**

​	采用以下定义拆分后的表达式与程序语句：

```c
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
```

**表达式拆分语义定义**

​	`Seval` 表示拆分表达式，`Seval_com` 表示拆分程序语句。

**表达式拆分过程定义及correspond关系**

​	我们采用了 `Names` 表示原语句变量空间与对应拆分语句状态空间的转换，通过 `name2name` 与 `nat2name` 两种方式映射，并有以下性质：

```c
Class NamesProperty {NameX : Names} : Prop :=
{
    trans_prop1 : forall (x : var_name) (y : var_name) , (x = y) <-> (name2Sname x = name2Sname y);	
    trans_prop2 : forall (x : nat) (y : nat) (s :state) , (x = y) <-> (s.(env) (nat2Sname x) = s.(env) (nat2Sname y));
    trans_prop3 : forall (x : var_name) (y : nat) , name2Sname x <> nat2Sname y;
}.
```

​	对于状态对应关系，我们采用了 `correspond` 关系定义，代表其中变量的对应转换及存储位置的关系：

```c
Definition correspond {NameX : Names} (s ss : state) : Prop :=
    (forall (x : var_name) (i : int64), s.(env) x = i <-> ss.(env) (name2Sname x) = i)
    /\ (forall (a : int64) (v : val), s.(mem) a = Some v -> ss.(mem) a = Some v)
    /\ (forall (vcnt : nat), s.(mem) (ss.(env) (nat2Sname vcnt)) = None 
                            /\ ss.(mem) (ss.(env) (nat2Sname vcnt)) <> None).
```

有以下性质：

- `correspond_prop0`： 若在对应拆分状态内变量未定义或不存在，则在原状态中该变量未定义或不存在；
- `correspond_prop1`：经过辅助变量赋值不改变correspond关系；
- `correspond_prop2`：经过表达式的 `se2pre(e)` 不改变correspond关系（通过`correspond_prop2_X`分别证明）
- `correspond_prop3_asgnvar`：经过程序语句的 `com2pre (CAsgnVar x e)` 不改变correspond关系
- `some_val`：相同变量名对应的值相同

表达式将被拆分为 `pre` 与 `se` 两部分，表示拆分后前处理的comlist和对应终值，表达式中分别由 `ex2pre` 和 `ex2se` 定义；程序语句中分别由 `com2pre` 与 `com2sc` 定义：

```c
Definition ex2se {NameX : Names}
    (e : expr) (vcnt : nat) :
    Sexpr := 
    match e with
    | EConst n =>
        SEConstOrVar (SEConst n)
    | EVar x =>
        SEConstOrVar (genSEVar x)
     ...
 
Fixpoint ex2pre {NameX : Names}
    (e : expr) (vcnt : nat) :
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
     ...
        
```

**精化关系定义**

采用课内精化关系的定义。

表达式为：

```c
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
```

其中对出错的情况 `Serefine_err` 分为 `Serefine_err1`、 `Serefine_err2_l`、 `Serefine_err2_r` 分别表示 `pre` 出错、`se` 左值出错、`se` 右值出错的情况。

程序语句为：

```
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
```



**证明中用到的部分引理**

- `midstate_4_nrm`： 用于构建`binop`中拆分的中间状态
- `midstate_deref_nrm`：用于构建`deref` 拆分的中间状态
- `midstate_unop`：用于构建`unop` 拆分的中间状态
- `asgn_vcnt_ex2se_err_prop`：用于在拆分中赋值出错的情况下证明拆分出错
- `deref4`：用于构建`*e` 拆分的中`#vcnt = e`中间状态的值
- `deref7`： 用于辅助证明`deref` 拆分的正确性
- `greater_vcnt2`：用于证明拆分表达式中`pre`语句不会影响此前的中间变量的值（在处理binop和asgnderef的pre时使用）
- `greater_vcnt1`：用于证明拆分表达式中间变量的赋值时不会影响此前的中间变量的值（在处理binop和asgnderef的pre时使用）
- `construct_state`：用于构造程序语句拆分中间状态
- `construct_asgnderef_sound`：用于构造程序语句拆分中间变量赋值
- `never_inf`：用于证明一般表达式不会产生inf，在后续inf情形证明中使用
- `midstate_asgnderef_nrm`：用于拆分赋值语句中间状态
- `is_inf_append`：用于证明while的inf情形
- `midstate_CSeq`：用于拆分顺序执行的comlist

**拆分正确性证明架构**

```
├── Split_expr_erefine
    ├── Split_Serefine_nrm
        ├── Const
        ├── Split_Serefine_nrm_EVar
        ├── Split_Serefine_nrm_EBinop
            ├── Split_Serefine_nrm_l_binop
            ├── Split_Serefine_nrm_r_binop
        ├── Split_Serefine_nrm_EUnop
            ├── Split_Serefine_nrm_l_unop
            ├── Split_Serefine_nrm_r_unop
        ├── Split_Serefine_nrm_EDeref
            ├── Split_Serefine_nrm_l_deref
            ├── Split_Serefine_nrm_r_deref
        ├── Split_Serefine_nrm_EUnop
            ├── Split_Serefine_nrm_l_addrof
            ├── Split_Serefine_nrm_r_addrof
    ├── Split_Serefine_err
        ├── Const
        ├── Var
        ├── Binop
            ├── Split_Serefine_err1_binop
            ├── Split_Serefine_err2_r_binop
            ├── Split_Serefine_err2_l_binop
        ├── Unop
            ├── Split_Serefine_err1_unop
            ├── Split_Serefine_err2_r_unop
            ├── Split_Serefine_err2_l_unop
        ├── Deref
            ├── Split_Serefine_err1_deref
            ├── Split_Serefine_err2_r_deref
            ├── Split_Serefine_err2_l_deref
        ├── Addrof
            ├── Split_Serefine_err1_addrof
            ├── Split_Serefine_err2_r_addrof
            ├── Split_Serefine_err2_l_addrof
├── Split_expr_crefine
    ├── Skip
        ├── Split_crefine_nrm_Skip
        ├── Split_crefine_err_Skip
        ├── Split_crefine_inf_Skip
    ├── AsgnVar
        ├── Split_crefine_nrm_AsgnVar
        ├── Split_crefine_err_AsgnVar
        ├── Split_crefine_inf_AsgnVar
    ├── AsgnDeref
        ├── Split_crefine_nrm_AsgnDeref
        ├── Split_crefine_err_AsgnDeref
        ├── Split_crefine_inf_AsgnDeref
    ├── Seq
        ├── Split_crefine_nrm_Seq_aux
        ├── Split_crefine_err_Seq_aux
        ├── Split_crefine_inf_Seq_aux
    ├── If
        ├── Split_crefine_nrm_If_aux
        ├── Split_crefine_err_If_aux
        ├── Split_crefine_inf_If_aux
    ├── While
        ├── Split_crefine_nrm_While_aux
            ├── split_while_nrm
        ├── Split_crefine_err_While_aux
            ├── split_while_err
        ├── Split_crefine_inf_While_aux
            ├── split_while_inf
```
