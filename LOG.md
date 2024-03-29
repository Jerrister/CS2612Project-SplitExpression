# CS2612 Final Project: SplitExpression
# Dev Log
## 1221
* 将com2comlist变成c2pre, c2sc
* 证明ex2pre对cor的保持
* 修改了Serefine的定义，需要把证明改一遍
### 下一步
* 重新过一遍erefine_deref_nrm的证明
* 继续erefine_deref_err的证明（仿照nrm的情形推理AsgnVar前后的关系）
* 完善erefine的其他情形和三个待证引理
* 证明com2pre对cor的保持
* 探索复杂情况：Binop和AsgnDeref的处理办法

## 1220
* 反复横跳地修改crefine的描述，最后发现问题出在correspond不够强上
* 发现了erefine和crefine看起来更好的描述方式。事实上，可以证明二者是等价的
* 加强了correspond，使得其对vcnt也有效力。这样一来就能证明经过ex2pre和c2pre能够维持correspond关系，从而完成midstate上correspond的传递
* 完成了crefine_asgnvar中的一些步骤
* 修改了SCIf, SCWhile的声明及其引用
### 下一步
* 继续erefine_deref_err的证明（仿照nrm的情形推理AsgnVar前后的关系）
* 完善erefine的其他情形和三个待证引理
* 将com2comlist变成c2pre, c2sc
* 证明pre对cor的保持
* 探索复杂情况：Binop和AsgnDeref的处理办法


## 1219
* 定义了erefine_err的情形，并发现了erefine_errS这一性质
* 证明完毕了erefine_deref_nrm的情形（除了两个单值引理和一个中间correspond引理）
### 下一步
* 继续err的证明（仿照nrm的情形推理AsgnVar前后的关系）
* 考虑com的精化证明框架：赋值、顺序、If、While
* 完善erefine的其他情形和三个待证引理


## 1218
* 找到了正确的correspond办法
* 证明了一些中间引理，只剩两个很显然的小引理
### 下一步
* 查找表达式语义和程序状态的单调性(mono)来处理两个小引理
* 根据前面修改的引理形式，为deref的证明找到中间变量(a : int64)


## 1211
* 定义了表达式和程序语句的精化关系
* 定义了所有需要证明的结论

## 1208
* 不能在Coq里面死磕，得列举大量的定义、引理，然后理清他们的关系，找到正确的证明顺序

## 1206
* 重新描述了表达式拆分的过程，变成了ex2pre和ex2cl两个函数，否则unfold的时候有时候会卡死（实现应该是没有问题的）
* 考虑搞一个更好递归的性质，现在这个递归不起来
  
## 1205
* 尝试定义了表达式的精化关系
* 但是证明起来很困难,于是拆成了几个部分分开证明（左值/右值，nrm/err）
* 尝试证明左值nrm的情况
### 存在的问题
* 证明左值的时候可能需要用到右值的情况，反之亦然。所以应该考虑把这些情况单独拿出来作为引理，否则会变成循环论证。
  
## 1128.v2
* 完成了com2comlist
* 更改了length函数以适配SCIf和SCWhile的长度
* 在expr2coml系列中加入了处理短路求值的模块
### 存在的问题
* 正确性不保证
### 下一步工作
* 定义精化关系
* 随时注意可能出现的漏洞

## 1128
* 完成了WhileDS语义的定义
* 完成了split_express的定义
* 修改了Svar_name,改回了var_name
### 存在的问题
* 正确性不保证
* 暂时没有实现短路求值
### 下一步工作
* 定义语句的拆分变化
* 定义精化关系
* 加入短路求值
* 注意if和while的正确性
  
## 1127
* 给comlist添加了重载和方法，实现Nat的加法
* WhileDS语言中的变量名：设计了nat和string分别到Svar_name的映射及其性质
* 部分完成了split_express(to comlist)函数
### 存在的问题
* 正确性不保证
### 下一步工作
* 完善拆分函数
* 定义WhileDS语义

## 1124
定义了WhileDS语言的语法
### 遇到的困难
* 还是无法构造中间变量名


## 1123
### 遇到的困难
* 定义split_expression的过程需要创建新变量，而这似乎是不行的
* 读题目要求，似乎也否定了这一点
### 可能的办法
* 先定义split后的表达式和程序语句的语法、语义
* 定义中间量，如TAC
* 定义新语句is_split旧语句，而不是显示地展现split的过程
* 可能需要定义新的结构，比如链表



# 中期报告
我们将WhileD语言经过表达式拆分后得到的语言称作WhileDS语言
## 已完成的工作
* 定义了WhileDS语言需要用到的数据结构：comlist，并实现了一些类方法
* 定义了WhileDS语言的语法
* 定义了WhileDS语言的语义
* 描述了表达式拆分的过程，即ex2pre, ex2se和com2comlist三个函数
* 描述了短路求值的情形
* 定义了表达式和程序语句的精化关系
* 定义了所有需要证明的结论，即表达式拆分的正确性
* 证明了一些通用的引理，如comlist的顺序执行
* 证明了一些特殊情形下的引理
## 核心思路
### 1.表达式拆分过程
对于WhileD语言中的表达式e，经过ex2pre和ex2se函数分别得到WhileDS语言中的拆分预处理语句pre和拆分后表达式se
### 2.通过精化关系描述正确性
* nrm情形：如果拆分后的表达式求值成功，即程序从状态s1经过语句列表pre成功到达s2，并且se在s2上求值成功，值为i，那么，要么e在s1上求值成功且值为i，要么e在s1上求值出错
* err情形：如果拆分后的表达式求值出错，即程序在状态s1上执行语句列表pre的过程中出错，或者程序从状态s1经过语句列表pre成功到达s2，并且se在s2上求值出错，那么，e在s1上求值出错
### X.当前证明进度及遇到的困难
目前我们只考虑了nrm的情形。通过对表达式e做induction来证明。在递归证明的过程中，提炼出需要频繁用到的性质，作为引理来证明，如顺序执行的性质，赋值语句的性质。

在递归证明的过程中，一个需要频繁考虑的情形是：程序从状态s1经过语句列表pre成功到达s2，再经过一个赋值语句将se的值赋给中间变量#vcnt到达状态s3。证明表达式se在状态s2上的值的正确性，即说明pre语句和#vcnt = se语句的行为，是证明的关键所在。

目前我们在证明这些性质时陷入了循环论证和induction/destruct展开过于复杂的问题。
### 3.表达式拆分过程在程序语句上的体现
对于WhileD语言中的程序语句c，经过com2comlist函数对c中的所有表达式做拆分，得到WhileDS语言中的表达式列表cl
### 4.通过精化关系描述正确性
* nrm情形：如果cl在s1上运行成功终止，即程序从状态s1经过cl成功到达s3，那么，要么c在s1上运行出错，要么s1经过c成功到达s2，且对于s2上的所有变量x，其env与mem在s2和s3上保持一致；对于s3上可能的其他中间变量#vcnt，不做任何要求
* err情形：如果cl在s1上运行出错，那么，c在s1上运行出错
* inf情形：如果cl在s1上运行不终止，那么，要么c在s1上运行不终止，要么c在s1上运行出错
### XX.预期使用的证明思路
同样是通过递归的方式来证明。





