# CS2612 Final Project: SplitExpression
SJTU CS2612 Final Project: Coq Project of expresion split.

Put SplitExpression.v file under /cs2612-aut2023/pl/ folder can successfully compile it.

# 中期报告
我们将WhileD语言经过表达式拆分后得到的语言称作WhileDS语言
## 已完成的工作
* 定义了WhileDS语言需要用到的数据结构：comlist，并实现了一些类方法
* 定义了WhileDS语言的语法
* 定义了WhileDS语言的语义
* 描述了表达式拆分的过程，即ex2pre, ex2se和com2comlist三个函数
* 定义了表达式和程序语句的精化关系
* 定义了所有需要证明的结论，即表达式拆分的正确性
* 证明了一些通用的引理，如comlist的顺序执行
* 证明了一些特殊情形下的引理
## 核心思路
### 表达式拆分过程
对于WhileD语言中的表达式e，经过ex2pre和ex2se函数分别得到WhileDS语言中的拆分预处理语句pre和拆分后表达式se
### 通过精化关系描述正确性
* nrm情形：如果拆分后的表达式求值成功，即程序从状态s1经过语句列表pre成功到达s2，并且se在s2上求值成功，值为i，那么，要么e在s1上求值成功且值为i，要么e在s1上求值出错
* err情形：如果拆分后的表达式求值出错，即程序在状态s1上执行语句列表pre的过程中出错，或者程序从状态s1经过语句列表pre成功到达s2，并且se在s2上求值出错，那么，e在s1上求值出错
### 证明思路及遇到的困难
目前我们只考虑了nrm的情形。通过对表达式e做induction来证明。在递归证明的过程中，提炼出需要频繁用到的性质，作为引理来证明，如顺序执行的性质，赋值语句的性质。
在递归证明的过程中，一个需要频繁考虑的情形是：程序从状态s1经过语句列表pre成功到达s2，再经过一个赋值语句将se的值赋给中间变量#vcnt到达状态s3。证明表达式se在状态s2上的值的正确性，即说明pre语句和#vcnt = se语句的行为，是证明的关键所在。
目前我们在证明这些性质时陷入了循环论证和induction/destruct展开过于复杂的问题。





# Log
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


