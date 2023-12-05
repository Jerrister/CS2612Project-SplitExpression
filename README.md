# CS2612 Final Project: SplitExpression
SJTU CS2612 Final Project: Coq Project of expresion split.

Put SplitExpression.v file under /cs2612-aut2023/pl/ folder can successfully compile it.


# Log
## 1205
* 尝试定义了精化关系
* 但是证明起来很困难
  
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


