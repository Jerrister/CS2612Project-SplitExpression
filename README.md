# CS2612 Final Project: SplitExpression
SJTU CS2612 Final Project: Coq Project of expresion split.

Put SplitExpression.v file under /cs2612-aut2023/pl/ folder can successfully compile it.


# Log
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


