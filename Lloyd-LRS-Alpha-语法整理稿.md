# Lloyd LRS-Alpha 语法整理稿

## 说明

本文按 LRS-Alpha 草案已有内容重排语法，保留原有句型和关键字，不替文档补定尚未定义的规则。草案把 Binder、Pattern、Term、Prop、Type、Lambda 等表达式文法列为附录 B.6 的前置交付物；因此下面的 EBNF 是已写明部分的整理稿，不代表整门语言的文法已经完备。

## EBNF 记号

- `A ::= B` 表示 A 可按 B 展开。
- `|` 表示任选其一。
- `[X]` 表示可选。
- `{X}` 表示重复零次或多次。
- 引号中的内容是固定关键字或符号。
- 大小写敏感；句子以句点结束。

## 源文件与顶层声明

```ebnf
File              ::= { FileItem } ;

FileItem          ::= Import
                    | Namespace
                    | TransparentDecl
                    | NotationDecl
                    | Command
                    | Decl ;

Import            ::= "Import" ModuleName "." ;

Namespace         ::= "Namespace" Name "."
                      { Decl }
                      "End" Name "." ;

TransparentDecl   ::= "Transparent" Name { "," Name } "." ;

NotationDecl      ::= "Notation" Symbol "on" Type ":=" Const "." ;

Command           ::= PrintAxioms ;

PrintAxioms       ::= "Print" "axioms" [ Name ] "." ;

Decl              ::= Theorem
                    | Define
                    | RecDefine
                    | Axiom ;

Axiom             ::= "Axiom" Name ":" Prop "." ;

Define            ::= "Define" Name { "(" Binder ")" }
                      ":" Type ":=" Term "." ;

RecDefine         ::= "Define" Name "(" Binder { "," Binder } ")"
                      ":" Type
                      "by recursion on" Var "."
                      { Equation }
                      [ Decreases ] ;

Equation          ::= "Equation" Name "(" Pattern { "," Pattern } ")"
                      ":=" Term
                      [ "when" Prop ]
                      "." ;

Decreases         ::= "Decreases" Term "."
                      { Obligation } ;

Obligation        ::= "Obligation" Name ":" Prop "." Proof ;

Theorem           ::= "Theorem" Name "."
                      { Let }
                      Claim
                      Proof ;

Let               ::= "Let" Binder { "," Binder } "be" Type "." ;

Claim             ::= "Claim:" Prop "." ;

Proof             ::= "Proof." { Sentence } "QED." ;
```

`Namespace` 的起止名称必须相同；文档规定名称作用域，但没有在 EBNF 中写出这项一致性检查。

## 证明句型

```ebnf
Sentence          ::= Let
                    | Step
                    | Hence
                    | Induction
                    | Case
                    | Suppose
                    | Take
                    | Unfold
                    | Contradiction
                    | Todo ;

Step              ::= "Step" Name ":" Prop "," "by" Just "." ;

Hence             ::= "Hence" Prop "by" Just "." ;

Just              ::= "[" ProofTerm "]" ;

ProofTerm         ::= Name { Arg }
                    | "evidence" Name Name { Arg }
                    | "symm" AtomPT
                    | "trans" AtomPT AtomPT
                    | "congr" AtomTerm AtomPT ;

AtomPT            ::= Name
                    | "(" ProofTerm ")" ;

Induction         ::= "By induction on" Var
                      [ "with motive" Lambda ]
                      "." ;

Case              ::= "Case" Pattern
                      [ "," "with hypothesis" Name ":" Prop ]
                      "." ;

Suppose           ::= "Suppose" Name ":" Prop "." ;

Take              ::= "Take" Var "such that" Name ":" Prop "." ;

Unfold            ::= "Unfold" Name "in" Prop "." ;

Contradiction     ::= "By contradiction" Name ":" Prop "." ;

Todo              ::= "Todo." ;
```

### ProofTerm 的约束

1. `Just` 的方括号中必须且只能有一个 `ProofTerm`。
2. 引理、局部假设、已命名步骤都通过 `Name` 引用；所需实参必须显式写出。
3. 应用按左结合解析；组合子嵌套时用括号分组，例如 `trans s1 (trans s2 s3)`。
4. `evidence` 形式为 `evidence 检查器 证书 实参...`；证据必须能由内核检查。
5. 编译器不做统一、搜索或猜测。组合方式和归纳 motive 需要选择时，作者必须显式写出。

## 已明确的文件级规则

- 源文件使用 UTF-8。
- 关键字大小写敏感，句型固定。
- `Proof.` 开始证明块，`QED.` 结束证明块。
- `Todo.` 仅能出现在证明块中；含未完成证明的文件不能认证，也不能被其他文件导入。
- `Print axioms.` 报告文件依赖的公理和未完成项；`Print axioms name.` 报告指定定理。
- `Import`、`Namespace`、`Transparent` 和 `Notation` 是顶层结构。
- 记法由操作数已声明的类型查表解析；无法唯一确定时必须报错。

## 草案尚未定义的语法

以下非终结符在草案中被引用，但没有正式产生式：

```text
ModuleName, Name, Var, Symbol, Const,
Binder, Pattern, Arg, Term, AtomTerm,
Prop, Type, Lambda
```

因此，当前文档还不能单独决定：

- 标识符的字符范围、保留字冲突规则、命名空间限定名的词法规则；
- 类型、命题、项、模式、绑定子和 Lambda 的完整表达式文法；
- 数学符号的固定优先级与结合性，以及 `Notation` 如何声明这些信息；
- `Define` 的参数写法与递归定义中的多参数写法是否统一；
- `Case`、`Suppose` 等句型如何划定正文块和局部作用域；
- 注释、换行、缩进、字符串与证书数据的词法规则；
- 各句型到 Lloyd Core Syntax 的逐条展开规则。

这些内容应在附录 B.6 定稿后补入，不能仅靠解析器猜测。

## 与当前 Python 检查器的区别

原文规定的标准块格式是 `Theorem name.`、`Claim: ... .`、`Proof.`、`QED.`。此前的 Python 示例还接受了紧凑写法，例如 `Theorem name : ...`、单独的 `Proof`、`intro h : ... => ...` 和单独句点结束。这些是当前检查器接受的简写，不属于原文 EBNF 已正式规定的语法。

同样，`/\\`、`\\/`、`AndIntro`、`h.1` 和 `h.2` 出现在用户示例及当前检查器中；原文尚未把它们纳入正式的 `Prop`、`Term` 或 `ProofTerm` 产生式。若要将这些语法纳入标准，需要在 LRS 正文或附录 B.6 明确补充。

