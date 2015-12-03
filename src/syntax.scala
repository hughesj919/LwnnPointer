

//——————————————————————————————————————————————————————————————————————————————
// Convenient type aliases

object TypeAliases {
  type ClassName = String
  type MethodName = String
}

import TypeAliases._

//——————————————————————————————————————————————————————————————————————————————
// AST base class

sealed abstract class AST {
  val id = AST.id() // unique node identifier
}

object AST {
  // create unique node identifiers
  var genID = 0
  def id(): Int = { genID += 1; genID-1 }
}

//——————————————————————————————————————————————————————————————————————————————
// Program, Class, Method, Decl

case class Program( classes:Seq[Class] ) extends AST

case class Class( cn:ClassName, supercn:ClassName, fields:Set[Decl],
                  methods:Set[Method] ) extends AST

case class Method( mn:MethodName, params:Seq[Decl], τret:Type,
                   body:Seq[Stmt], rete:Exp ) extends AST

case class Decl( x:Var, τ:Type ) extends AST

//——————————————————————————————————————————————————————————————————————————————
// Stmt
//
// We include a Print statement not in the semantics, which prints out
// the value of an expression; this is used to help debug the
// interpreters by inspecting the values they compute.

sealed abstract class Stmt extends AST
case class Assign( x:Var, e:Exp ) extends Stmt
case class Update( e1:Exp, x:Var, e2:Exp ) extends Stmt
case class Call( x:Var, e:Exp, mn:MethodName, args:Seq[Exp] ) extends Stmt
case class New( x:Var, cn:ClassName, args:Seq[Exp] ) extends Stmt
case class If( e:Exp, tb:Seq[Stmt], fb:Seq[Stmt] ) extends Stmt
case class While( e:Exp, body:Seq[Stmt] ) extends Stmt
case class Print( e:Exp ) extends Stmt

//——————————————————————————————————————————————————————————————————————————————
// Exp, BinaryOp

sealed abstract class Exp extends AST
case class Nums( ns:Set[BigInt] ) extends Exp
case class Bools( bs:Set[Boolean] ) extends Exp
case class Strs( strs:Set[String] ) extends Exp
case class Nulls() extends Exp
case class Var( name:String ) extends Exp
case class Access( e:Exp, x:Var ) extends Exp
case class Binop( op:BinaryOp, e1:Exp, e2:Exp ) extends Exp

sealed abstract class BinaryOp
case object ⌜+⌝ extends BinaryOp
case object ⌜−⌝ extends BinaryOp
case object ⌜×⌝ extends BinaryOp
case object ⌜÷⌝ extends BinaryOp
case object ⌜<⌝ extends BinaryOp
case object ⌜≤⌝ extends BinaryOp
case object ⌜∧⌝ extends BinaryOp
case object ⌜∨⌝ extends BinaryOp
case object ⌜≈⌝ extends BinaryOp
case object ⌜≠⌝ extends BinaryOp
