import TypeAliases._
import Typechecker._

import scala.collection.mutable.{Map => MMap} // from below

//——————————————————————————————————————————————————————————————————————————————
// Types

sealed abstract class Type {
  // the subtyping operator (Scala won't allow the more usual <: notation)
  def ⊑ ( τ:Type )(implicit classTable: ClassTable): Boolean
}

case object IntT extends Type {
  // IntT isn't a subtype of anything but itself
  def ⊑ ( τ:Type )(implicit classTable: ClassTable) =
    τ match {
      case  SyntheticType | IntT ⇒ true
      case _ ⇒ false
    }
}

case object BoolT extends Type {
  // BoolT isn't a subtype of anything but itself
  def ⊑ ( τ:Type )(implicit classTable: ClassTable) =
    τ match {
      case SyntheticType | BoolT ⇒ true
      case _ ⇒ false
    }
}

case object StrT extends Type {
  // StrT isn't a subtype of anything but itself
  def ⊑ ( τ:Type )(implicit classTable: ClassTable) =
    τ match {
      case SyntheticType | StrT ⇒ true
      case _ ⇒ false
    }
}

case object NullT extends Type {
  // NullT is a subtype of itself and all classes
  def ⊑ ( τ:Type )(implicit classTable: ClassTable) =
    τ match {
      case NullT | SyntheticType|  _:ClassT ⇒ true
      case _ ⇒ false
    }
}

case class ClassT(cn: ClassName) extends Type {
  // the subtyping of classes depends on the user's program
  def ⊑ ( τ:Type )(implicit classTable: ClassTable) = τ match {
    case SyntheticType | ClassT("TopClass") ⇒ true
    case ClassT(_) if cn == "TopClass" ⇒ false
    case o @ ClassT(on) ⇒
      val tpe = classTable(this)
      val other = classTable(o)
      if (tpe.selfType == other.selfType || tpe.superType == other.selfType)
        true
      else tpe.superType ⊑ o
    case _ ⇒ false
  }
}

case object SyntheticType extends Type {
  def ⊑ ( τ:Type )(implicit classTable: ClassTable) = true
}

//——————————————————————————————————————————————————————————————————————————————
// Parser

import scala.collection.mutable.{Map => MMap}
import scala.util.parsing.combinator._
import scala.util.parsing.combinator.syntactical._

object Parse extends StandardTokenParsers with PackratParsers {

  type Parser[T] = PackratParser[T]

  var counter = 0
  /* keep track of synthetic vars inside of a method */
  var syntheticSet = Set[Decl]()

  var currentClass: Type = ClassT("TopClass")

  val topClassEntry: (Type, ClassTableEntry) =
    ClassT("TopClass") → ClassTableEntry(Class("TopClass", null, Set(), Set()))

  // reserved keywords
  lexical.reserved ++= Seq("class", "extends", "fields", "methods",
    "def", "return", "new", "if", "else", "while", "int", "bool", "string",
    "null", "true", "false", "print")

  lexical.delimiters ++= Seq( "+", "-", "*", "/", "&", "|", "=", "!=",
			 "<", "<=", "{", "}", "(", ")", ":=", ";",
			 ",", "[", "]", ".", ":", "..", "⇒", "##" )

  def syntheticVar() = {
    val v = Var(s"tmp_var${counter += 1; counter}")
    syntheticSet += Decl(v, SyntheticType); v
  }

  def getAST(source: String): Either[String, (ClassTable, AST)] = {
    // strip out comments
    val commentR = """##((#?[^#]+)*)##""".r
    val cleanSource = commentR.replaceAllIn(source, "" )

    // parse the program
    val lexer = new lexical.Scanner(cleanSource)
    val result = phrase(program)(lexer)

    // return result or a useful error message
    result match {
      case Success(ast,_) ⇒ Right(ast)
      case NoSuccess(msg,next) ⇒
        Left(s"Parse error: $msg\n" +
        s"At line: ${next.pos.line} column: ${next.pos.column}\n" +
        next.pos.longString)
    }
  }

  lazy val program: Parser[(ClassTable, Program)] =
    rep(classP) ^^ { cs ⇒
      val classTable = for (c @ Class(name, _, _, _) ← cs)
                       yield (ClassT(name), ClassTableEntry(c))
      (ClassTable(Map((topClassEntry :: classTable): _*)), Program(cs))
    }

  lazy val classP: Parser[Class] =
    "class" ~> classNameDef ~ opt("extends" ~> className) ~ "{" ~ classBody ~ "}" ^^ {
      case name ~ supclass ~ "{" ~ body ~ "}" ⇒
        val superClass = supclass match {
          case Some(name) ⇒ name
          case None ⇒ "TopClass"
        }

        val (flds, methods) =
          if ( body._2.exists( _.mn == name ) ) body
          else (body._1,
                body._2 + Method(name, Seq(Decl(Var("self"), ClassT(name))), ClassT(name), Seq(), Var("self")))

        Class(name, superClass, flds, methods)
    }

  lazy val classBody: Parser[(Set[Decl], Set[Method])] =
    opt("fields" ~> rep1sep(fieldP, ",") <~ ";") ~ opt(rep1(methodP)) ^^ {
      case Some(fields) ~ Some(methods) ⇒ (fields.toSet, methods.toSet)
      case Some(fields) ~ None          ⇒ (fields.toSet, Set.empty[Method])
      case None ~ Some(methods)         ⇒ (Set.empty[Decl], methods.toSet)
      case None ~ None                  ⇒ (Set.empty[Decl], Set.empty[Method])
    }

  lazy val fieldP: Parser[Decl] =
    variable ~ ":" ~ typeP ^^ {
      case x ~ _ ~ t ⇒ Decl(x, t)
    }

  lazy val typeP = (
      "int"     ^^ (_ ⇒ IntT)
    | "bool"    ^^ (_ ⇒ BoolT)
    | "string"  ^^ (_ ⇒ StrT)
    | "null"    ^^ (_ ⇒ NullT)
    | className ^^ (cn ⇒ ClassT(cn))
  )

  lazy val methodP: Parser[Method] =
  "def" ~ methodName ~ ("(" ~> paramList <~ ")") ~ opt(":" ~> typeP) ~ "=" ~ ("{" ~> methodBody <~ "}") ^^ {
    case _ ~ mname ~ params ~ retType ~ _ ~ ((body, ret)) ⇒
      val method = retType match {
        case None ⇒
          if (params contains ((d:Decl) ⇒ d.x.name == "self"))
            sys.error("self parameter should be implicit in concrete syntax")
          Method(mname, Decl(Var("self"), currentClass) +: (params ++ syntheticSet.toList), currentClass, body, ret)

        case Some(tpe) ⇒
          Method(mname, Decl(Var("self"), currentClass) +: (params ++ syntheticSet.toList), tpe, body, ret)
      }
      syntheticSet = Set()
      method
  }

  lazy val paramList: Parser[Seq[Decl]]=
    repsep(variable ~ ":" ~ typeP ^^ { case x ~ _ ~ t ⇒ Decl(x, t) }, ",")

  lazy val methodBody: Parser[(List[Stmt], Exp)] =
    opt(stmtSeq) ~ opt(("return" ~> expP) <~ ";") ^^ {
      case Some(stmts) ~ Some(ret) ⇒ stmts → ret
      case Some(stmts) ~ None      ⇒ stmts → Var("self")
      case None ~ Some(ret)        ⇒ Nil   → ret
      case None ~ None             ⇒ Nil   → Var("self")
    }

  lazy val stmtSeq: Parser[List[Stmt]] =
    rep1sep(stmtP, ";") <~ ";"

  lazy val stmtP: Parser[Stmt] = (
      update
    | newClass
    | methodCall
    | assign
    | ifStmt
    | whileStmt
    | print
  )

  lazy val print: Parser[Stmt] =
    "print" ~> expP ^^ {
      case e ⇒ Print(e)
    }

  lazy val assign: Parser[Stmt] =
    variable ~ ":=" ~ expP ^^ {
      case v ~ _ ~ e ⇒ Assign(v, e)
    }

  lazy val update: Parser[Stmt] =
    expName ~ "." ~ variable ~ ":=" ~ expP ^^ {
      case obj ~ _ ~ field ~ _ ~ value ⇒ Update(obj, field, value)
    }

  lazy val newClass: Parser[Stmt] =
    variable ~ ":=" ~ "new" ~ className ~ argList ^^ {
      case v ~ _ ~ _ ~ cls ~ params ⇒ New(v, cls, params)
    }

  lazy val methodCall: Parser[Stmt] =
    opt(variable <~ ":=") ~ E ~ argList ^^ {
      case ov ~ exps ~ params ⇒
        val (e, mn) = exps match {
          case Access(o, Var(m)) ⇒ (o, m)
          case _ ⇒
            /* better err msg? */
            throw new Exception(s"No receiver for method call $exps.")
        }

        val v = ov match {
          case Some(vn) ⇒ vn
          case None     ⇒ syntheticVar()
        }
        Call(v, e, mn, params)
    }

  lazy val ifStmt: Parser[Stmt] =
    "if" ~ ("(" ~> expP <~ ")") ~ block ~ opt("else" ~>  block) ^^ {
      case _ ~ e ~ tbranch ~ ofbranch ⇒ ofbranch match {
        case None ⇒ If(e, tbranch, Seq())
        case Some(fbranch) ⇒ If(e, tbranch, fbranch)
      }
    }

  lazy val whileStmt: Parser[Stmt] =
    "while" ~ expP ~ block ^^ {
      case _ ~ guard ~ body ⇒ While(guard, body)
        }

  lazy val block =
    "{" ~> stmtSeq <~ "}"

  lazy val argList =
    "(" ~> repsep(expP, ",") <~ ")"

  lazy val expP: Parser[Exp] = (
      E ~ binOpP ~ expP ^^ { case e1 ~ op ~ e2 ⇒ Binop(op, e1, e2) }
    | E
  )

  lazy val E: Parser[Exp] = (
      expP ~ "." ~ variable ^^ { case e ~ _ ~ x ⇒ Access(e, x) }
    | value
    | variable
    | "(" ~> expP <~ ")"
  )

  lazy val expName: Parser[Exp] = (
      variable
    | ambiguousName ~ "." ~ variable ^^ { case e ~ _ ~ x ⇒ Access(e, x) }
    )

  lazy val ambiguousName: Parser[Exp] = (
    variable
  | ambiguousName ~ "." ~ variable ^^ { case e ~ _ ~ x ⇒ Access(e, x) }
  )

  /* need to do non-determinism here */
  lazy val value: Parser[Exp] = (
      int ^^ (d ⇒ Nums(Set(BigInt(d))))
    | bool ^^ (b ⇒ Bools(Set(b)))
    | string ^^ (s ⇒ Strs(Set(s)))
    | "null" ^^ (_ ⇒ Nulls())
    | intSet
    | boolSet
    | strSet
  )

  lazy val intSet =
    "{" ~> repsep(int, ",") <~ "}" ^^ { v ⇒ Nums(v.map(x ⇒ BigInt(x)).toSet) }

  lazy val boolSet =
    "{" ~> repsep(bool, ",") <~ "}" ^^ { v ⇒ Bools(v.toSet) }

  lazy val strSet =
    "{" ~> repsep(string, ",") <~ "}" ^^ { v ⇒ Strs(v.toSet) }

  lazy val binOpP = (
      "+"  ^^^ ⌜+⌝
    | "-"  ^^^ ⌜−⌝
    | "*"  ^^^ ⌜×⌝
    | "/"  ^^^ ⌜÷⌝
    | "<"  ^^^ ⌜<⌝
    | "<=" ^^^ ⌜≤⌝
    | "&"  ^^^ ⌜∧⌝
    | "|"  ^^^ ⌜∨⌝
    | "="  ^^^ ⌜≈⌝
    | "!=" ^^^ ⌜≠⌝
  )

  lazy val int: Parser[String] =
    numericLit

  lazy val bool =
    "true" ^^^ true | "false" ^^^ false

  lazy val string =
    stringLit

  lazy val variable: Parser[Var] =
    ident ^^ (v ⇒ Var(v))

  lazy val className =
    ident

  lazy val classNameDef: Parser[String] =
    ident >> { (s: String) ⇒
      currentClass = ClassT(s); success(s)
    }

  lazy val methodName =
    ident
}

//——————————————————————————————————————————————————————————————————————————————
// pretty printer for Lwnn ASTs

object PrettyPrinter {
  def print(t: AST): String = (new PrettyPrinter(t)).print
  def printType(t: Type): String = (new PrettyPrinter(null)).printType(t)
}

class PrettyPrinter(t: AST) {
  var indentationLevel = 0
  def indentation = "  " * indentationLevel
  def print: String = printTerm(t)

  def printTerm(t: AST): String = t match {
    case Program(cls) ⇒
      printSeq(cls, "\n\n")

    case Class(name, superClass, fields, methods) ⇒
      val pFields = indentBy(indent(s"${keyword("fields")} ${ printSeq(fields.toSeq, ", ") };"))
      val pMethods = indentBy(printSeq(methods.toSeq, "\n\n"))
      s"${keyword("class")} ${colorRed(name)} ${keyword("extends")} ${colorRed(superClass)}" +
        s" ${blockIndent(s"$pFields\n\n$pMethods")}"

    case Method(methodName, params, retT, body, retE) ⇒
      val pBody = indentBy(printSeq(body, ";\n", ";\n"))
      val pRet = indentBy(indent(s"${keyword("return")} ${ printTerm(retE) };"))
      val pParams = printSeq(params, ", ")
      indent(s"${keyword("def")} $methodName($pParams): ${printType(retT)} = ${blockIndent(pBody + pRet)}")

    case Decl(Var(n), t) ⇒
      val pT = printType(t)
      s"$n: $pT"

    case Assign(x, e) ⇒
      indent(s"${printTerm(x)} := ${printTerm(e)}")

    case Update(e1, x, e2) ⇒
      indent(s"${printTerm(e1)}.${printTerm(x)} := ${printTerm(e2)}")

    case Call(x, e, mn, args) ⇒
      indent(s"${printTerm(x)} := ${printTerm(e)}.$mn(${printSeq(args, ", ")})")

    case New(x, cn, args) ⇒
      indent(s"${printTerm(x)} := ${keyword("new")} $cn(${printSeq(args, ", ")})")

    case If(e, tb, fb) ⇒
      val pGuard = printTerm(e)
      val pTB = indentBy(printSeq(tb, ";\n", ";"))
      val pFB = indentBy(printSeq(fb, ";\n", ";"))
      indent(s"${keyword("if")} ($pGuard) ${blockIndent(pTB)} else ${blockIndent(pFB)}")

    case While(e, body) ⇒
      val pBody = indentBy(printSeq(body, ";\n"))
      indent(s"${keyword("while")} (${printTerm(e)}) ${blockIndent(pBody)}")

    case Print(e) ⇒
      s"print($e)"

    case Nums(ns) ⇒
      s"{ ${ns.mkString(", ")} }"

    case Bools(bs) ⇒
      s"{ ${bs.mkString(", ")} }"

    case Strs(ss) ⇒
      s"{ ${ss.map('"' + _ + '"').mkString(", ")} }"

    case Nulls() ⇒
      "null"

    case Var(n) ⇒
      n

    case Access(e, x) ⇒
      s"${printTerm(e)}.x"

    case Binop(op, e1, e2) ⇒
      val pOp = op match {
        case ⌜+⌝ ⇒ "+"
        case ⌜−⌝ ⇒ "-"
        case ⌜×⌝ ⇒ "*"
        case ⌜÷⌝ ⇒ "/"
        case ⌜<⌝ ⇒ "<"
        case ⌜≤⌝ ⇒ "<="
        case ⌜∧⌝ ⇒ "&"
        case ⌜∨⌝ ⇒ "|"
        case ⌜≈⌝ ⇒ "="
        case ⌜≠⌝ ⇒ "!="
      }
      s"${printTerm(e1)} $pOp ${printTerm(e2)}"
  }

  def printSeq(xs: Seq[AST], sepBy: String, termBy: String = "") = {
    val pXS = for (x ← xs) yield printTerm(x)
    if (pXS.isEmpty) ""
    else pXS.mkString(sepBy) + termBy
  }

  def printType(t: Type) = t match {
    case IntT       ⇒ colorRed("int")
    case BoolT      ⇒ colorRed("bool")
    case StrT       ⇒ colorRed("string")
    case NullT      ⇒ colorRed("null")
    case ClassT(cn) ⇒ colorRed(cn)
    case SyntheticType ⇒
      colorRed("SyntheticType")
  }

  def keyword(s: String) =
    colorBlue(s)

  def indentBy(s: ⇒ String) = {
    indentationLevel += 1
    val result = s
    indentationLevel -= 1
    result
  }

  def indent(s: ⇒ String) = {
    indentation + s
  }

  def blockIndent(s: ⇒ String) = {
    s"{\n$s\n$indentation}"
  }

  def colorRed(s: String) = {
    s"\033[31m$s\033[0m"
  }

  def colorBlue(s: String) = {
    s"\033[34m$s\033[0m"
  }
}

//——————————————————————————————————————————————————————————————————————————————
// Type checker

case class Illtyped(msg: String) extends Exception(msg)

object Typechecker {
  def pp(t: AST) = PrettyPrinter.print(t)
  def pt(t: Type) = PrettyPrinter.printType(t)

  case class ClassTable(table: Map[Type, ClassTableEntry]) {
    def apply(c: Type): ClassTableEntry = table get c match {
      case Some(t) ⇒ t
      case None ⇒ throw Illtyped(s"Class name $c is not declared. ${this}")
    }

    /* Field lookup that supports super classes. */
    def field(t: Type, x: Var): Type = {
      val clazz = apply(t)
      clazz.field(x) match {
        case Some(ft) ⇒ ft
        case None if clazz.superType == ClassT("TopClass") ⇒
          throw Illtyped(s"Class $t does not have a field $x.")
        case None ⇒ field(clazz.superType, x)
      }
    }

    /* Method lookup that supports super classes. */
    def method(t: Type, x: Var): MethodType = {
      val clazz = apply(t)
      clazz.method(x) match {
        case Some(mt) ⇒ mt
        case None if clazz.superType == ClassT("TopClass") ⇒
          throw Illtyped(s"Class $t does not have a method $x.")
        case None ⇒ method(clazz.superType, x)
      }
    }

    /* Constructor for a class */
    def constructor(t: Type): MethodType = {
      val clazz = apply(t)
      clazz.constructor match {
        case Some(cons) ⇒ cons
        case None if clazz.superType == ClassT("TopClass") ⇒
          MethodType(t, Nil)
        case None ⇒
          val MethodType(_, argT) = constructor(clazz.superType)
          MethodType(t, argT)
          /* downcast the constructor to the derived class */
      }
    }

    /* Built-In types */
    val builtins = Set[Type](BoolT, IntT, StrT, NullT)
  }

  case class MethodType(returnT: Type, argTs: Seq[Type])

  /* A helper container for types related to classes (constructor,
   * field, method, super type) */
  case class ClassTableEntry(clazz: Class) {

    val fieldTable = Map(
      (clazz match {
        case Class(_, _, fields, _) ⇒
          for (field ← fields) yield field.x → field.τ
      }).toSeq: _*
    )

    val methodTable = Map(
      (clazz match {
        case Class(_, _, _, methods)  ⇒
          for (method ← methods) yield {
            Var(method.mn) → MethodType(method.τret, method.params.map {_.τ})
          }
      }).toSeq: _ *
    )

    val constructor = methodTable.get(Var(clazz.cn))

    def field(x: Var): Option[Type] =
      fieldTable.get(x)

    def method(x: Var): Option[MethodType] =
      methodTable.get(x)

    def superType = ClassT(clazz.supercn)

    def selfType  = ClassT(clazz.cn)
  }

  def typecheck(ast: AST, classTable: ClassTable): Type = {
    inScope(TypeEnv(Map()))(classTable).check(ast)
  }

  // type environment
  case class TypeEnv(env: Map[String, Type] = Map()) {
    def apply( x:String ): Type =
      env get x match {
        case Some(τ) ⇒ τ
        case None ⇒ throw Illtyped(s"UndeclaredName: $x not found.")
      }

    def +(binding: (String, Type)): TypeEnv =
      TypeEnv(env + binding)

    /* Extend the environment leaving the mutable classTable the same */
    def ++( bindings:Seq[(String, Type)] ): TypeEnv =
      TypeEnv(env ++ bindings)
  }

  case class inScope(ρ: TypeEnv)(implicit classTable: ClassTable) {
    def check(term: AST): Type = term match {
      case Program(classes) ⇒
        for (clazz ← classes) yield check(clazz)
        NullT

      case clazz @ Class(className, superClass, fields, methods) ⇒
        /* check that superClass is declared */
        val sc = classTable(ClassT(superClass))

        val self = "self" → ClassT(className)

        /* Check that it's fields have valid types */
        for (f @ Decl(k, v) ← fields) yield check(f)

        methods map { m ⇒ inScope(ρ + self) check m }

        NullT

      case m @ Method(methodName, args, retT, body, rete) ⇒
        /* check that arguments exist, and expand scope with method */
        val paramsT = for (d @ Decl(x, t) ← args) yield { x.name → check(d) }
        val methodScope = inScope(ρ ++ paramsT.toList)

        /* check that each stmt is correct */
        for (stmt ← body) { methodScope.check(stmt) }

        val rtype = methodScope.check(rete)
        if (retT ⊑ rtype) NullT
        else throw Illtyped(s"Declared return type: $retT does match actual return type of $rtype.")

      case Decl(x, t) ⇒ t match {
        /* make sure that the type exists in the ClassTable */
        case c: ClassT ⇒ classTable(t).selfType
        case _         ⇒ t
      }

      /* Statements */
      case Assign(x, e) ⇒
        val t1 = check(x)
        val t2 = check(e)
        if (t2 ⊑ t1) NullT else
          throw Illtyped(s"Attempting to assign value of type ${pt(t1)} to a variable of type ${pt(t2)}")

      case Update(e1, x, e2) ⇒
        val receiverT = check(e1)
        val clazz = classTable(receiverT)
        val fieldT = classTable.field(clazz.selfType, x)
        if (check(e2) ⊑ fieldT) NullT
        else throw Illtyped(s"In `${pp(term)}` field has type ${pt(fieldT)} and `${pp(e2)}` has type ${pt(check(e2))}")

      case c @ Call(x, e, mn, args) ⇒
        val fieldT = check(x)
        val method = classTable.method(check(e), Var(mn))
        for ((d, a) ← method.argTs.tail.zip(args)) {
          if (!(check(a) ⊑ d))
            throw Illtyped(s"$a is not subtype $d")
        }

        if (!(method.returnT ⊑ fieldT))
          throw Illtyped(s"${method.returnT} is not subtype $fieldT in `${pp(c)}`")
        NullT

      case New(x, cn, args) ⇒
        val fieldT = check(x)
        val classT = ClassT(cn)
        val declTypes = classTable.constructor(classT).argTs

        for ((d, a) ← declTypes.tail.zip(args)) {
          if (!(check(a) ⊑ d))
            throw Illtyped(s"Argument type ${pt(check(a))} does not match declared type ${pt(d)}")
        }

        if (classT ⊑ fieldT) classT
        else throw Illtyped(s"$cn not subtype of ${pt(fieldT)}")

      case If(e, tb, fb) ⇒
        val guardT = check(e)
        if (guardT != BoolT) throw Illtyped(s"`${pp(e)}` must be of type bool.")
        for (stmt ← tb ++ fb) yield check(stmt)
        NullT

      case w @ While( e, body ) ⇒
        /* check guard */
        if (check(e) != BoolT)
          throw Illtyped(s"`${pp(e)}` must be of type ${pt(BoolT)} in\n\n${pp(w)}")
        /* check body */
        for (stmt ← body) yield check(stmt)
        /* unit */
        NullT

      case Print(e) ⇒
        check(e)
        NullT

      /* Expressions */
      case Nums(_)   ⇒
        IntT

      case Bools(_)  ⇒
        BoolT

      case Strs(_)   ⇒
        StrT

      case Nulls()   ⇒
        NullT

      case Var(name) ⇒
        ρ(name)

      case Access(e, x) ⇒
        classTable.field(check(e), x)

      case bop @ Binop(op, e1, e2) ⇒
        val types = (check(e1), check(e2))
        op match {
          case ⌜+⌝ ⇒ types match {
            case (IntT, IntT) ⇒ IntT
            case (StrT, StrT) ⇒ StrT
            case (t1, t2) ⇒
              throw Illtyped(s"${pt(t1)} ${pt(t2)} must both be int or string in:\n${pp(bop)}.")
          }

          case ⌜−⌝ | ⌜×⌝ | ⌜÷⌝ ⇒ types match {
            case (IntT, IntT) ⇒ IntT
            case (t1, t2)     ⇒
              throw Illtyped(s"${pt(t1)} ${pt(t2)} must both be int in:\n${pp(bop)}.")
          }

          case ⌜<⌝ | ⌜≤⌝ ⇒ types match {
            case (IntT, IntT) ⇒ BoolT
            case (StrT, StrT) ⇒ BoolT
            case (t1, t2)     ⇒
              throw Illtyped(s"${pt(t1)} ${pt(t2)} must both be int or string in:\n${pp(bop)}.")
          }

          case ⌜∧⌝ | ⌜∨⌝ ⇒ types match {
            case (BoolT, BoolT) ⇒ BoolT
            case (t1, t2)       ⇒
              throw Illtyped(s"${pt(t1)} ${pt(t2)} must both be bool:\n${pp(bop)}.")
          }

          case ⌜≈⌝ | ⌜≠⌝ ⇒ types match {
            case (t1, t2) ⇒ BoolT
          }
        }
    }
  }
}

