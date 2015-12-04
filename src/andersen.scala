import jdk.nashorn.internal.ir.ObjectNode

import scala.collection.mutable.{Map => MMap, Set => MSet}
import scala.util.control.Breaks._
import scala.util._
import TypeAliases._

//——————————————————————————————————————————————————————————————————————————————
// Analysis entry point

object Andersen {
  // flag set by command-line argument: should we use cycle elimination?
  var CE = false

  def main( args:Array[String] ) {
    Parse.getAST( scala.io.Source.fromFile(args(0)).mkString ) match {
      // parsing error: program is not well-formed
      case Left(err) ⇒ println(err)

      // successfully parsed: program is well-formed
      case Right((classTable, ast:Program)) ⇒
        try {
          // throws Illtyped exception if program is not well-typed
          Typechecker.typecheck(ast, classTable)

          // program is well-formed and well-typed; ready to analyze.
          // first check whether we should use cycle elimination
          if (args.size > 1 && args(1) == "--ce") CE = true

          // create and solve the constraint graph
          createGraph(ast)
          solveGraph()

          // print out solution. rather than print everything, which
          // can be overwhelming, instead we'll just print out the
          // points-to sets of the top-level variables.
          //
          // NOTE: if cycle elimination is enabled, then the following
          // needs to be modified accordingly. we want to get exactly
          // the same output whether we use cycle elimination or not.
          //
          val soln:MMap[String, (String, String)] = MMap()
          Graph.varToNode foreach {
            case ((m, x), n) ⇒
              val name = m.mn + "_" + x.name
              val ptsto = n.ptsto.toSeq.sortBy(_.id).mkString(", ")
              val subsetof = n.subsetof.toSeq.sortBy(_.hashCode()).mkString(", ")
              soln(name) = (ptsto, subsetof)
          }
          soln.toSeq.sortBy(_._1).foreach {
            case (name, (ptsto, subsetof)) ⇒ println(name + " → " + ptsto); if (!subsetof.isEmpty) {/*println("subset of: " + subsetof)*/}

          }
        }
        catch {
          // program is not well-typed
          case i:Illtyped ⇒ println(s"TypeError: ${i.msg}")
        }

      case _ ⇒
        sys.error("undefined behavior")
    }
  }
  //returns none if the method is determinate, otherwise it returns the class that makes it non-determinate
  def isDeterminate(cname:ClassName, allClasses: Map[ClassName, Class], methName: MethodName): Option[Class] ={
    allClasses.values.find((c:Class) =>  c.methods.exists((m:Method) => m.mn == methName && c.cn != cname)
      && {
      var superClasses: Set[ClassName] = Set()
      var currClass: ClassName = c.cn
      var topClass: Boolean = false
      while (!topClass && !allClasses(currClass).supercn.isEmpty){
        val superClass = allClasses(currClass).supercn
        superClasses += superClass
        currClass = superClass
        if(currClass == "TopClass"){topClass = true}
      }
      superClasses.contains(cname)
    })
  }
  // create the constraint graph from the program's AST. this will:
  //
  // 1. create all TopNodes and ObjNodes (thus, after createGraph is
  // done no new nodes will ever be created). TopNodes correspond to
  // program variables; ObjNodes correspond to objects (with one
  // ObjNode per static allocation site, i.e., New statement, and also
  // one per object field).
  //
  // 2. fill in the appropriate TopNode ptsto sets using the ObjNodes
  // created for the program's New statements.
  //
  // 3. fill in the appropriate TopNode subsetof edges using the copy
  // assignments (e.g., 'x := y') and the determinate method calls
  // (including New statements, which are constructor calls and are
  // always determinate).
  //
  // 4. fill in the appropriate TopNode indirect constraint sets using
  // the remaining assignments and indeterminate method calls.
  //
  // see the comments below for definitions of determinate and
  // indeterminate calls.
  //
  // NOTE: we only care about variables and object fields that have a
  // reference type, i.e., null or some class. any other
  // variables/fields should be ignored.
  //
  // NOTE: we only care about assignments, method calls, and
  // returns. we assume that all assignments, calls, and returns are
  // of the following forms:
  //
  //      x := y //assign case var
  //      x := y.z //assign case access
  //    x.y := z //update
  //      x := new Foo(y, z, null) //new
  //      x := y.foo(null, z) //method call
  //      x := null //assign case null
  //    return x //method
  //    return x.y // method
  //    return null //method
  //
  // in particular, there is at most one field access in any statement
  // and no call arguments contain field accesses (the null call
  // arguments are there as an example just to remind you to handle
  // this special case). if the program contains an assignment, call,
  // or return that doesn't meet this requirement, your analysis
  // should call 'sys.error("malformed program")'.
  //
  // NOTE: a method call is _determinate_ if we can figure out which
  // method is being called without any analysis. consider the call 'x
  // := y.foo()'. this call is determinate if (1) foo's type is some
  // class X; and (2) no class that directly or transitively inherits
  // from X overrides method foo. in this case we know that there is
  // only one possible method that this call can go to, and we can go
  // ahead and update the constraint graph appropriately. otherwise
  // the call is _indeterminate_; indeterminate calls will be stored
  // in CallCon indirect constraints, attached to the receiver
  // object's node (in this example, the TopNode for y), and processed
  // dynamically.
  //
  // NOTE: when handling method calls (determinate ones here, but the
  // same note applies for the indeterminate ones handled
  // dynamically), be sure to remember the implicit 'self'
  // parameter. A method's 'self' parameter should be updated so that
  // its points-to set contains the ObjNode used to call that
  // method. For example, for 'x := y.foo()' suppose that y points to
  // an ObjNode o of class X, and X has a particular method foo. then
  // we will generate the appropriate assignments between the call
  // arguments and foo's parameters and between x and foo's return
  // statement. in addition, foo has an implicit parameter 'self', and
  // self's points-to set should be updated to contain o.
  //
  // NOTE: another thing to remember about method calls is that there
  // can be more parameters than arguments. Any extra parameters
  // should have their points-to sets updated to contain Null.
  //
  def createGraph( ast:Program ) = {

    //keep track of all the allocated object nodes
    //var objNodes: MMap[(Var, ClassName), ObjNode]= MMap()
    val allClasses: Map[ClassName, Class] = ast.classes.map(f => (f.cn, f)).toMap

    ast.classes.map{
      cls => cls.methods.map {
        meth => meth.body.map{
          stmt => stmt match{

            //Assignments
            case Assign(x, e) =>
              e match{
                case v1 @ Var(name) => {
                  val leftTopNode = Graph.getNode(meth, x)
                  val rightTopNode = Graph.getNode(meth, v1)
                  rightTopNode.subsetof += leftTopNode
                }

                case a @ Access(e, v) =>
                  e match{
                    case v2 @ Var(name) => {
                      val newTopNode = Graph.getNode(meth, x)
                    }
                    case _ => sys.error("malformed program")
                  }

                case Nulls() =>
                  val newTopNode = Graph.getNode(meth, x)
                  newTopNode.ptsto += Null

                case _ => ;
              }

            // New objects
            case New(x, cn, args) => {
              val fields: Set[Decl] = allClasses(cn).fields
              val parentNode = Graph.allocNode(cn, stmt.id,
                fields.map(fld => fld.τ match {
                case ClassT(fld_cn) =>
                  val childNode:ObjNode = Graph.allocNode(fld_cn, stmt.id)
                  childNode.ptsto += Null
                  (fld.x,  childNode)
                case _ =>
              }).collect{case (v: Var, o: ObjNode) => v -> o}.toMap)
              val topNode = Graph.getNode(meth, x)
              topNode.ptsto += parentNode
            }

            //Updates
            case u @ Update(e1, x, e2) =>
              e1 match{
                case v1 @ Var(name_1) => e2 match {
                  case v2 @ Var(name_2) =>
                    val newTopNode = Graph.getNode(meth, v1)
                  //case nulls here?
                }
                case _ => sys.error("malformed program")
              }

            //Method Calls
            /*case c @ Call(x, e, mn, args) => e match {
                //Right hand expression is some variable
              case v@Var(name) => meth.params.find((d: Decl) => d.x == v) match {
                  //We found the type in the parameter list
                case Some(d) => d.τ match {
                  //The type of that variable is some class/object
                  case ClassT(classname) => allClasses(classname).methods.find((m: Method) => m.mn == mn) match {
                      //The method actually exists
                    case Some(m) => m.τret match {
                        // It's return type is a class
                      case c_1@ClassT(classname_2) => isDeterminate(classname_2, allClasses, m.mn) match {

                        case Some(c) => //indeterminate i.e. there is some child out there that overrides the method

                        case None => //determinate
                          m.rete match{
                            case returnVar @ Var(name)=>
                              val leftTopNode = Graph.getNode(meth, x)
                              val rightTopNode = Graph.getNode(m, returnVar)
                              rightTopNode.subsetof += leftTopNode
                            case _ => sys.error("malformed program")
                          }
                      }
                      case NullT =>
                    }
                    case None => sys.error("malformed program")
                  }
                  //continue on if the return type isn't a class
                }
                case None => sys.error("malformed program")
              }

            }*/

            case c @ Call(x, e, mn, args) => e match {
              case v@Var(name) => val ptsto = Graph.getNode(meth, v).ptsto;
                ptsto.map{
                  objNode =>
                    objNode match {
                    case ObjNode(child_ptsto, child_subsetof, cn, id, fields) => {
                      val cls: Class = allClasses(cn)
                      cls.methods.find(( m:Method ) => m.mn == mn ) match {
                        case Some(match_meth) => match_meth.τret match {
                          case c_2@ClassT(classname_2) => isDeterminate(cn, allClasses, match_meth.mn) match {

                            //method is indeterminant
                            //TODO: handle indeterminant calls
                            case Some(c) =>

                            //method is determinant
                            case None =>

                              //update self node
                              val selfNode: TopNode = Graph.getNode(match_meth, match_meth.params(0).x)
                              selfNode.ptsto +=  objNode

                              //update subsetof nodes for args and params
                              args.zipWithIndex.foreach( a => a._1 match {
                                  case v@Var(name) =>
                                    val argTopNode: TopNode = Graph.getNode(meth, v)
                                    //add 1 to account for self
                                    if(a._2 +1 < args.length) {
                                      val paramTopNode: TopNode = Graph.getNode(match_meth, match_meth.params(a._2 + 1).x)
                                      argTopNode.subsetof += paramTopNode
                                    }else{
                                      //account for more params than args
                                      val paramTopNode: TopNode = Graph.getNode(match_meth, match_meth.params(a._2 + 1).x)
                                      paramTopNode.ptsto += Null
                                    }

                                  case Nulls() =>
                                    val paramTopNode: TopNode = Graph.getNode(match_meth, match_meth.params(a._2 + 1).x)
                                    paramTopNode.ptsto += Null
                                  case _ => ;
                            })
                              //handle determinate return statements
                              match_meth.rete match {
                                //return x
                                case v @ Var(name) =>
                                  val leftTopNode = Graph.getNode(meth, x)
                                  val rightTopNode = Graph.getNode(match_meth, v)
                                  rightTopNode.subsetof += leftTopNode
                                // return null
                                case Nulls() =>
                                  val leftTopNode = Graph.getNode(meth, x);
                                  leftTopNode.ptsto += Null
                                // return x.e
                                case Access(e, x)  =>
                                  e match {
                                    case v @ Var(field_name) =>
                                      val leftTopNode = Graph.getNode(meth, x)
                                      val rightTopNode = Graph.getNode(match_meth, v)
                                      rightTopNode.subsetof += leftTopNode
                                    case Nulls() => val leftTopNode = Graph.getNode(meth, x);
                                                  leftTopNode.ptsto += Null
                                    case _ => sys.error("malformed program")
                                  }
                              }
                          }
                        }
                        case None => sys.error("malformed program") //method doesn't exist
                      }
                    }
                    case Null => ; //continue on if we have a null in the ptsto set
                  }

                }
              case _ => ;
            }
          }
        }
      }
    }
    // ...
  }

  // use the worklist algorithm to propagate ptsto sets and add new
  // edges until the constraint graph converges to its final version.
  //
  // if the CE flag is true, then solveGraph should use Lazy Cycle
  // Detection as described in class: immediately after propagating
  // ptsto information across an edge from node n to node m, check
  // whether n and m have identical points-to sets. if they do, then
  // trigger cycle elimination by calling cycleElim(n).
  //
  // here is the worklist algorithm:
  //
  // initialize the worklist to contain all TopNodes
  //
  // while the worklist is not empty:
  //   n := worklist.pop()
  //
  //   for each dst in n.subsetof do {
  //     propagate n.ptsto to dst.ptsto
  //     if dst.ptsto changed, add dst to worklist
  //     // if CE is true, check whether cycle elimination should be triggered
  //   }
  //
  //   if n is an ObjNode, go to the next iteration. else n is a
  //   TopNode; do the following:
  //
  //   for each RhsCon(src, _, fld) in n.cons {
  //     for each p in n.ptsto {
  //       update src.subsetof to include p.fields(fld)
  //       if src.subsetof changed, add src to worklist
  //     }
  //   }
  //
  //   for each LhsCon(_, fld, dst) in n.cons {
  //     for each p in n.ptsto {
  //       update p.fields(fld).subsetof to include dst
  //       if p.fields(fld).subsetof changed, add p.fields(fld) to worklist
  //     }
  //   }
  //
  //   for each CallCon(rhs, _, mn, args) in n.cons {
  //     for each p in n.ptsto {
  //       let getMethod(p.class, mn) = m @ Method(_, params, _, _, rete)
  //       let paramsN = params map ( getNode(m, _) )
  //       let reteN = getNode(m, rete)
  //       let selfN = getNode(m, Var("self"))
  //       update selfN.ptsto to include p
  //       if selfN.ptsto changed, add selfN to worklist
  //       update reteN.subsetof to include rhs
  //       if reteN.subsetOf changed, add reteN to worklist
  //       for each arg in args { 
  //         let prm be the corresponding member of paramsN
  //         update arg.subsetof to include prm
  //         if arg.subsetof changed, add arg to worklist
  //       }
  //       for each prm in params that did not have a corresponding arg {
  //         update prm.ptsto to include Null
  //         if prm.ptsto changed, add prm to worklist
  //       }
  //     }
  //   }
  //
  def solveGraph() {
    // ...
    var workList: Set[Node] = Graph.varToNode.values.toSet

    while (workList.nonEmpty) {
      val n = workList.head
      workList = workList.tail

      n match {
        //head is a top node
        case n@TopNode(ptsto, subsetof, cons) => {
          n.subsetof.foreach((dst: Node) => {
            dst match {
              case t@TopNode(ptsto, subsetof, cons) => {
                var priorT = t
                t.ptsto ++= n.ptsto
                if (!(t.ptsto equals priorT.ptsto)) {
                  workList += t
                }
              }
              case o@ObjNode(ptsto, subsetof, cn, site, fields) => {
                var priorO = o;
                o.ptsto ++= n.ptsto;
                if (!(o.ptsto equals priorO.ptsto)) {
                  workList += o
                }
              }
            }
          }) //for each
        }
        //head is a an obj node
        case n@ObjNode(ptsto, subsetof, cn, site, fields) => {
          n.subsetof.foreach((dst: Node) => {
            dst match {
              case t@TopNode(ptsto, subsetof, cons) => {
                var priorT = t
                t.ptsto ++ n.ptsto
                if (t.ptsto != priorT.ptsto) {
                  workList += t
                }
              }
              case o@ObjNode(ptsto, subsetof, cn, site, fields) => {
                var priorO = o;
                o.ptsto ++ n.ptsto;
                if (o.ptsto != priorO.ptsto) {
                  workList += o
                }
              }
            }
          })
        }
      }
    } //worklist loop
  }

  // this is called from solveGraph() to detect and merge cycles in
  // the constraint graph involving the given node n. it should only
  // be used if the 'CE' flag is set to true by a command-line
  // argument.
  //
  // NOTE: you will need to modify the definitions of the graph nodes
  // to enable node merging using the union-find data structure.
  //
  // NOTE: cycle elimination is simple in principle, but can be tricky
  // in execution. when merging nodes, you need to remember to
  // transfer all the appropriate information from the constituent
  // nodes to the new set representative. when processing nodes, you
  // need to be very careful that you're always dealing with the set
  // representative and not a node that has been merged away. remember
  // that cycle elimination can happen at any time, and just because
  // something used to be a set representative before doesn't mean
  // that it still is now.
  //
  // NOTE: you can choose whether to define a new kind of node to use
  // as set representatives, or to allow TopNodes and ObjNodes to
  // stand as set representatives; either way will work. consider,
  // though, that TopNodes and ObjNodes can be in the same cycle
  // together, and in this case a set representative needs to act like
  // a TopNode _and_ an ObjNode.
  //
  def cycleElim( n:Node ) {
    print("No cycles to eliminate...")
    // ...
  }
}

//——————————————————————————————————————————————————————————————————————————————
// Indirect constraints (initial and direct constraints are
// represented directly in the constraint graph via the ptsto and
// subsetof sets in the graph nodes)

sealed abstract class Constraint

// field access on the left: src.fld ⊆ dst
case class RhsCon( src:TopNode, fld:Var, dst:TopNode ) extends Constraint

// field access on the right: src ⊆ dst.fld
case class LhsCon( src:TopNode, dst:TopNode, fld:Var ) extends Constraint

// indeterminate method call: rhs := lhs.method(args)
case class CallCon( rhs:TopNode, lhs:TopNode, mn:MethodName, args:Seq[TopNode] ) extends Constraint

//——————————————————————————————————————————————————————————————————————————————
// Constraint graph

// constraint graph nodes
sealed abstract class Node

object Node {
  type Ptsto = MSet[RefNode] // points-to sets
  type Edges = MSet[Node]    // edge sets
}
import Node._

// nodes for top-level variables
case class TopNode(
  ptsto:Ptsto = MSet(),        // points-to set
  subsetof:Edges = MSet(),     // graph edges
  cons:Set[Constraint] = Set() // indirect constraints for this node
) extends Node

// ref nodes are for things that can belong to points-to sets. this
// includes objects and Null.
sealed abstract class RefNode( val id:Int ) extends Node

// nodes for abstract objects
case class ObjNode(
  ptsto:Ptsto = MSet(),           // points-to set
  subsetof:Edges = MSet(),        // graph edges
  cn:ClassName,                   // this object's class
  site:Int,                       // this object's allocation site (AST node id)
  fields:Map[Var,ObjNode] = Map() // this object's fields (that are references)
) extends RefNode(site) { override def toString = id.toString }

// the Null node. this will only show up inside points-to sets; there
// cannot be edges to or from Null.
case object Null extends RefNode(0) {
  override def toString = "null"
}

object Graph {
  // we need to remember our mapping from variables to TopNodes in
  // order to consistently map the same variable to the same TopNode
  // across all constraints. in order to disambiguate multiple
  // variables with the same name in different methods, we'll actually
  // map from (method, variable) pairs to TopNodes.
  val varToNode = MMap[(Method,Var), TopNode]()

  // return the TopNode corresponding to the given method and
  // variable. use the mapping in varToNode if it exists; otherwise
  // create one and use that.
  def getNode( m:Method, x:Var ): TopNode = {
    if (varToNode.contains((m, x))){
      varToNode((m , x))
    }else{
      val newNode = TopNode()
      varToNode += ((m, x) -> newNode)
      newNode
    }
  }
    // ...

  // for each object allocation site (i.e., New, as in 'x := new
  // Foo(...)'), we need to take the allocated class and AST node id
  // and create a new ObjNode. this is used to initialize the
  // points-to set of the TopNode corresponding to the variable on the
  // left-hand side of the New.
  //
  // NOTE: each ObjNode contains a map 'fields' containing those class
  // fields that are references; each such field maps to another
  // ObjNode standing for that object's field. the 'site' of these
  // field ObjNodes should be the same as their parent ObjNode, their
  // 'fields' should be empty, and their ptsto sets should be
  // initialized to contain Null.
  //
  // NOTE: the 'allocation site' is the AST node id of the New
  // statement itself. if AST node 'stmt' is 'x := new Foo(...)', then
  // the allocation site is stmt.id.
  //
  def allocNode( cn:ClassName, id:Int, fields: Map[Var, ObjNode] = Map() ): ObjNode =
    ObjNode(MSet(), MSet(), cn, id, fields)

    // ...
}
