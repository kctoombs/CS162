import scala.io._
import cs162.assign3.syntax._
import Aliases._
import scala.io.Source.fromFile

//—————————————————————————————————————————————————————————————————————————
// Main entry point

object Checker {
  type TypeEnv = scala.collection.immutable.HashMap[Var, Type]
  object Illtyped extends Exception

  var typeDefs = Set[TypeDef]()

  def main( args:Array[String] ) {
    val filename = args(0)
    val input = fromFile(filename).mkString
    Parsers.program.run(input, filename) match {
      case Left(e) => println(e)
      case Right(program) =>
        val prettied = Pretty.prettySyntax(program)
        typeDefs = program.typedefs

        try {
          getType( program.e, new TypeEnv())
          println(Pretty.prettySyntax(program))
          println("This program is well-typed:\n")
        } catch { case Illtyped => println("This program is ill-typed") }
    }
  }

  // Gets all the constructors associated with a given type name.
  // For example, consider the following typedefs:
  //
  // type Either = Left num | Right bool
  // type Maybe = Some num | None
  //
  // With respect to the above typedefs, `constructors` will return
  // the following underneath the given arguments:
  //
  // constructors(Label("Either")) = Map(Label("Left") -> NumT, Label("Right") -> BoolT)
  // constructors(Label("Maybe")) = Map(Label("Some") -> NumT, Label("None") -> UnitT)
  // constructors(Label("Fake")) throws Illtyped
  //
  def constructors(name: Label): Map[Label, Type] =
    typeDefs.find(_.name == name).map(_.constructors).getOrElse(throw Illtyped)

  // Gets the type of the constructor.
  // For example, considering the typedefs given in the `constructors` comment above,
  // `typename` will return the following with the given arguments:
  //
  // typename(Label("Left")) = Label("Either")
  // typename(Label("Right")) = Label("Either")
  // typename(Label("Some")) = Label("Maybe")
  // typename(Label("None")) = Label("Maybe")
  //
  def typename(constructor: Label): Label =
    typeDefs.find(_.constructors.contains(constructor)).getOrElse(throw Illtyped).name

  def getType( e:Exp, env:TypeEnv ): Type =
    e match {
      // variables
      case x:Var => env get x match{
      case Some(t) => t
      case None => throw Illtyped
      }

      // numeric literals
      case _:Num => NumT

      // boolean literals
      case _:Bool => BoolT

      // `nil` - the literal for unit
      case _: NilExp => UnitT

      // builtin arithmetic operators
      case Plus | Minus | Times | Divide => FunT(Seq(NumT, NumT), NumT)

      // builtin relational operators
      case LT | EQ => FunT(Seq(NumT, NumT), BoolT)

      // builtin logical operators
      case And | Or => FunT(Seq(BoolT, BoolT), BoolT)

      // builtin logical operators
      case Not => FunT(Seq(BoolT), BoolT)

      // function creation
      case Fun(params, body) => FunT(params.map(_._2), getType(body, env ++ params))

      // function call
      case Call(fun, args) => val t: Type = getType(fun, env)
      	   t match{
 	   case FunT(params, ret) => val typeMap = args.map((args: Exp) => getType(args, env))
	   if(typeMap == params) ret else throw Illtyped
	   case _ => throw Illtyped
	   }

      // conditionals 
      case If(e1, e2, e3) =>
      if(getType(e1, env) != BoolT) throw Illtyped
      else if(getType(e2, env) != getType(e3, env)) throw Illtyped
      else getType(e2, env)

      // let binding
      case Let(x, e1, e2) => val tuple: (Var, Type) = (x, getType(e1, env))
      getType(e2, env + tuple)

      // recursive binding
      case Rec(x, t1, e1, e2) => val newEnv: (Var, Type) = (x, t1)
      val t = getType(e1, env + newEnv)
      if(t1 == t) getType(e2, env+ newEnv) else throw Illtyped

      // record literals
      case Record(fields) => RcdT(fields.mapValues((ex: Exp) => getType(ex, env)))

      // record access
      case Access(e, field) => val t = getType(e, env)
      t match{
      case RcdT(f) => f.getOrElse(field, throw Illtyped)
      case _ => throw Illtyped
      }
      
      // constructor use
      case Construct(constructor, e) => {
      val construct = constructors(typename(constructor)).getOrElse(constructor, throw Illtyped)
      if(construct == getType(e, env)) getType(e, env) else throw Illtyped
}      

      // pattern matching (case ... of ...)
      case Match(e, cases) => {
			getType(e, env) match {
				case TypT(name) => {
					val consTypes = constructors(name).map{case(v, t) => v}
					val varTypes = cases.map{case(l, v, t) => l}
				
					if (consTypes.size != varTypes.size || consTypes.toSet != varTypes.toSet) {
						throw Illtyped
					}
					
					val eTypes = cases.map{case(l, v, t) => getType(t, env + (v -> constructors(name)(l)))}.distinct

					if (eTypes.size != 1) {
						throw Illtyped
					}
					eTypes.head
				}
				case _ => {
					throw Illtyped
				}
			}
		}
	}
    }
