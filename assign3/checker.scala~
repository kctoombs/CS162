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
				getType(program.e, new TypeEnv())
				println(Pretty.prettySyntax(program))
				println("\nThis program is well-typed")
			} 
			catch { 
				case Illtyped => 
					println("\nThis program is ill-typed")
			}
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

	def getType(e:Exp, env:TypeEnv): Type = e match {
	
		// variables
		case x:Var => {
			env.getOrElse(x, throw Illtyped)
		}

		// numeric literals
		case _:Num => {
			NumT
		}

		// boolean literals
		case _:Bool => {
			BoolT
		}

		// `nil` - the literal for unit
		case _: NilExp => {
			UnitT
		}

		// builtin arithmetic operators
		case Plus | Minus | Times | Divide => {
			FunT(Seq(NumT, NumT), NumT)
		}

		// builtin relational operators
		case LT | EQ => {
			FunT(Seq(NumT, NumT), BoolT)
		}

		// builtin logical operators
		case And | Or => {
			FunT(Seq(BoolT, BoolT), BoolT)
		}

		// builtin logical operators
		case Not => {
			FunT(Seq(BoolT), BoolT)
		}

		// function creation
		case Fun(params, body) => {
			FunT(params.map{case(v, t) => t}, getType(body, env ++ params))
		}
	
		// function call
		case Call(fun, args) => {
			val funType = getType(fun, env)
			val argsTypes = args.map{e => getType(e, env)}					
			funType match {
				case FunT(params, retType) =>
					if (params != argsTypes) {
						throw Illtyped
					}
					retType
				case _ =>
					throw Illtyped
			} 
		}

		// conditionals 
		case If(e1, e2, e3) => {
			val e1Type = getType(e1, env)
			val e2Type = getType(e2, env)
			val e3Type = getType(e3, env)
			
			if (e1Type != BoolT || e2Type != e3Type) {
				throw Illtyped
			}
			else {
				e3Type
			}
		}
			
		// let binding
		case Let(x, e1, e2) => {
			val e1Type = getType(e1, env)
			val e2Type = getType(e2, env + (x -> e1Type))
			e1Type
		}
		
		// recursive binding
		case Rec(x, t1, e1, e2) => {
			val e1Type = getType(e1, env + (x -> t1))
			val e2Type = getType(e2, env + (x -> t1))
			
			if (e1Type != t1) {
				throw Illtyped
			}
			e2Type
		}

		// record literals
		case Record(fields) => {
			RcdT(fields.map{case(l, e) => (l, getType(e, env))})
		}

		// record access
		case Access(e, field) => {
			getType(e, env) match {
				case RcdT(fields) => 
					fields.getOrElse(field, throw Illtyped)
				case _ =>
					throw Illtyped
			}
		}

		// constructor use
		case Construct(constructor, e) => {
			System.out.println("Construct")

			val name = typename(constructor)
			val consType = constructors(name)(constructor)
			val eType = getType(e, env)
			if (eType == consType) {
				TypT(name)
			}
			else {
				throw Illtyped
			}
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