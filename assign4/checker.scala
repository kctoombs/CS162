import scala.io._
import cs162.assign4.syntax._
import Aliases._
import scala.io.Source.fromFile

//——————————————————————————————————————————————————————————————————————————————
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
          println("This program is well-typed")
        } catch { case Illtyped => println("This program is ill-typed") }
    }
  }

  // Gets a listing of the constructor names associated with a given type definition.
  // For example, consider the following type definition:
  //
  // type Either['A, 'B] = Left 'A | Right 'B
  //
  // Some example calls to `constructors`, along with return values:
  //
  // constructors("Either") = Set("Left", "Right")
  // constructors("Foo") = a thrown Illtyped exception
  //
  def constructors(name: Label): Set[Label] =
    typeDefs.find(_.name == name).map(_.constructors.keySet).getOrElse(throw Illtyped)

  // Takes the following parameters:
  // -The name of a user-defined constructor
  // -The types which we wish to apply to the constructor
  // Returns the type that is held within the constructor.
  //
  // For example, consider the following type definition:
  //
  // type Either['A, 'B] = Left 'A | Right 'B
  //
  // Some example calls to `constructorType`, along with return values:
  //
  // constructorType("Left", Seq(NumT, BoolT)) = NumT
  // constructorType("Right", Seq(NumT, BoolT)) = BoolT
  // constructorType("Left", Seq(NumT)) = a thrown Illtyped exception
  // constructorType("Right", Seq(BoolT)) = a thrown Illtyped exception
  // constructorType("Foo", Seq(UnitT)) = a thrown Illtyped exception
  // constructorType("Left", Seq(UnitT)) = a thrown Illtyped exception
  //
  def constructorType(constructor: Label, types: Seq[Type]): Type =
    (for {
      td <- typeDefs
      rawType <- td.constructors.get(constructor)
      if (types.size == td.tvars.size)
    } yield replace(rawType, td.tvars.zip(types).toMap)).headOption.getOrElse(throw Illtyped)

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

  // Given a type and a mapping of type variables to other types, it
  // will recursively replace the type variables in `t` with the
  // types in `tv2t`, if possible.  If a type variable isn't
  // in `tv2t`, it should simply return the original type.  If a
  // `TFunT` is encountered, then whatever type variables it defines
  // (the first parameter in the `TFunT`) should overwrite whatever is in
  // `tv2t` right before a recursive `replace` call.  In other words,
  // type variables can shadow other type variables.
  //
  def replace( t:Type, tv2t:Map[TVar, Type] ): Type =
    t match {
     case NumT | BoolT | UnitT => t

     case FunT(params, ret) => FunT(params.map(replace(_, tv2t)), replace(ret, tv2t))

     case RcdT(fields) => RcdT(fields.mapValues(replace(_, tv2t)))

     case TypT(name, typs) => TypT(name, typs.map(replace(_, tv2t)))

     case tv:TVar => tv2t.getOrElse(tv, t)

     case TFunT(tvars, funt) =>

     TFunT(tvars,replace(funt, tv2t -- tvars).asInstanceOf[FunT])
    }

  // HINT - the bulk of this remains unchanged from the previous assignment.
  // Feel free to copy and paste code from your last submission into here.
  def getType( e:Exp, env:TypeEnv ): Type =
    e match {

      	// variables
        case x:Var => env.getOrElse(x, throw Illtyped)

        // numeric literals
        case _:Num => NumT

        // boolean literals
        case _:Bool => BoolT

        // `nil` - the literal for unit
        case _: Unit => UnitT

        // builtin arithmetic operators
        case Plus | Minus | Times | Divide => FunT(Seq(NumT, NumT), NumT)

        // builtin relational operators
        case LT | EQ => FunT(Seq(NumT, NumT), BoolT)

        // builtin logical operators
        case And | Or => FunT(Seq(BoolT, BoolT), BoolT)

        // builtin logical operators
        case Not => FunT(Seq(BoolT), BoolT)

        // function creation
	case Fun(params, body) => {
		FunT(params.map{case(v, t) => t}, getType(body, env ++ params))
	}


	
	// function call
	case Call(fun, args) => {
	val t = args.map{e => getType(e, env)}					
	getType(fun, env) match {
		case FunT(params, retType) =>
			if (params != t) throw Illtyped
			retType
			case _ => throw Illtyped
		}
	}



	// conditionals 
	case If(e1, e2, e3) => {	
	if (getType(e1, env) != BoolT || getType(e2, env) != getType(e3, env)) throw Illtyped else getType(e3, env)
	}


			
	// let binding
	case Let(x, e1, e2) => {
		val t = getType(e2, env + (x ->  getType(e1, env)))
		getType(e1, env)
	}



      case Rec(x, t1, e1, e2) => val newEnv: (Var, Type) = (x, t1)
      val t = getType(e1, env + newEnv)
      if(t1 == t) getType(e2, env + newEnv) else throw Illtyped



      case Record(fields) => RcdT(fields.map{case(label, exp) => (label, getType(exp, env))})
	



      case Access(e, field) => getType(e, env) match {
      case RcdT(fields) => fields.getOrElse(field, throw Illtyped)
      case _ => throw Illtyped
      }
	



      case c @ Construct(constructor, typs, e) =>
      val t = getType(e, env)
      val consMap = typename(constructor)
      if(t == constructorType(constructor, typs)) TypT(consMap, typs) else throw Illtyped



      	case Match(e, cases) => {
        val t = getType(e,env)
	t match {
          case TypT(name,typs) => { 
            val caseSeq = cases.map( (lCase: (Label,Var,Exp)) => lCase._1).toSeq //obtain a sequence of the labels
	    val cons = constructors(name) 
	    val consSeq = cons.toSeq
	    val caseSeqSet = caseSeq.toSet //convert to set in order to be able to compare to cons
	    //compare the lengths, throw illtyped if unequal
            if (caseSeq.length != consSeq.length || cons != caseSeqSet ) throw Illtyped
	    // map the variable to a type, get the type of the expression, and remove the duplicates from the list
            val typeMap = cases.map(( l: (Label,Var,Exp)) => getType(l._3, env+(l._2 -> constructorType(l._1, typs)))).distinct //constructorType returns Type
	    // if they dont all map to the same type then throw illtyped, else return the type
            if(typeMap.length!=1) throw Illtyped else typeMap.apply(0)
          }
          case _ => throw Illtyped
        }
      }



      case TAbs(tvars, fun) => val t = getType(fun, env)
      t match{
      case funType: FunT => TFunT(tvars, funType)
      case _ => throw Illtyped
      }



      case TApp(e, typs) => val t = getType(e, env)
      t match{
      case TFunT(tvars, funt) =>
      if(tvars.size != typs.size) throw Illtyped else replace(funt, (tvars.zip(typs)).toMap)
      case _ => throw Illtyped
      }

   }
    
}
