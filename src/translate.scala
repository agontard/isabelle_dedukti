/** Translation of Isabelle (proof)terms into the lambda-Pi calculus **/

package isabelle.dedukti

import isabelle.Export_Theory.{No_Syntax, Prefix}
import isabelle.*

import scala.collection.mutable
import scala.annotation.tailrec

/** <!-- Some macros for colors and common references.
 *       Pasted at the start of every object.
 *       Documentation:
 *       $dklp: reference dk/lp (purple)
 *       $dk: reference Dedukti (purple)
 *       $lp: reference Lambdapi (purple)
 *       $isa: reference Isabelle (yellow)
 *       <$met>metname<$mete>: a scala method (orange,code)
 *       <$metc>metname<$metce>: a scala method inside code (orange)
 *       <$type>typname<$typee>: a scala type (dark orange,bold,code)
 *       <$arg>argname<$arge>: a scala argument (pink,code)
 *       <$argc>argname<$argce>: a scala argument inside code (pink)
 *       <$str>string<$stre>: a scala string (dark green)
 *       <$lpc>code<$lpce>: some Lambdapi code (light blue,code)
 *       -->
 * @define dklp <span style="color:#9932CC;">dk/lp</span>
 * @define dk <span style="color:#9932CC;">Dedukti</span>
 * @define lp <span style="color:#9932CC;">Lambdapi</span>
 * @define isa <span style="color:#FFFF00">Isabelle</span>
 * @define met code><span style="color:#FFA500;"
 * @define metc span style="color:#FFA500;"
 * @define mete /span></code
 * @define metce /span
 * @define type code><span style="color:#FF8C00"><b
 * @define typee /b></span></code
 * @define arg code><span style="color:#FFC0CB;"
 * @define argc span style="color:#FFC0CB;"
 * @define arge /span></code
 * @define argce /span
 * @define str span style="color:#006400;"
 * @define stre /span
 * @define lpc code><span style="color:#87CEFA"
 * @define lpce /span></code
 */
object Prelude {

  // Object name translation, and module dependencies management

  // An Isabelle object can be uniquely identified from its id (module
  // name dot name) and its kind (class, type, const, etc.).

  /**
   * Unqualifies an identifier
   * @param qid the (possibly qualified) identifier
   * @return its longest suffix which does not contain a '.'
   */
  def unqualify(qid:String): String = qid.split('.').last

  /**
   * Making an $isa object name unique by specifying its kind.
   * @param id the qualified identifier of the object (modulename.name)
   * @param kind the kind of the object (class, type, const, etc.)
   * @return the string obtained by appending <$arg>kind<$arge>
   *         to <$arg>id<$arge>, with a slash to separate them
   */
  def full_name(id: String, kind: String): String = id + "/" + kind

  /* However, to keep the translated name as close as possible to the
   original name, we remove the module prefix and the kind if this is
   possible. */

  /** map $isa full_name -> translated name */
  var namesMap: Map[String, String] = Map()

  /** set of translated names */
  var namesSet: Set[String] = Set()

  /** Replaces dots with underscore in a name, as $dk does not accept
   * dots in a name.
   * @param m the name to modify
   * @return the name with each '.' and '-' replaced with '_' */
  def mod_name(m: String): String = m.replace(".", "_").replace("-", "_")

  /** map translated name -> module */
  var moduleOf: Map[String, String] = Map()

  /** Get the module of a translated name using map moduleOf
   * @param id the translated name
   * @return the module in which it is defined. <br>
   *         Prints an error if the name cannot be found. */
  def module_of(id: String): String = {
    moduleOf get id match {
      case None => error("unknown name:" + id)
      case Some(m) => m
    }
  }
  
  var current_module: String = "STTfa"
  var map_theory_session: Map[String, String] = Map("STTfa" -> "Pure")
  def set_current_module(m: String): Unit = { current_module = m }
  def set_theory_session(t: String, s: String): Unit = {map_theory_session += t -> s}
  
  /** The string <$str>"STTfa"<$stre> */
  val STTfa: String = "STTfa"

  /** Add a new mapping from an $isa full_name to its translation.
   * @param id the qualified identifier of the object (modulename.name)
   * @param kind the kind of the object (class, type, const, etc.)
   * @param module0 the current $dklp module
   * @return a unique translated id, after updating maps to account for it */
  def add_name(id: String, kind: String, module0: String) : String = {
    val (translated_id,module) = id match {
      case Pure_Thy.FUN => ("arr",STTfa)
      case Pure_Thy.PROP => ("prop",STTfa)
      case Pure_Thy.IMP => ("imp",STTfa)
      case Pure_Thy.ALL => ("all",STTfa)
      case id =>
        val cut = id.split("[.]", 2)
        val (prefix, radical) = if (cut.length == 1) ("", cut(0)) else (cut(0), cut(1))
        // because Dedukti does not accept names with dots
        var translated_id = radical.replace(".","_")
        if (kind == "var") translated_id += "_"
        if (namesSet(translated_id)) translated_id += "_" + kind
        if (namesSet(translated_id)) translated_id = prefix + "_" + translated_id
        if (namesSet(translated_id)) error("duplicated name: " + translated_id)
        (translated_id,module0)
    }
    namesMap += full_name(id, kind) -> translated_id
    namesSet += translated_id
    moduleOf += translated_id -> module
    //println("add_name "+full_name(id,kind)+" -> "+translated_id)
    translated_id
  }

  /** Get the translated name of an $isa object using map namesMap
   * @param id the qualified identifier of the object (modulename.name)
   * @param kind the kind of the object (class, type, const, etc.)
   * @return the translated name of the object. <br>
   *         Prints an error if the object cannot be found. */
  def get_name(id: String, kind: String): String = {
    namesMap get (full_name(id, kind)) match {
      case None => error ("id '"+full_name(id,kind)+"' not found")
      case Some(s) => s
    }
  }

  /* kinds */
  /** <pre><code><$metc>add_class_ident<$metce>(<$argc>a<$argce>, <$argc>module<$argce>) =
   * <$metc><u>[[add_name]]</u><$metce>(<$argc>a<$argce>+<$str>"_class"<$stre>, <$str>"const"<$stre>, <$argc>module<$argce>)</pre></code>
   */
  def add_class_ident(a: String, module: String): String = add_name(a+"_class", Export_Theory.Kind.CONST, module)
  /** <pre><code><$metc>add_class_pred_ident<$metce>(<$argc>a<$argce>, <$argc>module<$argce>) =
   * <$metc><u>[[add_name]]</u><$metce>(<$argc>a<$argce>+<$str>"_class_pred"<$stre>, <$str>"type"<$stre>, <$argc>module<$argce>)</pre></code>
   */
  def add_class_pred_ident(a: String, module: String): String = add_name(a + "_class_pred", Export_Theory.Kind.TYPE, module)
  /** <pre><code><$metc>add_class_type_ident<$metce>(<$argc>a<$argce>, <$argc>module<$argce>) =
   * <$metc><u>[[add_name]]</u><$metce>(<$argc>a<$argce>+<$str>"_class_type"<$stre>, <$str>"type"<$stre>, <$argc>module<$argce>)</pre></code>
   */
  def add_class_type_ident(a: String, module: String): String = add_name(a + "_class_type", Export_Theory.Kind.TYPE, module)
  /** <pre><code><$metc>add_type_ident<$metce>(<$argc>a<$argce>, <$argc>module<$argce>) =
   * <$metc><u>[[add_name]]</u><$metce>(<$argc>a<$argce>, <$str>"type"<$stre>, <$argc>module<$argce>)</pre></code>
   */
  def add_type_ident(a: String, module: String): String = add_name(a, Export_Theory.Kind.TYPE, module)
  /** <pre><code><$metc>add_subtype_ident<$metce>(<$argc>a<$argce>, <$argc>b<$argce>, <$argc>module<$argce>) =
   * <$metc><u>[[add_name]]</u><$metce>(<$str>"<$argc>b<$argce>_of_<$argc>a<$argce>"<$stre>, <$str>"const"<$stre>, <$argc>module<$argce>)</pre></code>
   */
  def add_subtype_ident(a: String, b: String, module: String): String = add_name(s"${b}_of_${a}", Export_Theory.Kind.CONST, module)
  /** Adds a new dependency instance name for two $isa classes
   *
   * @param c1 the name of the first class
   * @param c2 the name of the second class
   * @param module the current $dklp module
   * @return the added name
   * @see <$met><u>[[add_name]]</u><$mete>
   */
  def add_class_dep_ident(c1: String, c2: String, module: String): String = add_subtype_ident(ref_class_pred_ident(c1),ref_class_pred_ident(c2),module)
  /** <pre><code><$metc>add_const_ident<$metce>(<$argc>a<$argce>, <$argc>module<$argce>) =
   * <$metc><u>[[add_name]]</u><$metce>(<$argc>a<$argce>, <$str>"const"<$stre>, <$argc>module<$argce>)</pre></code>
   */
  def add_const_ident(a: String, module: String): String = add_name(a, Export_Theory.Kind.CONST, module)
  /** <pre><code><$metc>add_axiom_ident<$metce>(<$argc>a<$argce>, <$argc>module<$argce>) =
   * <$metc><u>[[add_name]]</u><$metce>(<$argc>a<$argce>, <$str>"axiom"<$stre>, <$argc>module<$argce>)</pre></code>
   */
  def add_axiom_ident(a: String, module: String): String = add_name(a, Markup.AXIOM, module)
  /** <pre><code><$metc>add_thm_ident<$metce>(<$argc>a<$argce>, <$argc>module<$argce>) =
   * <$metc><u>[[add_name]]</u><$metce>(<$argc>a<$argce>, <$str>"thm"<$stre>, <$argc>module<$argce>)</pre></code>
   */
  def add_thm_ident(a: String, module: String): String = add_name(a, Export_Theory.Kind.THM, module)
  /** <pre><code><$metc>add_proof_ident<$metce>(<$argc>serial<$argce>, <$argc>module<$argce>) =
   * <$metc><u>[[add_name]]</u><$metce>(<$str>f"proof_<$stre>$<$argc>serial<$argce><$str>"<$stre>, <$str>""<$stre>, <$argc>module<$argce>)
   */
  def add_proof_ident(serial: Long, module: String): String = add_name(f"proof_$serial", "", module)

  /** The translated name of an $isa class
   * @param a the name of the class
   * @return The translated name of the object <$arg>a<$arge>_class of kind const
   */
  def ref_class_ident(a: String): String = get_name(a+"_class", Export_Theory.Kind.CONST)
  /** The name of an $isa class's predicate
   *
   * @param a the unqualified name of the class
   * @return The translated name of the object <$arg>a<$arge>_class_pred of kind type
   */
  def ref_class_pred_ident(a: String): String = get_name(a + "_class_pred", Export_Theory.Kind.TYPE)
  /** The name of an $isa class's type
   *
   * @param a the unqualified name of the class
   * @return The translated name of the object <$arg>a<$arge>_class_type of kind type
   */
  def ref_class_type_ident(a: String): String = get_name(a + "_class_type", Export_Theory.Kind.TYPE)
  /** The name of two $isa class's dependency instance
   *
   * @param c1 the name of an $isa class
   * @param c2 the name of a subclass of <$arg>c1<$arge>
   * @return The translated name of the object <$arg>a<$arge>_class_pred of kind type
   */
  def ref_class_dep_ident(c1: String, c2: String): String = {
    val cc1 = ref_class_pred_ident(c1)
    val cc2 = ref_class_pred_ident(c2)
    get_name(s"${cc1}_of_${cc2}", Export_Theory.Kind.CONST)
  }
  /** The translated name of an $isa type
   *
   * @param a the name of the type
   * @return The translated name of the object <$arg>a<$arge> of kind type
   * @see <$met><u>[[get_name]]</u><$mete>
   */
  def ref_type_ident(a: String): String = get_name(a, Export_Theory.Kind.TYPE )
  /** The translated name of an $isa constant
   *
   * @param a the name of the constant
   * @return The translated name of the object <$arg>a<$arge> of kind const
   * @see <$met><u>[[get_name]]</u><$mete>
   */
  def ref_const_ident(a: String): String = get_name(a, Export_Theory.Kind.CONST)
  /** The translated name of an $isa axiom
   *
   * @param a the name of the axiom
   * @return The translated name of the object <$arg>a<$arge> of kind axiom
   * @see <$met><u>[[get_name]]</u><$mete>
   */
  def ref_axiom_ident(a: String): String = get_name(a, Markup.AXIOM)
  /** The translated name of an $isa theorem
   *
   * @param a the name of the theorem
   * @return The translated name of the object <$arg>a<$arge> of kind thm
   * @see <$met><u>[[get_name]]</u><$mete>
   */
  def ref_thm_ident(a: String): String = get_name(a, Export_Theory.Kind.THM)
  /** the name of the translation of an $isa proof step
   * @param serial the index of the proof step
   * @return The name that was assigned to it
   * @see <$met><u>[[get_name]]</u><$mete>
   */
  def ref_proof_ident(serial: Long): String = get_name(f"proof_$serial", "")
  /** The translated name of a variable
   * @param a the name of the variable
   * @return The string <$arg>a<$arge>&#95_var
   */
  def var_ident(a: String): String = a+"__var"

  /* prologue proper */
  val typeId: String = add_const_ident("Set",STTfa)
  val  etaId: String = add_const_ident("El",STTfa)
  val  epsId: String = add_const_ident("Prf",STTfa)

  /** The $dklp type <$lpc>Set<$lpce> of simple types. */
  val typeT: Syntax.Term = Syntax.Symb(typeId)
  /** The $dklp function <$lpc>El<$lpce>
   * that maps a simple type to the type of its elements.
   */
  val  etaT: Syntax.Term = Syntax.Symb( etaId)
  /** The $dklp function <$lpc>Prf<$lpce> that maps
   * a simple type proposition to the type of its proofs.
   */
  val  epsT: Syntax.Term = Syntax.Symb( epsId)
  
  /** The name of the $dklp simple type <$lpc>prop<$lpce> of propositions. */
  val propId: String = add_type_ident(Pure_Thy.PROP,STTfa)
  /** The name of the $dklp simple type constructor
   * <$lpc>arr<$lpce> representing arrow types.
   */
  val  funId: String = add_type_ident(Pure_Thy.FUN,STTfa)
  /** The name of the $dklp simple type connector
   * <$lpc>imp<$lpce> representing implication.
   */
  val  impId: String = add_const_ident(Pure_Thy.IMP,STTfa)
  /** The name of the $dklp simple type connector
   * <$lpc>all<$lpce> representing universal quantification.
   */
  val  allId: String = add_const_ident(Pure_Thy.ALL,STTfa)

  /** Declares the $dklp type <$lpc>Set<$lpce> of simple types. */
  val typeD: Syntax.Command  = Syntax.Declaration(typeId, Nil, Syntax.TYPE)

  val  etaN: Syntax.Notation = Syntax.Prefix("η", 10)
  /** Declares the $dklp function <$lpc>El<$lpce>
   * that maps a simple type to the type of its elements.
   */
  val  etaD: Syntax.Command  = Syntax.DefableDecl(etaId, Syntax.arrow(typeT, Syntax.TYPE), inj = true, not = Some(etaN))

  val epsN: Syntax.Notation = Syntax.Prefix("ε", 10)
  val epsTy: Syntax.Term = Syntax.arrow(Syntax.Appl(etaT, Syntax.Symb(propId)), Syntax.TYPE)
  /** Declares the $dklp function <$lpc>Prf<$lpce> that maps
   * a simple type proposition to the type of its proofs.
   */
  val epsD: Syntax.Command = Syntax.DefableDecl(epsId, epsTy, not = Some(epsN))
  
  /** Typing context. <code><$metc>global_types<$metce>(<$argc>id<$argce>)</code> is used to know
   *  the amount and types of arguments needed to eta-expand <$arg>id<$arge>. */
  var global_types: Map[Syntax.Ident, Syntax.Typ] = Map(
    typeId -> Syntax.TYPE,
    etaId -> Syntax.arrow(typeT, Syntax.TYPE),
    epsId -> epsTy
  )

}

/** <!-- Some macros for colors and common references.
 *       Pasted at the start of every object.
 *       Documentation:
 *       $dklp: reference dk/lp (purple)
 *       $dk: reference Dedukti (purple)
 *       $lp: reference Lambdapi (purple)
 *       $isa: reference Isabelle (yellow)
 *       <$met>metname<$mete>: a scala method (orange,code)
 *       <$metc>metname<$metce>: a scala method inside code (orange)
 *       <$type>typname<$typee>: a scala type (dark orange,bold,code)
 *       <$arg>argname<$arge>: a scala argument (pink,code)
 *       <$argc>argname<$argce>: a scala argument inside code (pink)
 *       <$str>string<$stre>: a scala string (dark green)
 *       <$lpc>code<$lpce>: some Lambdapi code (light blue,code)
 *       <$isac>code<$isace>: some isabelle code (red,code)
 *       -->
 * @define dklp <span style="color:#9932CC;">dk/lp</span>
 * @define dk <span style="color:#9932CC;">Dedukti</span>
 * @define lp <span style="color:#9932CC;">Lambdapi</span>
 * @define isa <span style="color:#FFFF00">Isabelle</span>
 * @define met code><span style="color:#FFA500;"
 * @define metc span style="color:#FFA500;"
 * @define mete /span></code
 * @define metce /span
 * @define type code><span style="color:#FF8C00"><b
 * @define typee /b></span></code
 * @define arg code><span style="color:#FFC0CB;"
 * @define argc span style="color:#FFC0CB;"
 * @define arge /span></code
 * @define argce /span
 * @define str span style="color:#006400;"
 * @define stre /span
 * @define lpc code><span style="color:#87CEFA"
 * @define lpce /span></code
 * @define isac code><span style="color:#D40606"
 * @define isace /span></code
 */
object Translate {
  import Prelude.*
  var global_eta_expand = false


  /* binders */

  /** The bound arguments representing an $isa type variable
   *
   * @param typ the name and stored sort of the $isa type
   * @param tm a term to look into for more sort information about <$arg>typ<$arge>
   * @param impl whether the type argument should be implicit
   * @return a bound variable containing <$arg>typ<$arge> and a possible other argument
   *         storing a class assignment for <$arg>typ<$arge>
   */
  def bound_type_argument(typ : (String, Term.Sort), tm: Term.Term=Term.dummy, impl: Boolean = false): List[Syntax.BoundArg] = typ match {
    case (name,s) =>
      val typarg = Syntax.BoundArg(Some(var_ident(name)), typeT, impl)
      val cname = {
        val c1 = class_of_sort(s)
        if (c1.isDefined) c1 else get_class(tm, name)
      }
      val carg = cname.toList.map { cn =>
        val ty = Syntax.Appl (Syntax.Symb (ref_class_pred_ident (cn) ), Syntax.Var (var_ident (name) ) )
        Syntax.BoundArg (None, ty, true)
      }
      typarg :: carg
  }

  def bound_term_argument(name: String, ty: Term.Typ, impl: Boolean = false): Syntax.BoundArg =
    Syntax.BoundArg(Some(var_ident(name)), eta(typ(ty)), impl)

  def bound_proof_argument(name: String, tm: Term.Term, bounds: Bounds): Syntax.BoundArg =
    Syntax.BoundArg(Some(var_ident(name)), eps(term(tm, bounds)))

  /** Object used as a map between variable names and de Bruijn indices. <br>
   * Represents the context of bound variables. */
  sealed case class Bounds(
    trm: List[String] = Nil,
    prf: List[String] = Nil
  ) {
    /** Adds a mapping between a term variable and a de Bruijn index 
     * @param tm the name of the variable
     * @return the context updated with the new variable */
    def add_trm(tm: String): Bounds = copy(trm = tm :: trm)
    /** Adds a mapping between a proof variable and a de Bruijn index
     * @param pf the name of the variable
     * @return the context updated with the new variable */
    def add_prf(pf: String): Bounds = copy(prf = pf :: prf)

    /** Get a term variable from its de Bruijn index
     * @param idx the de Bruijn index of the variable
     * @return the name of the bound term variable at that index, fetched from a list. */
    def get_trm(idx: Int): String = trm(idx)
    /** Get a proof variable from its de Bruijn index
     *
     * @param idx the de Bruijn index of the variable
     * @return the name of the bound proof variable at that index, fetched from a list. */
    def get_prf(idx: Int): String = prf(idx)
  }


  /* types and terms */
  /** Translates an $isa type to a $dklp simple type 
   * @param ty the $isa type to translate
   * @return the corresponding $dklp simple type
   */
  def typ(ty: Term.Typ): Syntax.Term =
    ty match {
      case Term.TFree(a, _) =>
        Syntax.Var(var_ident(a))
      case Term.Type(c, args) =>
        val id_c = ref_type_ident(c)
        val impl = implArgsMap.getOrElse(id_c,Nil)
        Syntax.appls(Syntax.Symb(id_c), args.map(typ), impl)
      case Term.TVar(xi, _) => error("Illegal schematic type variable " + xi.toString)
    }

  /** Function mapping a $dklp simple type to the type of its elements.
   * @param ty a $dklp term, which must be of type <$lpc>Set<$lpce>
   *           in order for the output to be typable.
   * @return the type <$lpc>El ty<$lpce> of elements of <$arg>ty<$arge>
   */
  def eta(ty: Syntax.Term): Syntax.Typ = Syntax.Appl(etaT, ty)

  /** Translates an $isa term to a $dklp one
   *
   * @param tm the $isa term to translate
   * @param bounds the context of bound variables and their de Bruijn indices
   * @param class_replacement Whether to replace all calls to class constants
   *                          with their alternative for bundled structures
   * @return the corresponding $dklp term
   */
  def term(tm: Term.Term, bounds: Bounds, class_replacement : Boolean = false): Syntax.Term =
    tm match {
      case Term.Const(c, typargs) =>
        val id_c_raw = if (class_replacement && c.contains("_class.")) c + "_alt" else c
        val id_c = ref_const_ident(id_c_raw)
        val impl = implArgsMap.getOrElse(id_c,Nil)
        Syntax.appls(Syntax.Symb(id_c), typargs.map(typ), impl)
      case Term.Free(x, _) =>
        Syntax.Var(var_ident(x))
      case Term.Var(xi, _) => error("Illegal schematic variable " + xi.toString)
      case Term.Bound(i) =>
        try Syntax.Var(var_ident(bounds.get_trm(i)))
        catch { case _: IndexOutOfBoundsException => isabelle.error("Loose bound variable " + i) }
      case Term.Abs(x, ty, b) =>
        Syntax.Abst(bound_term_argument(x, ty), term(b, bounds.add_trm(x), class_replacement))
      case Term.OFCLASS(t, c) =>
        Syntax.Appl(Syntax.Symb(ref_class_ident(Prelude.unqualify(c))), typ(t))
      case Term.App(a, b) =>
        Syntax.Appl(term(a, bounds, class_replacement), term(b, bounds, class_replacement))
    }

  /** Function mapping a $dklp simple type proposition to the type of its proofs.
   *
   * @param tm a $dklp term, which must be of type <$lpc>El prop<$lpce>
   *           in order for the output to be typable.
   * @return the type <$lpc>Prf tm<$lpce> of proofs of <$arg>tm<$arge>
   */
  def eps(tm: Syntax.Term): Syntax.Term =
    Syntax.Appl(epsT, tm)

  /** map to replace calls to useless unnamed proofs with theorem/lemma calls.
   *  Stores both the name and the kind of the object to replace with, to be
   *  fed to <$met><u>[[get_name]]</u><$mete>*/
  var replace_serial: Map[Long,(String,String)] = Map()
  /** Translates an $isa proof to a $dklp term
   *
   * @param prf the $isa proof to translate
   * @param bounds the context of bound variables and their de Bruijn indices
   * @param cont an accumulator storing the result as a function (default: <code>t => t</code>) 
   * @return the corresponding $dklp proof term
   */
  def proof(
    prf: Term.Proof,
    bounds: Bounds,
    cont: Syntax.Term => Syntax.Term = (t => t)/* continuation */
  ): Syntax.Term =
    prf match {
      case Term.PBound(i) =>
        try cont(Syntax.Var(var_ident(bounds.get_prf(i))))
        catch { case _: IndexOutOfBoundsException => isabelle.error("Loose bound variable (proof) " + i) }
      case Term.Abst(x, ty, b) =>
        proof(b, bounds.add_trm(x), prfb =>
          cont(Syntax.Abst(bound_term_argument(x, ty), prfb))
        )
      case Term.AbsP(x, prf, b) =>
        proof(b, bounds.add_prf(x), prfb =>
          cont(Syntax.Abst(bound_proof_argument(x, prf, bounds), prfb))
        )
      case Term.Appt(a, b) =>
        proof(a, bounds, prfa =>
          cont(Syntax.Appl(prfa, term(b, bounds)))
        )
      case Term.AppP(a, b) =>
        val prfa = proof(a, bounds)
        proof(b, bounds, prfb => cont(Syntax.Appl(prfa, prfb)))
      case axm: Term.PAxm =>
        val id = ref_axiom_ident(axm.name)
        val impl = implArgsMap.getOrElse(id,Nil)
        cont(Syntax.appls(Syntax.Symb(id), axm.types.map(typ), impl))
      case thm: Term.PThm =>
        val head = if (!thm.thm_name.is_empty) ref_thm_ident(thm.thm_name.name)
          else replace_serial.get(thm.serial) match {
            case Some((name,kind)) => get_name(name,kind)
            case _ =>
              if (namesMap contains full_name("proof_"+thm.serial.toString, "")) ref_proof_ident(thm.serial)
              else {
                // println("proof "+thm.serial+" is badly identified from theory "+thm.theory_name+thm.types.foldLeft(""){case (s,ty) => s+" "+ty.toString})
                add_proof_ident(thm.serial, current_module)
              }
            }
        val impl = implArgsMap.getOrElse(head,Nil)
        cont(Syntax.appls(Syntax.Symb(head), thm.types.map(typ), impl))
      case _ => error("Bad proof term encountered:\n" + prf)
    }


  /* eta contraction */

  /** Looks if an identifier is used freely in a $dklp term
   * @param term the term in which to search
   * @param ident the identifier to search for
   * @return true if a symbol or free variable named <$arg>ident<$arge> appears in
   *         <$arg>term<$arge> (including in the type of bound variables)
   */
  def lambda_contains(term: Syntax.Term, ident: Syntax.Ident): Boolean =
    term match {
      case Syntax.TYPE => false
      case Syntax.Wildcard => false
      case Syntax.Symb(id) => id == ident
      case Syntax.Var(id)  => id == ident
      case Syntax.Appl(t1, t2, _) => lambda_contains(t1, ident) || lambda_contains(t2, ident)
      case Syntax.Abst(Syntax.BoundArg(arg, ty, _), t) =>
        !arg.contains(ident) && (lambda_contains(ty, ident) || lambda_contains(t, ident))
      case Syntax.Prod(Syntax.BoundArg(arg, ty, _), t) =>
        !arg.contains(ident) && (lambda_contains(ty, ident) || lambda_contains(t, ident))
    }

  /** Replaces all free occurrences of an identifier in a $dklp term with a term
   * @param tm the term in which to replace
   * @param ident the identifier to search for
   * @param value to term to replace all occurrences with
   * @return a copy of the term <$arg>tm<$arge>
   *         wherein any symbol or free variable named <$arg>ident<$arge> is replaced with 
   *         <$arg>value<$arge> (including inside the type of bound variables) */
  def lambda_replace(tm: Syntax.Term, ident: Syntax.Ident, value: Syntax.Term): Syntax.Term =
    tm match {
      case Syntax.TYPE => tm
      case Syntax.Wildcard => tm
      case Syntax.Symb(id) => if (id == ident) value else tm
      case Syntax.Var(id) => if (id == ident) value else tm
      case Syntax.Appl(t1, t2, b) => Syntax.Appl(lambda_replace(t1, ident, value), lambda_replace(t2, ident, value), b)
      case Syntax.Abst(Syntax.BoundArg(arg, ty, b), t) =>
        Syntax.Abst(Syntax.BoundArg(arg, lambda_replace(ty, ident, value), b),
          if (arg.fold(false)(arg => arg == ident)) t
          else lambda_replace(t, ident, value))
      case Syntax.Prod(Syntax.BoundArg(arg, ty, b), t) =>
        Syntax.Prod(Syntax.BoundArg(arg, lambda_replace(ty, ident, value), b),
          if (arg.fold(false)(arg => arg == ident)) t
          else lambda_replace(t, ident, value))
    }

  /**  applies <$met><u>[[lambda_replace]]</u><$mete> in the type of <$arg>arg<$arge>*/
  def lambda_replace_arg(arg: Syntax.BoundArg, ident: Syntax.Ident, value: Syntax.Term): Syntax.BoundArg =
    arg match {
      case Syntax.BoundArg(arg, ty, b) =>
        Syntax.BoundArg(arg, lambda_replace(ty, ident, value), b)
    }

  /** Applies eta-contraction inside all subterms of a $dklp term.
   * @param tm the $dklp term in which to do the contraction
   * @return a copy of <$arg>tm<$arge> in which all subterms of the form
   *         <$lpc>λ x, t x <$lpce> are replaced by t as long as x does not appear in t.*/
  def eta_contract(tm: Syntax.Term) : Syntax.Term =
    tm match {
      case Syntax.Abst(Syntax.BoundArg(Some(id), ty, false), tm2) =>
        eta_contract(tm2) match {
          case Syntax.Appl(tm1, Syntax.Var(id2), _)
            if id == id2 && !lambda_contains(tm1, id) => eta_contract(tm1)
          case tm2 => Syntax.Abst(Syntax.BoundArg(Some(id), eta_contract(ty)), tm2)
        }

      case Syntax.Abst(Syntax.BoundArg(id, ty, impl), tm2) =>
        Syntax.Abst(Syntax.BoundArg(id, eta_contract(ty), impl), eta_contract(tm2))

      case Syntax.Prod(Syntax.BoundArg(id, ty, impl), tm2) =>
        Syntax.Prod(Syntax.BoundArg(id, eta_contract(ty), impl), eta_contract(tm2))

      case Syntax.Appl(t1, t2, impl) => Syntax.Appl(eta_contract(t1), eta_contract(t2), impl)
      case _ => tm
    }

  /** Mutable objects of type A. <br>
  * Simply contains a variable
  * <$arg>value<$arge> of type A. */
  case class Mut[A](var value: A) {}

  /** The way it is used, for now, is the following:
   * if ?1 is a letter, then let ?2 be the next letter in the alphabet (with z -> a),
   * this function changes the string "€?1" into "€?2". It is used for eta-expansion,
   * thus allowing the naming of 26 different unnamed nested arguments at once
   * (parallel arguments receive the same names in that construction).
   * the '€' is there to ensure that the names are fresh I imagine, even though
   * it feels like overkill.
   */
  def update_name(name: String): String = {
    if (!(name.length > 1 && name(0) == '€'))
      error("Broke invariant: " + name)
    var last_non_z = name.length - 1
    while (name(last_non_z) == 'z') {
      last_non_z -= 1
    }
    if (last_non_z == 0) {
      "€" + "a".repeat(name.length)
    } else {
      name.substring(0, last_non_z) + (name(last_non_z).toInt + 1).toChar.toString + "a".repeat(name.length - 1 - last_non_z)
    }
  }

  /** Given a $dklp type and a list of bound arguments it depends on,
   * renames all named arguments by adding a <span style="color:#006400;">'£'</span> in front
   * @param argnames the list of bound arguments to rename, where the type of an argument might depend on the
   *                 arguments before it in the list.
   * @param ret_ty the return type parametrized by <$arg>argname<$arge>
   * @return the updated list and type, where all named variables are prefixed by a
   *         <span style="color:#006400;">'£'</span> and are replaced as such in the type of all arguments
   *         coming after in the list as well as in <$arg>ret_ty<$arge> */
  def alpha_escape(argnames: List[Syntax.BoundArg], ret_ty: Syntax.Typ) : (List[Syntax.BoundArg], Syntax.Typ) =
    argnames match {
      case Nil => (Nil, ret_ty)
      case (arg @ Syntax.BoundArg(None, ty, impl)) :: tl => {
        val (lst, new_ret_ty) = alpha_escape(tl, ret_ty)
        (arg :: lst, new_ret_ty)
      }
      case Syntax.BoundArg(Some(name), ty, impl) :: tl => {
        val new_name = "£" + name
        val (lst, new_ret_ty) = alpha_escape(tl.map(lambda_replace_arg(_, name, Syntax.Var(new_name))), lambda_replace(ret_ty, name, Syntax.Var(new_name)))
        (Syntax.BoundArg(Some(new_name), ty, impl) :: lst, new_ret_ty)
      }
    }

 /** Create and name new arguments to a $dklp function when
   *  they do not already exist (partially applied function)
   *  
   * @param known_argnames the names given to the arguments in the type/proposition
   *                       (in case of a product and not an arrow type).
   *                       Supposed to be renamed using <$met><u>[[alpha_escape]]</u><$mete>
   *                       before being given to the function
   * @param spine The arguments already given to the function
   * @param ctxt a map storing the type of all bound variable in the context
   * @param name_ref the next fresh argument name available of the form "€(a-z)"
   * @param ret_type the codomain of the function being expanded. Allows typing the term
   *                 on the fly. See the example for use.
   *                 
   * @return A list with one variable for each argument that was not given
   *         to the original function.
   *                 
   * @example let <$isac>f : N -> 'A<$isace> then the $dklp type will be
   *          <$lpc>Π A:Set, N → el A<$lpce> so <$arg>known_argnames<$arge> would be
   *          <code>[(A,Set),(_,N)]</code> and <$arg>ret_type<$arge>
   *          would be <$lpc>el A<$lpce>. <br>
   *          But then, one might want to
   *          eta-expand <$lpc>f (N → N → N) 0 0<$lpce>. <br><br>
   *          Upon reading the first argument, the function updates
   *          <$arg>ret_type<$arge> to <$lpc>N → N → N<$lpce>. <br>
   *          When it reaches the end of <$arg>known_argnames<$arge>, it start again
   *          by having <$arg>known_argnames<$arge> be
   *          <code>[(_,N),(_,N)]</code> and will successfuly expand the term to
   *          <$lpc>λ €1:N, f (N → N → N) 0 0 €1<$lpce>.
   *          
   * @see [[eta_expand]] */
  def name_args_of_list(known_argnames: List[Syntax.BoundArg], spine: List[Syntax.Term], ctxt: Map[String, Syntax.Typ], name_ref: Mut[String], ret_type: Syntax.Typ) : List[Syntax.BoundArg] = {
    (known_argnames, spine) match {
      case (Syntax.BoundArg(id, _, _) :: tl, tm :: spine) => {
        val real_id = id.getOrElse("")
        val replaced = tl.map(lambda_replace_arg(_, real_id, tm))
        name_args_of_list(replaced, spine, ctxt, name_ref, lambda_replace(ret_type, real_id, tm))
      }
      case (Syntax.BoundArg(Some(name), ty, impl) :: tl, Nil) => {
        val exp_ty = eta_expand(ty, ctxt, Mut(name_ref.value))
        val res = Syntax.BoundArg(Some(name), exp_ty, impl)
        if (name(0) != '£') error("Invariant broken")
        res :: name_args_of_list(tl, Nil, ctxt + (name -> exp_ty), name_ref, ret_type)
      }
      case (Syntax.BoundArg(None, ty, impl) :: tl, Nil) => {
        val name = name_ref.value
        val exp_ty = eta_expand(ty, ctxt, Mut(name))
        val res = Syntax.BoundArg(Some(name), exp_ty, impl)
        name_ref.value = update_name(name)
        res :: name_args_of_list(tl, Nil, ctxt + (name -> exp_ty), name_ref, ret_type)
      } 
      case (Nil, sp) => name_args(ret_type, spine, ctxt, name_ref)
    }
  }

  /** splits type <$arg>ty<$arge> into arguments and domain, modifies the arguments
   *  with <$met><u>[[alpha_escape]]</u><$mete> and then applies
   *  <$met><u>[[name_args_of_list]]</u><$mete>
   */
  def name_args(ty: Syntax.Typ, spine: List[Syntax.Term], ctxt: Map[String, Syntax.Typ], name_ref: Mut[String]) : List[Syntax.BoundArg] =
    fetch_head_args_type(ty) match {
      case (Nil, _) => Nil
      case (lst, ty) => {
        val (argnames, ret_ty) = alpha_escape(lst, ty)
        name_args_of_list(argnames, spine, ctxt, name_ref, ret_ty)
      }
    }

  /*
  // Apply a list of arguments, given as lambda arguments
  def appls_args(tm: Syntax.Term, args: List[Syntax.BoundArg]): Syntax.Term = {
    val pure_args = args.map { case Syntax.BoundArg(Some(name), _, _) => Syntax.Var(name) case _ => error("oops") }
    val impl_list = args.map { case Syntax.BoundArg(_, _, impl) => impl }
    Syntax.appls(tm, pure_args, impl_list)
  }
   */


  // Drop the first abstractions when there are arguments already, also replacing the abst argname with the argument proper
  // Does not handle it when some abst argname and some arguments share free idents
  // @tailrec
  // def drop(lst: List[Syntax.BoundArg], spine: List[Syntax.Term]): List[Syntax.BoundArg] =
  //   (lst, spine) match {
  //     case (Syntax.BoundArg(id, _, _) :: lst, tm :: spine) =>
  //       val real_id = id.getOrElse("")
  //       val replaced = lst.map(lambda_replace_arg(_, real_id, tm))
  //       drop(replaced, spine)
  //     case (lst, Nil) => lst
  //     case (Nil, _ :: _) => Nil
  //   }

  /** Particular case of <$met><u>[[eta_expand]]</u><$mete> when t
   *  is an application or is a function symbol/variable.
   */
  def eta_expand_appl(t: Syntax.Term, ctxt: Map[String, Syntax.Typ], name_ref: Mut[String]): Syntax.Term = {
    val (head, spine) = Syntax.destruct_appls(t)
    val expanded_args = spine.map { case (arg, impl) => (eta_expand(arg, ctxt, Mut(name_ref.value)), impl) }
    val spine_args = expanded_args.map(_._1)
    head match {
      case Syntax.Symb(id) =>
        val named_args = name_args(global_types(id), spine_args, ctxt, name_ref)
        val applied1 = expanded_args.foldLeft(head) { case (tm, (arg, impl)) => Syntax.Appl(tm, arg, impl) }
        val applied = named_args.foldLeft(applied1) { case (tm, Syntax.BoundArg(Some(name), _, impl)) => Syntax.Appl(tm, Syntax.Var(name), impl) case _ => error("oops") }
        val abstracted = named_args.foldRight(applied)(Syntax.Abst.apply)
        abstracted

      case Syntax.Var(id) =>
        val named_args = name_args(ctxt(id), spine_args, ctxt, name_ref)
        val applied1 = expanded_args.foldLeft(head) { case (tm, (arg, impl)) => Syntax.Appl(tm, arg, impl) }
        val applied = named_args.foldLeft(applied1) { case (tm, Syntax.BoundArg(Some(name), _, impl)) => Syntax.Appl(tm, Syntax.Var(name), impl) case _ => error("oops") }
        val abstracted = named_args.foldRight(applied)(Syntax.Abst.apply)
        abstracted

      case _ =>
        expanded_args.foldLeft(eta_expand(head, ctxt, name_ref)) { case (tm, (arg, impl)) => Syntax.Appl(tm, arg, impl) }
    }
  }

  /** Expand all idents which have a function type,
   * so that the number of arguments they accept is made clear
   *
   * @param tm the $dklp term to expand
   * @param ctxt a map storing the type of all bound variable in the context
   * @param name_ref the next fresh argument name available of the form "€(a-z)"
   *
   * @return a copy of <$arg>tm<$arge> where every function is expanded to
   * a lambda abstraction if it is only partially applied.
   * 
   * @see [[name_args_of_list]]
   */
  def eta_expand(tm: Syntax.Term, ctxt: Map[String, Syntax.Typ], name_ref: Mut[String]): Syntax.Term = {
    tm match {
      case Syntax.TYPE =>
        tm

      case Syntax.Wildcard =>
        tm

      case Syntax.Symb(_) | Syntax.Var(_) | Syntax.Appl(_, _, _) =>
        eta_expand_appl(tm, ctxt, name_ref)

      case Syntax.Abst(Syntax.BoundArg(Some(name), ty, impl), t) =>
        Syntax.Abst(Syntax.BoundArg(Some(name), eta_expand(ty, ctxt, Mut(name_ref.value)), impl), eta_expand(t, ctxt + (name -> ty), name_ref))

      case Syntax.Abst(Syntax.BoundArg(None, ty, impl), t) =>
        Syntax.Abst(Syntax.BoundArg(None, eta_expand(ty, ctxt, Mut(name_ref.value)), impl), eta_expand(t, ctxt, name_ref))

      case Syntax.Prod(Syntax.BoundArg(Some(name), ty, impl), t) =>
        Syntax.Prod(Syntax.BoundArg(Some(name), eta_expand(ty, ctxt, Mut(name_ref.value)), impl), eta_expand(t, ctxt + (name -> ty), name_ref))

      case Syntax.Prod(Syntax.BoundArg(None, ty, impl), t) =>
        Syntax.Prod(Syntax.BoundArg(None, eta_expand(ty, ctxt, Mut(name_ref.value)), impl), eta_expand(t, ctxt, name_ref))
    }
  }
  
  /** <pre><code><$metc>eta_expand<$metce>(<$argc>tm<$argce>) = if (global_eta_expand)
   *  <$metc><u>[[eta_expand]]</u><$metce>(<$argc>tm<$argce>, <$metc>Map<$metce>(), <$metc>Mut<$metce>(<$str>"€a"<$stre>))
   *  else <$argc>tm<$argce></code></pre>
   *  Where global_eta_expand is a variable
   */
  def eta_expand(tm: Syntax.Term) : Syntax.Term = {
    if (global_eta_expand) eta_expand(tm, Map(), Mut("€a")) else tm
  }

  /** Pop all compatible {abstraction, product} arguments and return their list and the remaining terms 
   *
   * @param tm the $dklp term to search into
   * @param ty the type of <$arg>tm<$arge>
   * @return a triplet consisting of a list <$arg>[x1,...,xn]<$arge> of bound arguments, a term <$arg>tm0<$arge>
   *           and a type <$arg>ty0<$arge> such that:<br>
   *           <code><$argc>tm<$argce> = <$lpc>λ (x1 : A1) ... (xn : An), tm0<$lpce></code> and<br>
   *           <code><$argc>ty<$argce> = <$lpc>f1(...(fn(ty0))...)<$lpce></code> where f<sub>i</sub>(T)
   *           is either <$lpc>Ai -> T<$lpce> (in a simply typed functional or propositional way)
   *           or <$lpc>Π xi, T<$lpce>
   */
  def fetch_head_args(tm: Syntax.Term, ty: Syntax.Term) : (List[Syntax.BoundArg], Syntax.Term, Syntax.Term) =
    (tm, ty) match {
      case (Syntax.Abst(arg @ Syntax.BoundArg(_, arg_ty, false), tm0),
        Syntax.Appl(Syntax.Symb("eta"), Syntax.Appl(Syntax.Appl(Syntax.Symb("fun"), arg_ty2, false), ret_ty, false), false))
      if arg_ty == eta(arg_ty2) => {
        val (lst, tm1, ty1) = fetch_head_args(tm0, eta(ret_ty))
        (arg :: lst, tm1, ty1)
      }
      case (Syntax.Abst(arg @ Syntax.BoundArg(_, arg_ty, false), tm0),
        Syntax.Appl(Syntax.Symb("eps"), Syntax.Appl(Syntax.Appl(Syntax.Symb("imp"), arg_ty2, false), ret_ty, false), false))
      if arg_ty == eps(arg_ty2) => {
        val (lst, tm1, ty1) = fetch_head_args(tm0, eps(ret_ty))
        (arg :: lst, tm1, ty1)
      }
      case (Syntax.Abst(arg, tm0), Syntax.Prod(arg2, ty0))
        if arg==arg2 => {
        val (lst, tm1, ty1) = fetch_head_args(tm0, ty0)
        (arg :: lst, tm1, ty1)
      }

      case _ => (Nil, tm, ty)
  }

  /** Pop all product arguments and return their list and the remaining term
   * 
   * @param ty the $dklp type to split
   * @return <code><$metc>fetch_head_args_type<$metce>(<$lpc>Π x1 ... xn, T<$lpce>) =
   *         ([x1, ..., xn],T)</code> including the consideration that <code>xi=None</code> (that is,
   *         <code>_</code>) for simple type arrow and implication
   */
  def fetch_head_args_type(ty: Syntax.Typ) : (List[Syntax.BoundArg], Syntax.Typ) =
    ty match {
      case Syntax.Appl(Syntax.Symb("eta"), Syntax.Appl(Syntax.Appl(Syntax.Symb("fun"), arg_ty, false), ret_ty, false), false) => {
        val (lst, ty1) = fetch_head_args_type(eta(ret_ty))
        (Syntax.BoundArg(None, eta(arg_ty)) :: lst, ty1)
      }
      case Syntax.Appl(Syntax.Symb("eps"), Syntax.Appl(Syntax.Appl(Syntax.Symb("imp"), arg_ty, false), ret_ty, false), false) => {
        val (lst, ty1) = fetch_head_args_type(eps(ret_ty))
        (Syntax.BoundArg(None, eps(arg_ty)) :: lst, ty1)
      }
      case Syntax.Prod(arg, ret_ty) => {
        val (lst, ty1) = fetch_head_args_type(ret_ty)
        (arg :: lst, ty1)
      }

      case _ => (Nil, ty)
    }

  /* notation */

  var notationsSet: Set[String] = Set()

  // Make sure that there are no two notations with the same op string
  // You can edit them here (eg. replace ≡ with ⩵ or _ with __ to avoid their escaping)
  /** Get the $isa symbol for a notation, then change it if needed (to avoid conflicts with $dklp)
   * and make sure it is unique.<br><br>
   * <b>Note: not so sure, is what I can guess from the isabelle code. My best guess is that it's just
   * decoding the notation string so the object name does not appear here, just two encodings of
   * the notation</b>
   * 
   * @param op the string for which there might be a notation defined<br>
   *           <b>Note: This could actually just be the XML encoding of the notation,
   *           whatever that means (if it makes sense).</b>
   * @return the modified notation, after adding it to the variable notationsSet.
   */
  def notations_get(op: String) : String = {
    var op1 = Symbol.decode(op)
    if (op1 == "≡") op1 = "⩵"
    while (notationsSet(op1)) {
      op1 = "~"+op1
    }
    notationsSet += op1
    op1
  }

  /** Translates $isa notation data into $dklp notation data */
  def notation_decl (nota: Export_Theory.Syntax): Option[Syntax.Notation] = nota match { // TODO: Ugly (... but in what sense?)
    case No_Syntax => None
    case Prefix(op) => Some(Syntax.Prefix(notations_get(op), Syntax.defaultPrefixPriority))
    case Export_Theory.Infix(Export_Theory.Assoc.NO_ASSOC,    op, priority) => Some(Syntax.Infix (notations_get(op), priority))
    case Export_Theory.Infix(Export_Theory.Assoc.LEFT_ASSOC,  op, priority) => Some(Syntax.InfixL(notations_get(op), priority))
    case Export_Theory.Infix(Export_Theory.Assoc.RIGHT_ASSOC, op, priority) => Some(Syntax.InfixR(notations_get(op), priority))
    case _ => error("oops")
  }

  var implArgsMap: Map[String, List[Option[Boolean]]] = Map()

  /* type classes */

  /** Maps $isa classes to all their constants */
  var ccsts: mutable.Map[String, Set[String]] = mutable.Map()

  /** Registers an $isa typeclass constant by updating variable <code>Translate.ccsts</code>
   *
   * @param cname the class's name
   * @param cstname the constant's name
   */
  def add_cst(cname: String, cstname: String): Unit = {
    val uqcname = Prelude.unqualify(cname)
    if (ccsts.contains(uqcname)) ccsts(uqcname) += cstname
    else ccsts += uqcname -> Set(cstname)
  }

  /** Maps $isa classes to all their dependencies which have new constants
   * (including possibly themselves) */
  var cdeps: mutable.Map[String, Set[String]] = mutable.Map()
  
  /** Maps sets of <code>cdeps</code> to a canonical $isa class having these deps */
  var canon_map: Map[Set[String], String] = Map()

  /** Computes the $isa class with the most constants
   *
   * @param c1 the name of the first $isa class
   * @param c2 the name of the second $isa class
   * @return <$arg>c1<$arge> if <code>cdeps(<$argc>c1<$argce>)</code> is a subset of
   *         <code>cdeps(<$argc>c2<$argce>)</code>, <$arg>c2<$arge> if
   *         <code>cdeps(<$argc>c2<$argce>)</code> is a strict subset of
   *         <code>cdeps(<$argc>c1<$argce>)</code>, and raises an error if they are
   *         uncomparable or if <$arg>c1<$arge> or <$arg>c2<$arge> is not a typeclass
   */
  def class_max(c1: String, c2: String, context: Option[Term.Term] = None): String = {
    def withdeps[A](c: String)(f: Set[String] => A) = {
      cdeps.get(c) match {
        case Some(s) => f(s)
        case _ => error("unrecognized class: " + c + "\nClasses known:\n" +
          cdeps.foldLeft("")((_ + _._1 + "\n")))
      }
    }

    withdeps(c1) { deps1 =>
      withdeps(c2) { deps2 =>
        val union = deps1 | deps2
        if (union == deps1) c1 else if (union == deps2) c2 else {
          val errormsgpt2 = context.fold("")(Ctxt => s"\nPrinting problematic term: $Ctxt")
          error(s"uncomparable classes: $c1 and $c2$errormsgpt2")
        }
      }
    }
  }

  /** updates variables <code>Translate.allclasses</code> and <code>Translate.cdeps</code>.
   *
   * @param theory The $isa theory to read for classes and class dependencies
   */
  def read_class_deps(theory: Export_Theory.Theory): Unit = {
    for (isaclass <- theory.classes) {
      val cname = isaclass.name
      add_type_ident(cname, current_module)
      val uqcname = Prelude.unqualify(cname)
      cdeps += (uqcname -> (
        if (isaclass.the_content.params.nonEmpty) (
          Set(uqcname)
          )
        else Set()
        ))
    }
    for (crel <- theory.classrel) {
      val uq = Prelude.unqualify
      cdeps(uq(crel.class1)) ++= cdeps(uq(crel.class2))
    }
    for (isaclass <- theory.classes) {
      val uqcname = Prelude.unqualify(isaclass.name)
      val deps = cdeps(uqcname)
      if (deps.nonEmpty && !canon_map.contains(deps)) {
        canon_map += deps -> uqcname
      } 
    }
  }

  /** <code><$metc>dep_representative<$metce>(<$argc>cname<$argce>)</code>
   *  is the unqualified name of a class with the same set of class constants as
   *  <$arg>cname<$arge>, uniquely determined by this set
   *
   * @throws isabelle.error if <$arg>cname<$arge> is not a known class 
   */
  def dep_representative(cname: String): Option[String] = {
    val uqcname = Prelude.unqualify(cname)
    val deps = cdeps.getOrElse(uqcname,error(s"class $uqcname not registered!"))
    val res = canon_map.get(deps)
    if (res.isEmpty && deps.nonEmpty) error("invariant broken for read_class_deps")
    res
  }

  /** Similar to <$met><u>[[dep_representative]]</u><$mete> but with the union of the
   *  sets of class constants of all classes in <$arg>s<$arge> 
   */
  def class_of_sort(s : Term.Sort): Option[String] = {
    val alldeps : Set[String] = s.foldRight(Set()){
      case (cname,curdeps) =>
        val uqcname = Prelude.unqualify(cname)
        val deps = cdeps.getOrElse(uqcname,error(s"class $uqcname not registered!"))
        curdeps.union(deps)
    }
    val res = canon_map.get(alldeps)
    if (res.isEmpty && alldeps.nonEmpty) error("invariant broken for read_class_deps")
    res
  }

  /** Splits an $isa term between head and arguments */
  def destruct_Apps(tm: Term.Term): (Term.Term, Vector[Term.Term]) = tm match {
    case Term.App(a,b) =>
      val (hd,args) = destruct_Apps(a)
      (hd,args :+ b)
    case _ =>
      (tm, Vector.empty)
  }

  /** Reads all classes an $isa type variable must belong to
   * 
   * @param tm the proposition to look in for class assignments
   * @param Tyvar the type variable's name
   * @return the set of classes <code>c</code> <$arg>Tyvar<$arge> must belong to
   *         according to <$arg>tm<$arge>, both because of hypotheses
   *         of the form <code>[[OFCLASS]](<$argc>Tyvar<$argce>,c)</code>
   *         and because of <$arg>Tyvar<$arge> using constants of class c
   */
  def get_cdeps(tm: Term.Term, Tyvar: String): Set[String] = {
    val (hd, args) = destruct_Apps(tm)
    var checkargs = true
    def is_in(s: Set[String])(tm: Term.Term): Boolean = tm match {
      case Term.Const(name, _) =>
        s.contains(name)
      case _ =>
        false
    }
    val uq = Prelude.unqualify
    val hddeps = hd match {
      case Term.OFCLASS(Term.TFree(Tyvar, _), c) =>
        cdeps(uq(c))
      case Term.Const(s"$_.${c}_class$_", List(Term.TFree(Tyvar,_))) if !c.endsWith("intro_of") =>
        cdeps(uq(c))
      case Term.Const(s"$module.class.${name}_axioms",List(Term.TFree(Tyvar, _))) =>
        val deps = cdeps(name)
        val accessible_constants : Set[String] = deps.foldRight(Set())(ccsts(_).union(_))
        if (args.forall(is_in(accessible_constants))) {
          checkargs = false
          deps
        }
        else Set()
      case Term.App(_, _) =>
        error("Invariant broken for destruct_Apps")
      case Term.Abs(_, _, rem) =>
        get_cdeps(rem, Tyvar)
      case Term.Const(_, _) | Term.Var(_, _) | Term.Free(_, _) | Term.Bound(_) | Term.OFCLASS(_, _) =>
        Set()
    }
    val argdeps: Set[String] = if (checkargs) args.foldRight(Set())(get_cdeps(_, Tyvar).union(_)) else Set()
    hddeps.union(argdeps)
  }

  /** The $isa typeclass a type variable needs to belong to.
   *
   * @param tm the proposition context
   * @param Tyvar the name of the type variable
   * @return <code>Some tc</code> if <$arg>tm<$arge> mentions that <$arg>Tyvar<$arge> is
   *         in typeclasses with overall <$met><u>[[class_max]]</u><$mete> <code>tc</code>
   *         and None otherwise
   */
  def get_class(tm: Term.Term, Tyvar: String): Option[String] = {
    val deps = get_cdeps(tm, Tyvar)
    if (deps.isEmpty) None
    else {
      val res = canon_map.get(deps)
      if (res.isEmpty) error(s"Unregistered dependency set\n  Problematic set: $deps")
      else res
    }
  }

  /** Declaration of an $isa typeclass's predicate in $lp
   *
   * @param module the module where the typeclass is defined
   * @param c      the name of the typeclass
   * @return A $lp command declaring the typeclass's associated $lp typeclass.
   */
  def class_pred_decl(module: String, c: String) : Syntax.Command = {
    val id_p = add_class_pred_ident(c,module)
    val ty = Syntax.arrow(typeT,Syntax.TYPE)
    implArgsMap += id_p -> List(Some(true))
    global_types += id_p -> ty
    Syntax.DefableDecl(id_p, ty, tc=true)
  }

  /** Declaration of an $isa typeclass's bundled type in $lp
   *
   * @param module the module where the typeclass is defined
   * @param c      the name of the typeclass
   * @return A list containing a $lp command declaring the typeclass's associated type
   *         <code><$argc>c<$argce>_class_type</code> and one
   *         stating that for all <$lpc>T : <$argc>c<$argce>_class_type<$lpce>,
   *         <$lpc>El T<$lpce> is an instance of <$arg>c<$arge>'s associated $lp typeclass
   */
  def class_type_decl(module: String, c: String): List[Syntax.Command] = {
    val id_type = add_class_type_ident(Prelude.unqualify(c), module)
    val cmd_type = Syntax.Definition(id_type, Nil, Some(Syntax.TYPE), typeT)
    /* Class types are all equal to Set. This means we do not have to deal with subtyping.
    *  For this representation to work, the target language should support some form of meaningful
    *  subtyping (for Rocq, this is done through coercions). All these types should be a subtype of
    *  Set, the type of (pointed) types. Other subtyping should be as indicated by class dependencies.
    *  Note: the result can easily be inconsistent in lambdapi, because we will assert that every
    *  type in (cname)_class_type satisfies (cname)_class's axioms, but every (pointed) type is a
    *  (cname)_class_type. This disappears with mappings by not having Set be a subtype of all class
    *  types. */
    val id_instance = add_const_ident(c + ".class_pred_of_type", module)
    val ty_instance = Syntax.Prod(Syntax.BoundArg(Some("A"),Syntax.Symb(id_type)),
      Syntax.Appl(Syntax.Symb(ref_class_pred_ident(dep_representative(c).get)), Syntax.Var("A")))
    val cmd_instance = Syntax.DefableDecl(id_instance, ty_instance, inst = true)
    List(cmd_type,cmd_instance)
  }

  /** Declaration of a $isa typeclass subtyping
   *
   * @param module the module where the typeclass is defined
   * @param class1 the name of the first typeclass
   * @param class2 the name of the second typeclass
   * @return A $lp command declaring that <$arg>class1<$arge> is a subclass of
   *         <$arg>class2<$arge>
   */
  def classrel_decl(module: String, class1: String, class2: String): Syntax.Command = {
    val id_c = add_class_dep_ident(class1, class2, module)
    val arg = Syntax.BoundArg(Some("A"),typeT)
    def ofclass(cname: String): Syntax.Typ = Syntax.Appl(Syntax.Symb(ref_class_pred_ident(cname)),Syntax.Var("A"))
    val ty = Syntax.Prod(arg,Syntax.arrow(ofclass(class1),ofclass(class2)))
    Syntax.DefableDecl(id_c,ty,inst=true)
  }

  /** Declaration of $isa typeclass's type definition
   *
   * @param module the module where the typeclass is defined
   * @param c      the name of the typeclass
   * @return A $lp command declaring an axiom which states that
   *         for all <$lpc>T : <$argc>c<$argce>_class_type<$lpce>,
   *         <$lpc>El T<$lpce> satisfies <$arg>c<$arge>'s axioms
   */
  def class_type_definition(module: String, c: String): Syntax.Command = {
    val uqc = Prelude.unqualify(c)
    val id_def = add_thm_ident(uqc + "_class_type_def", module)
    val arg = List(Syntax.BoundArg(Some("A"),Syntax.Symb(ref_class_type_ident(uqc))))
    val typ = eps(Syntax.Appl(Syntax.Symb(ref_class_ident(uqc)), Syntax.Symb("A")))
    Syntax.Declaration(id_def, arg, typ)
  }

  /** Declaration of an $isa typeclass in $dklp
   * 
   * @param module the module where the typeclass is defined
   * @param c the name of the typeclass
   * @param d the optional definition of the class (its axioms), can be
   *          <code>None</code>, for example for simply overloading a notation without
   *          giving any axiom.
   * 
   * @return A $dklp command declaring the typeclass as a predicate on types.
   */
  def class_decl(module: String, c: String, d: Option[Term.Term]): Syntax.Command = {
    val out_type = eta(Syntax.Symb(propId))
    val (args,impls) = bound_type_arguments(List(("'a",List(c))))
    val id_c = add_class_ident(Prelude.unqualify(c),module)
    implArgsMap  += id_c -> impls
    global_types += id_c -> args.foldRight(out_type)(Syntax.Prod.apply)
    d match {
      case None => Syntax.Declaration(id_c,args,out_type)
      case Some(d) => Syntax.Definition(id_c,args,Some(out_type),term(d,Bounds()),None)
    }
  }

  /* types */

  /** Declaration of an $isa type in $dklp
   *
   * @param module the module where the type is defined
   * @param c      the name of the type
   * @param args   the list of names of the type variables appearing in the type's definition
   * @param rhs      the optional definition of the type, can be
   *               <code>None</code>, in case of an axiomatic type (bool, for example)
   * @param not the $isa notation for this type
   * 
   * @return A $dklp command declaring the type.
   */
  def type_decl(module: String, c: String, args: List[String], rhs: Option[Term.Typ], not: Export_Theory.Syntax): Syntax.Command = {
    val full_ty = Syntax.arrows(List.fill(args.length)(typeT), typeT)
    val id_c = add_type_ident(c,module)
    implArgsMap  += id_c -> List.fill(args.length)(Some(false))
    global_types += id_c -> full_ty
    val complete_args: List[(String,Term.Sort)] = args.map((_,List()))

    rhs match {
      case None =>
        Syntax.Declaration(id_c, Nil, full_ty, notation_decl(not))
      case Some(rhs) => {
        val translated_rhs = typ(rhs)
        val full_tm : Syntax.Term = bound_type_arguments(complete_args)._1.foldRight(translated_rhs)(Syntax.Abst.apply)
        val (new_args, contracted, ty) = fetch_head_args(eta_expand(eta_contract(full_tm)), full_ty)
        Syntax.Definition(id_c, new_args, Some(ty), contracted, notation_decl(not))
      }
    }
  }

  /* consts */
  /** true if the $isa type <$arg>ty<$arge> contains the variable named <$arg>arg<$arge> */
  def type_contains_arg(ty: Term.Typ, arg: String): Boolean =
    ty match {
      case Term.TFree(name, _) => name == arg
      case Term.Type(_, args) => args.exists(type_contains_arg(_, arg))
      case Term.TVar(_, _) => error("False assertion")
    }
  
  /** checks if a type variable appears in an $isa type as a domain type
   * 
   * @param ty the type to search into
   * @param arg the name of the variable
   * @return true if <code><$argc>ty<$argce> = <$isac>"x1 ⇒ ... ⇒ arg ⇒ ..."<$isace></code>
   */
  @tailrec
  def type_contains_arg_as_arg(ty: Term.Typ, arg: String): Boolean =
    ty match {
      case Term.TVar(_, _) => error("False assertion")
      case Term.Type(Pure_Thy.FUN, List(arg1, arg2)) => type_contains_arg(arg1, arg) || type_contains_arg_as_arg(arg2, arg)
      case _ => false
    }

  /** Which type arguments of a constant can be implicit.
   * 
   * @param typargs the name of the type variables
   *                appearing in the type of the constant
   * @param ty the $isa type of the constant
   * @return a list of booleans, true for implicit type constants and false otherwise
   */
  def const_implicit_args(typargs: List[String], ty: Term.Typ): List[Boolean] = {
    var canStillBeImplicit = true // No implicit arg after a non-implicit one
    typargs.map(arg => {
      canStillBeImplicit &&= type_contains_arg_as_arg(ty, arg)
      canStillBeImplicit
    })
  }

  /** List of bound type arguments
   *
   * @param args The list of names of the type arguments
   * @param impl Whether the arguments are implicit
   * @param tm A proof term, potentially giving information about $isa typeclasses for each argument.
   * @return A list of bound arguments, containing all the types and also possibly
   *         typeclass witnesses
   * @see <$met><u>[[bound_type_argument]]</u><$mete>
   */
  def bound_type_arguments(args: List[(String,Term.Sort)])
  (tm: Term.Term = Term.dummy, impl: List[Boolean] = args.map(_ => false)): (List[Syntax.BoundArg],List[Option[Boolean]]) =
    (args, impl) match {
      case (Nil, Nil) => (Nil,Nil)
      case (arg :: args, impl :: impls) => {
        val (recres1, recres2) = bound_type_arguments(args)(tm, impls)
        val res = bound_type_argument(arg, tm, impl)
        val newimpls = if (res.length == 1) List(Some(impl)) else List(Some(impl), None)
        (res ::: recres1, newimpls ::: recres2)
      }
      case (Nil, _) => isabelle.error("Implicit list too long.")
      case (_, Nil) => isabelle.error("Implicit list too short.")
    }

  /** <code><$metc>bound_type_arguments<$metce>(<$argc>args<$argce>) =
   * <$metc><u>[[bound_type_arguments]]</u><$metce>(<$argc>args<$argce>)()
   */
  def bound_type_arguments(args: List[(String,Term.Sort)]) : (List[Syntax.BoundArg],List[Option[Boolean]]) =
    bound_type_arguments(args)()

  /** Set of known $isa typeclass instances */
  var all_instances: Set[(String,String)] = Set()
  /** looks in set [[Translate.all_instances]] whether a type is already
   *  known to be an instance of an $isa class while updating it if not
   */
  def new_instance(type_name: String, uqcname: String): Boolean = {
    val key = (type_name,uqcname)
    val is_new = !all_instances.contains(key)
    if (is_new) all_instances += key
    is_new
  }
  /** List of the current $isa theory's arities (typeclass instances) */
  var current_arities: List[Export_Theory.Arity] = List()
  
  /** Uses [[Translate.current_arities]] to find an
   *  instantiation's sort assignments, returning the corresponding
   *  <$met><u>[[bound_type_arguments]]</u><$mete>*/
  def args_from_arity(iname: String, cname: String, impl: List[Boolean] = List()): (List[Syntax.BoundArg],List[Option[Boolean]]) = {
    @tailrec
    def rec_ver(l: List[Export_Theory.Arity]): (List[Syntax.BoundArg],List[Option[Boolean]]) = l match {
      case Export_Theory.Arity(type_name, _, codomain, prop) :: _ if type_name.endsWith(iname) &&
        codomain.split('.').last == cname =>
        if (impl.isEmpty) bound_type_arguments(prop.typargs) else bound_type_arguments(prop.typargs)(impl = impl)
      case _ :: rest => rec_ver(rest)
      case _ =>
        val printarities = current_arities.mkString(s"\n\n")
        error(s"Arity not found for type $iname of class $cname.\nKnown arities:\n$printarities")
    }
    rec_ver(current_arities)
  }
  
  /** Declaration of an $isa constant in $dklp
   *
   * @param module the module where the constant is defined
   * @param c      the name of the constant
   * @param typargs   the list of names of the type variables appearing in the constant's type
   * @param rhs    the optional definition of the constant, can be
   *               <code>None</code>, in case of an axiomatic constant (equality, for example)
   * @param not    the $isa notation for this constant
   * @return A $dklp command declaring the constant.
   */
  def const_decl(module: String, c: String, typargs: List[(String,Term.Sort)], ty: Term.Typ, rhs: Option[Term.Term],
                 not: Export_Theory.Syntax, ignore_classes: Boolean = false): Syntax.Command = {
    val id_c = add_const_ident(c,module)
    val impl = const_implicit_args(typargs.map(_._1), ty)
    val (bound_args, full_impls) = (typargs,impl,c) match {
      case (List((tyname,tysort)),List(imp),s"${cname}_class$_") if !ignore_classes =>
        (bound_type_argument((tyname,cname :: tysort), impl = imp),
          List(Some(imp), None))
      case (_,_,s"$_.${cname}_${iname}_inst$_") if !(iname + cname).contains('.') =>
        args_from_arity(iname,cname,impl)
      case _ =>
        bound_type_arguments(typargs)(impl=impl)
    }
    implArgsMap += id_c -> full_impls
    val full_ty = bound_args.foldRight(eta(typ(ty)))(Syntax.Prod.apply)
    val contracted_ty = eta_expand(eta_contract(full_ty))
    global_types += id_c -> contracted_ty
    rhs match {
      case None =>
        Syntax.DefableDecl(id_c, contracted_ty, not=notation_decl(not))
      case Some(rhs) => {
        val translated_rhs = term(rhs, Bounds())
        val full_tm = bound_args.foldRight(translated_rhs)(Syntax.Abst.apply)
        val (new_args, contracted, final_ty) = fetch_head_args(eta_expand(eta_contract(full_tm)), contracted_ty)
        Syntax.Definition(id_c, new_args, Some(final_ty), contracted, notation_decl(not))
      }
    }
  }
  
  /** like <$met><u>[[const_decl]]</u><$mete> but declares an alternative version of the symbol
   *  for bundled structures of class <$arg>class_name<$arge>, using
   *  alternative versions of all class constants appearing in the symbol's
   *  definition */
  def const_of_class_type_decl(module: String, class_name: String, const_name: String,
                               typargs: List[(String, Term.Sort)], ty: Term.Typ, body: Term.Term): Syntax.Command = {
    val name = add_const_ident(const_name + "_alt", module)
    val impl = const_implicit_args(typargs.map(_._1), ty)
    val class_type_ref = Syntax.Symb(ref_class_type_ident(Prelude.unqualify(class_name)))
    val (full_args, full_impls) = (typargs,impl) match {
      case (List((tyname,_)),List(imp)) =>
        (List(Syntax.BoundArg(Some(var_ident(tyname)), class_type_ref, imp)), List(Some(imp)))
      case _ =>
        bound_type_arguments(typargs)(impl=impl) match {
          case (Syntax.BoundArg(id, _, imp)::_::args, _::None::impls) =>
            (Syntax.BoundArg(id, class_type_ref, imp)::args,Some(imp)::impls)
          case _ =>
            error("not enough arguments arguments in class parameter/definition")
        }
    }
    val full_tm = full_args.foldRight(term(body,Bounds()))(Syntax.Abst.apply)
    val full_ty = full_args.foldRight(eta(typ(ty)))(Syntax.Prod.apply)
    val contracted_ty = eta_expand(eta_contract(full_ty))
    implArgsMap += name -> full_impls
    global_types += name -> contracted_ty
    val (new_args, contracted, final_ty) = fetch_head_args(full_tm, contracted_ty)
    Syntax.Definition(name,new_args,Some(final_ty),contracted)
  }

  /* theorems and proof terms */
  /** Declaration of an $isa theorem/axiom in $dklp
   * 
   * @param s the name of the theorem/axiom
   * @param prop the $isa theorem/axiom
   * @param prf_opt the optionnal $isa proof of the theorem/axiom
   * @return a $dklp command declaring the symbol <$arg>s<$arge>, possibly with a translation of
   *         <$arg>prf_opt<$arge> as definitional body.
   */
  def stmt_decl(s: String, prop: Export_Theory.Prop, prf_opt: Option[Term.Proof], original_name: String = ""): Syntax.Command = {
    val typargs = prop.typargs
    val (bound_args, impls) = (typargs, original_name) match {
      case (List((tyname,tysort)),s"${cname}_class$_") if !cname.endsWith("intro_of")=>
        (bound_type_argument((tyname,cname :: tysort)),
          List(Some(false), None))
      case (_,s"$_.${cname}_${iname}_inst$_") if !(iname + cname).contains('.') =>
        args_from_arity(iname,cname)
      case _ =>
        bound_type_arguments(typargs)(tm=prop.term)
    }
    val args = bound_args ::: prop.args.map(arg => bound_term_argument(arg._1, arg._2))

    val full_ty = args.foldRight(eps(term(prop.term, Bounds())))(Syntax.Prod.apply)
    val contracted_ty = eta_expand(eta_contract(full_ty))

    implArgsMap  += s -> impls
    global_types += s -> contracted_ty

    try prf_opt match {
      case None => {
        val (new_args, final_ty) = (Nil, contracted_ty)
        Syntax.Declaration(s, new_args, final_ty)
        }
      case Some(prf) => {
        val translated_rhs = proof(prf, Bounds())
        val full_prf : Syntax.Term = args.foldRight(translated_rhs)(Syntax.Abst.apply)
        val (new_args, contracted, final_ty) = fetch_head_args(eta_expand(eta_contract(full_prf)), contracted_ty)
        Syntax.Theorem(s, new_args, final_ty, contracted)
      }
    }
    catch { case e : Throwable => e.printStackTrace()
      error("oops in " + quote(s)) }
//    catch { case ERROR(msg) => error(msg + "\nin " + quote(s)) }
  }

  /** like <$met><u>[[stmt_decl]]</u><$mete> but declares an alternative version of the symbol
   * for bundled structures of class <$arg>class_name<$arge>, using
   * alternative versions of all class constants appearing in the symbol's
   * type */
  def stmt_of_class_type_decl(module: String, thm_name: String, sortmap: Map[String,String], prop: Export_Theory.Prop, prf: Term.Proof): Syntax.Command = {
    val name = add_thm_ident(thm_name + "_alt", module)
    val bound_args = prop.typargs.map( (tvar,_) =>
      Syntax.BoundArg(Some(var_ident(tvar)), sortmap.get(tvar).fold(typeT)(cname => Syntax.Symb(ref_class_type_ident(cname))), true)
    )
    val args = bound_args ::: prop.args.map(arg => bound_term_argument(arg._1, arg._2))
    val full_ty = args.foldRight(eps(term(prop.term, Bounds(), class_replacement = true)))(Syntax.Prod.apply)
    val contracted_ty = eta_expand(eta_contract(full_ty))
    val translated_rhs = proof(prf, Bounds())
    val full_prf = args.foldRight(translated_rhs)(Syntax.Abst.apply)
    val (new_args, contracted, final_ty) = fetch_head_args(eta_expand(eta_contract(full_prf)), contracted_ty)
    Syntax.Theorem(name, new_args, final_ty, contracted)
  }
}
