/** Generator of dk or lp file for a session **/

package isabelle.dedukti

import isabelle.*
import isabelle.Term.*
import isabelle.Export_Theory.*

import java.io.{Writer,*}
import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.control.Breaks.*

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
object Exporter {

  /** Compute the biggest theorem serial occurring in
   *  an $isa proof */
  def max_serial(proof: Term.Proof): Long = proof match {
    case PThm(serial,_,_,_) => serial
    case Appt(p,_) => max_serial(p)
    case AppP(p,q) => Math.max(max_serial(p), max_serial(q))
    case Abst(_,_,b) => max_serial(b)
    case AbsP(_,_,b) => max_serial(b)
    case _ => 0
  }

  /** Recursively splits an $isa term between its head and its arguments.
   * 
   * @param t the term being split
   * @param args the list of arguments encountered so far (default: <$met>Nil<$mete>)
   *             
   * @return the couple of the head function and the list of arguments it is applied to
   *         
   * @see <$met><u>[[isabelle.dedukti.Syntax.destruct_appls]]</u><$mete> for $dklp terms
   */
  @tailrec
  def head_args(t:Term, args:List[Term]=List()): (Term,List[Term]) = {
    t match {
      case App(u,v) => head_args(u,v::args)
      case _ => (t,args)
    }
  }

  /** True if the $isa term <$arg>t<$arge> is a free term variable or <$isac>Pure.type<$isace> */
  def is_Free_or_TYPE(t:Term): Boolean = {
    t match {
      case Free(_,_) => true
      case Term.Const(Pure_Thy.TYPE, List(TFree("'a",Nil))) => true
      case _ => false
    }
  }

  /** tell if an $isa type is a free variable */
  def is_TFree(t:Typ): Boolean = {
    t match {
      case TFree(_,_) => true
      case _ => false
    }
  }

  /** Replace all free variables in an $isa term by De Bruijn indices (therefore binding them)
   * 
   *  @param revargs the list of bound variables, to which those bound in the term are added
   *         during the process. */
  def debruijn(revargs:List[Term], t:Term): Term = {
    t match {
      case Free(_,_) => Bound(revargs.indexOf(t))
      case App(u,v) => App(debruijn(revargs,u),debruijn(revargs,v))
      case Abs(n,ty,b) => Abs(n,ty,debruijn(Free(n,ty)::revargs,b))
      case _ => t
    }
  }

  /** build an $isa abstraction assuming that <$arg>arg<$arge> is a free variable */
  def abs(b:Term, arg:Term): Term = {
    arg match {
      case Free(n,ty) => Abs(n,ty,b)
      case _ => error("exporter.abs: not a free variable "+arg.toString)
    }
  }

  /** whether an $isa term is a specific (possibly eta_expanded) free variable
   * 
   * @param term the $isa term to test
   * @param name the free variable name to search for
   * @param n_Abs the amount of Abs cases encountered so far
   * @param n_App the amount of App cases encountered so far
   * @return true if <code><$argc>term<$argce>=eta_k1(...(eta_kn(<$metc>Free<$metce>(<$argc>name<$argce>)))...)</code>
   *         where <code>eta_i(f)=λx1 ... xi, f x1 ... xi</code>
   */
  @tailrec
  def is_abstract_free(term: Term, name: String, n_Abs: Int = 0, n_App: Int = 0): Boolean = term match {
      case Abs(_, _, remainder) => is_abstract_free(remainder, name, n_Abs+1, n_App)
      case App(remainder, Bound(m)) => n_Abs > n_App && m == n_App && is_abstract_free(remainder, name, n_Abs, n_App+1)
      case Free(othername, _) => n_Abs == n_App && name == othername
      case _ => false
    }

  @tailrec
  def get_call(proof: Term.Proof, args: List[String]): Option[PThm] = (proof, args) match {
    case (thm: PThm, Nil) =>
      Some(thm)
    case (Appt(proofrem, arg), argname :: argsrem) if is_abstract_free(arg, argname) =>
      get_call(proofrem, argsrem)
    case _ =>
      None
  }
  /** Export or read a specific $isa session
   *
   * @param session the $isa session to read
   * @param parent the parent session unless it is Pure
   * @param theory_graph the dependency graph of the theories in the session
   * @see <$met><u>[[Generator.generator]]</u><$mete>
   */
  def exporter(
    options: Options,
    session: String,
    parent: Option[String],
    theory_graph: Document.Node.Name.Graph[Unit],
    translate: Boolean,
    term_cache: Term.Cache = Term.Cache.make(),
    progress: Progress = new Progress(),
    dirs: List[Path] = Nil,
    to_lp: Boolean = true,
    use_notations: Boolean = true,
    eta_expand: Boolean = false,
    with_class_types: Boolean = false,
    verbose: Boolean = false,
    outdir: String = "",
  ): Unit = {

    /** depending on variable <code>to_lp</code>, opens an [[LP_Writer]] or a [[DK_Writer]] */
    def new_Writer(writer: Writer): Abstract_Writer =
      if (to_lp) {
        writer.write("""flag "eta_equality" on;""")
        writer.write('\n')
        new LP_Writer(use_notations,writer)
      }
      else new DK_Writer(writer)

    /** .lp or .dk depending on variable <code>to_lp</code> */
    val extension: String = if (to_lp) ".lp" else ".dk"
    /** .lpo or .dko depending on variable <code>to_lp</code> */
    val exto: String = extension+"o"

    /** from an $isa equality axiom <$isac>Pure.eq[eqtys] lhs rhs<$isace>
     * where <code>lhs = <$isac>c[tys] x1 .. xn<$isace></code> with tys and xj variables,
     * returns <code>(c,dfn,eqtys,lhs)</code> where
     * <code>dfn=<$isac>λ x1...λ xn. rhs<$isace></code>
     *
     * @define isa <span style="color:#FFFF00">Isabelle</span>
     * @define isac code><span style="color:#D40606"
     * @define isace /span></code
     */
    def is_eq_axiom(a:Entity[Axiom]): Option[(String,Term,List[Typ],Term)] = {
      if (!(a.name.endsWith("_def") || a.name.endsWith("_def_raw") || a.name.endsWith("_dict"))) None
      else a.the_content.prop.term match {
        case App(App(Term.Const(id, _), _), _) if id != "Pure.eq" =>
          if (verbose) progress.echo("axiom " + a.name + ": cannot extract definition because it is headed by " + id + " instead of Pure.eq")
          None
        case App(App(Term.Const(_, eqtys), lhs@OFCLASS(_, name)), rhs) =>
          Some(name + "_class", rhs, eqtys, lhs)
        case App(App(Term.Const(_, eqtys), lhs), rhs) =>
          head_args(lhs) match {
            case (Term.Const(n, tys), args) if !(tys.forall(is_TFree) && args.forall(is_Free_or_TYPE)) =>
              if (verbose) progress.echo("axiom " + a.name + ": cannot extract definition because it is not applied to free variables\n  axiom: " + a.the_content.prop.term.toString + "\n  type arguments: " + tys.toString + "\n  term arguments: " + args.toString)
              None
            case (h @ Term.Const(n, tys), args @ List(Term.Const(Pure_Thy.TYPE, List(TFree(_, Nil))))) =>
              if (verbose) progress.echo("  head: " + h.toString + "\n  args: " + args.toString + "\n  rhs: " + rhs.toString)
              None
            case (h @ Term.Const(n, tys), args) =>
              if (verbose) progress.echo("  head: " + h.toString + "\n  args: " + args.toString + "\n  rhs: " + rhs.toString)
              val revargs = args.reverse
              val rhs2 = debruijn(revargs, rhs)
              val dfn = revargs.foldLeft(rhs2)(abs)
              Some(n, dfn, eqtys, lhs)
            case _ => None
          }
        case _ => None
      }
    } 
    
    val notations: mutable.Map[Syntax.Ident, Syntax.Notation] = mutable.Map()
    Translate.global_eta_expand = eta_expand
    val build_results =
      Build.build(options, selection = Sessions.Selection.session(session),
        dirs = dirs, progress = progress)
    val store = build_results.store
    val session_background =
      Document_Build.session_background(options, session, dirs = dirs)
    val ses_cont = Export.open_session_context(store, session_background)
    val thys = theory_graph.topological_order
    val theory_names = thys.map(node_name => node_name.toString)

    /** Opens for writing a .dk.part or .lp.part file associated to a session or theory,
     *  which, when closed, is copied to the corresponding .dk or .lp file
     */
    def new_part_writer(name: String) =
      new Part_Writer(Path.explode(outdir+Prelude.mod_name(name)+extension))

    /** Reads the proof of a lemma and uses it
     *
     * @param serial the integer serial of the lemma
     * @param f the function to apply to the proof and proposition
     * @return the application of f to the proof numbered <$arg>serial<$arge> and to the
     *         proposition it proves
     * @throws isabelle.error if no proof can be found
     * @define arg code><span style="color:#FFC0CB;"
     * @define arge /span></code
     */
    def use_proof[A](theory_name: String, serial: Long)(f: (Term.Proof,Prop) => A): A = {
      read_proof(ses_cont, Thm_Id(serial,theory_name), other_cache=Some(term_cache)) match {
        case Some(proof) =>
          f(proof.proof,proof.prop)
        case None =>
          error("proof "+serial+" not found!")
      }
    }

    /** Reads the proof of theorem <code><span style="color:#FFC0CB;">serial</span></code>
     *  if there is one and returns a command declaring it as a lemma or axiom 
     */
    def decl_proof(serial: Long, theory_name: String): Syntax.Command = use_proof(theory_name,serial){
      case (proof,prop) => Translate.stmt_decl(Prelude.ref_proof_ident(serial),prop,Some(proof))
    }

    /** map theory_name -> set of proofs in increasing order */
    val map_theory_proofs = mutable.Map[String, mutable.SortedSet[Long]]()
    // add an entry for each theory
    for (theory_name <- theory_names) {
      map_theory_proofs += (theory_name -> mutable.SortedSet[Long]())
    }

    /** the name of the module for orphan proofs (not in the current session theories) */
    val mod_name_orphans = Prelude.mod_name(session)+"_orphans"

    /** commands for orphan proofs */
    val orphan_commands = mutable.Queue[Syntax.Command]()

    // record proof idents and update map_theory_proofs or orphan_commands
    Prelude.set_theory_session(mod_name_orphans,session)
    Prelude.set_current_module(mod_name_orphans)
    for (entry_name <- ses_cont.entry_names()) {
      if (entry_name.name.startsWith(Export.PROOFS_PREFIX)) {
        val serial = entry_name.name.substring(7).toLong
        val theory_name = entry_name.theory
        if (verbose) progress.echo("  proof " + serial)
        if (map_theory_proofs.keySet.contains(theory_name)) {
          Prelude.add_proof_ident(serial,theory_name)
          map_theory_proofs(theory_name) += serial
        } else {
          Prelude.add_proof_ident(serial,mod_name_orphans)
          orphan_commands += (decl_proof(serial,theory_name))
        }
      }
    }

    if (!translate) { /* if translate is false, just update maps to keep in mind
                         the translated names of the session, but do not
                         write anything anywhere
                      */
      progress.echo("Start reading session "+session)
      for (thy <- thys) {
        val theory_name = thy.toString

        /** Same as remove_useless_proofs (below) but only update the Translate.replace_serial map */
        @tailrec
        def update_useless_proofs(name: String, proof: Term.Proof, args: List[String]): Unit =
          for (PThm(serial, origin_theory, thm_name, _) <- get_call(proof,args)
               if thm_name.is_empty
               if origin_theory == theory_name
               if !Translate.replace_serial.contains(serial)){
            Translate.replace_serial += serial -> (name,Export_Theory.Kind.THM)
            val (next_proof,next_args) = use_proof(theory_name, serial) {
              case (prf, prop) => (prf, prop.args.map(_._1).reverse)
            }
            update_useless_proofs(name, next_proof, next_args)
          }

        progress.echo("Start reading theory "+theory_name)
        val provider = ses_cont.theory(theory_name, other_cache=Some(term_cache))
        val theory = read_theory(provider)
        Translate.current_arities = theory.arities
        for (a <- theory.types) {
          if (verbose) progress.echo("  "+a.toString+" "+a.serial)
          Translate.type_decl(theory_name, a.name, a.the_content.args, None, No_Syntax)
        }
        Translate.read_class_deps(theory)
        for ((_, c) <- Translate.canon_map if theory.classes.exists(tc => Prelude.unqualify(tc.name) == c)) {
          Translate.class_pred_decl(theory_name, c)
        }
        for (a <- theory.consts) {
          if (verbose) progress.echo("  " + a.toString + " " + a.serial)
          val cst = a.the_content
          val name = if (a.name.endsWith("_class")) Prelude.unqualify(a.name) else a.name
          Translate.const_decl(theory_name, name, cst.typargs, cst.typ, None, No_Syntax)
          a.name match {
            case s"${cname}_class.$rest" =>
              Translate.add_cst(cname, a.name)
              val altname = a.name + "_alt"
              Translate.const_decl(theory_name, altname, cst.typargs, cst.typ, None, No_Syntax, ignore_classes = true)
            case _ =>
          }
        }
        if (with_class_types) {
          for (c <- theory.classes if Translate.cdeps(Prelude.unqualify(c.name)).nonEmpty) {
            if (verbose) progress.echo("  type for class " + c.name)
            Translate.class_type_decl(theory_name, c.name)
            Prelude.add_thm_ident(Prelude.unqualify(c.name) + "_class_type_def", theory_name)
          }
        }
        for (a <- theory.axioms) {
          if (verbose) progress.echo("  "+a.toString+" "+a.serial)
          Translate.stmt_decl(Prelude.add_axiom_ident(a.name, theory_name), a.the_content.prop, None, a.name)
        }
        for (a <- theory.thms) {
          if (verbose) progress.echo("  " + a.toString + " " + a.serial)
          val thm = a.the_content
          Translate.stmt_decl(Prelude.add_thm_ident(a.name, theory_name), thm.prop, None, a.name)
          update_useless_proofs(a.name, thm.proof, thm.prop.args.map(_._1).reverse)
        }
        /* Remove useless proofs that were not reached by update_useless_proofs.
        *  These are normally removed by write_proof. */
        for (prf <- map_theory_proofs(theory_name)
             if (!Translate.replace_serial.contains(prf))) {
          if (verbose) progress.echo("  proof " + prf)
          use_proof(theory_name, prf) {
            case (proof, prop) => get_call(proof, prop.args.map(_._1).reverse) match {
              case Some(PThm(serial, _, thm_name, _)) =>
                val new_mapping = {
                  if (!thm_name.is_empty) (thm_name.name, Export_Theory.Kind.THM)
                  else Translate.replace_serial.getOrElse(serial, (f"proof_$serial", ""))
                }
                Translate.replace_serial += prf -> new_mapping
                case _ =>
            }
          }
        }
        progress.echo("End reading theory "+theory_name)
      }
      progress.echo("End reading session "+session)
    }

    else {
      progress.echo("Start translating session "+session)
      /** name of the module for this session */
      val mod_name_session = "session_"+Prelude.mod_name(session)

      // set up generation of makefile script to check Dedukti or Lambdapi files
      val checkstr : String = (if (to_lp) "lpcheck_" else "dkcheck_")
      val filename = checkstr + session + ".mk"
      progress.echo("Start writing "+filename)
      val file = new File(outdir+filename)
      val mk = new BufferedWriter(new FileWriter(file))
      // get the base dependencies
      val base_deps: String = parent match {
        case Some(anc) =>
          // Dependency of the orphan file
          mk.write("$(OUT_DIR)/" + mod_name_orphans + exto + " : $(OUT_DIR)/session_" + Prelude.mod_name(anc) + exto)
          // write orphan proofs
          using(new_part_writer(mod_name_orphans)) { part_writer =>
            progress.echo("Start writing " + mod_name_orphans + extension)
            val orphan_writer = new_Writer(part_writer)
            orphan_writer.require("session_" + anc)
            for (cmd <- orphan_commands) {
              orphan_writer.command(cmd, notations)
            }
            progress.echo("End writing " + mod_name_orphans + extension)
          }
          " $(OUT_DIR)/session_" + Prelude.mod_name(anc) + exto + " $(OUT_DIR)/" + mod_name_orphans + exto
        case _ =>
          " $(OUT_DIR)/STTfa" + exto
      }
      /** Write makefile dependencies, either from predecessors in the dependency graph or
       *  from base dependencies in case of no predecessor
       *
       *  @param filename the file for which to write dependencies
       *  @param predecessors the list of its predecessors in the dependency graph
       */
      def mk_deps(filename: String, predecessors: List[Document.Node.Name]): Unit = {
        mk.write("\n$(OUT_DIR)/" + filename + exto + " :")
        if (predecessors.isEmpty) mk.write(base_deps)
        else for (pred <- predecessors) mk.write(" $(OUT_DIR)/" + Prelude.mod_name(pred.toString) + exto)
      }

      mk_deps(mod_name_session,thys)
      /* Open a dk file S for the session, then translate each theory of the
       * session in a dk file T, and simply import module T in S
       */
      using(new_part_writer(mod_name_session)) { part_writer1 =>
        progress.echo("Start writing "+mod_name_session+extension)
        val session_writer = new_Writer(part_writer1)

        for (thy <- thys) {
          val theory_name = thy.toString
          progress.echo("Start reading theory "+theory_name)
          val provider = ses_cont.theory(theory_name, other_cache=Some(term_cache))
          val theory = read_theory(provider)
          session_writer.require(theory_name)
          val mod_name_theory = Prelude.mod_name(theory_name)
          
          mk_deps(mod_name_theory, theory_graph.imm_preds(thy).toList)
          using(new_part_writer(mod_name_theory)) { part_writer2 =>
            val writer = new_Writer(part_writer2)
            progress.echo("Start writing "+mod_name_theory+extension)
            writer.comment("Theory "+theory_name)
            // write module dependencies
            if (parent.isDefined) writer.require(mod_name_orphans)
            else writer.require("STTfa")
            for (node_name <- theory_graph.imm_preds(thy)) {
              writer.require(node_name.toString)
            }
            Prelude.set_current_module(theory_name)
            // translate types
            writer.nl()
            writer.comment("Types")
            for (a <- theory.types) {
              if (verbose) progress.echo("  "+a.toString+" "+a.serial)
              val cmd = Translate.type_decl(theory_name, a.name, a.the_content.args, a.the_content.abbrev, a.the_content.syntax)
              writer.command(cmd,notations)
            }
            /** map constant name -> definition */
            var map_cst_dfn:Map[String,Term] = Map()
            /** map definitional axiom name -> (type variables, the term it defines) */
            var map_axm_eqtyp:Map[String,(List[Typ],Term)] = Map()
            // check constant definitions
            for (a <- theory.consts) {
              a.the_content.abbrev match {
                case Some(d) =>
                  if (verbose) progress.echo(a.name+" has definition")
                  map_cst_dfn += (a.name -> d)
                case _ =>
              }
            }
            // check axioms
            for (a <- theory.axioms) {
              is_eq_axiom(a) match {
                case Some(n,d,eqtys,lhs) =>
                  if (verbose) progress.echo(n+" is defined by axiom "+a.name)
                  map_cst_dfn += (n -> d)
                  map_axm_eqtyp += (a.name -> (eqtys,lhs))
                case None =>
              }
            }
            // ordering on entities
            def le[A<:Content[A]](e1:Entity[A], e2:Entity[A]) = e1.serial <= e2.serial
            // read class dependencies
            Translate.read_class_deps(theory)
            // write class predicates and their relations
            writer.nl()
            writer.comment("Class predicates")

            for ((_,c) <- Translate.canon_map if theory.classes.exists(tc => Prelude.unqualify(tc.name) == c)) {
              val cmd = Translate.class_pred_decl(theory_name, c)
              writer.command(cmd, notations)
            }
            
            // Dependencies
            writer.nl()
            writer.comment("Class relations")
            for {
              (deps1,cname1) <- Translate.canon_map
              (deps2,cname2) <- Translate.canon_map
              if cname1 != cname2
              if theory.classrel.exists{
                case Classrel(c1,c2,_) =>
                  val uq = Prelude.unqualify
                  Translate.cdeps(uq(c1)) == deps1 &&
                  Translate.cdeps(uq(c2)) == deps2
              }
            } {
              if (verbose) progress.echo("  " + cname1 + " -> " + cname2)
              val cmd = Translate.classrel_decl(theory_name, cname1, cname2)
              writer.command(cmd, notations)
            }
            
            // (Optional) Class types
            if (with_class_types) {
              writer.nl()
              writer.comment("Class types")
              for (c <- theory.classes if Translate.cdeps(Prelude.unqualify(c.name)).nonEmpty) {
                if (verbose) progress.echo("  type for class " + c.name)
                Translate.class_type_decl(theory_name, c.name).foreach(writer.command(_, notations))
              }
            }
            
            // class instances
            writer.nl()
            writer.comment("Class predicate instances")
            for (a <- theory.arities) {
              val (bound_args: List[Syntax.BoundArg],_) = Translate.bound_type_arguments(a.prop.typargs)
              a.prop.term match {
                case OFCLASS(ty,c) =>
                  for (cname <- Translate.dep_representative(c) if Translate.new_instance (a.type_name, cname)) {
                    val cut_cname = cname.split("[.]", 2)
                    val uq_cname = if (cut_cname.length == 1) cut_cname(0) else cut_cname(1)
                    val name = Prelude.add_const_ident(s"${a.type_name}_${uq_cname}_pred_instance", theory_name)
                    val concl = Syntax.Appl(Syntax.Symb(Prelude.ref_class_pred_ident(cname)), Translate.typ(ty))
                    val full_type = bound_args.foldRight(concl)(Syntax.Prod.apply)
                    val cmd = Syntax.DefableDecl(name, full_type, inst = true)
                    writer.command(cmd, notations)
                  }
                case t => error("Inappropriate arity conclusion: " + t.toString)
              }
            }
            Translate.current_arities = theory.arities
            
            // write declarations related to undefined classes
            if (verbose) progress.echo("Undefined classes")
            writer.nl()
            writer.comment("Undefined classes")
            for (a <- theory.classes.sortWith(le)) {
              if (!(map_cst_dfn contains (a.name+"_class"))) {
                if (verbose) progress.echo("  "+a.toString+" "+a.serial)
                val cmd = Translate.class_decl(theory_name, a.name, None)
                writer.command(cmd,notations)
                if (with_class_types && Translate.cdeps(Prelude.unqualify(a.name)).nonEmpty) {
                  val other_cmd = Translate.class_type_definition(theory_name, a.name)
                  writer.command(other_cmd,notations)
                }
              }
            }
            // write declarations related to undefined constants
            writer.nl()
            writer.comment("Undefined constants")
            for (c <- theory.consts.sortWith(le)) {
              // skip constants corresponding to classes
              if (!c.name.endsWith("_class") && !map_cst_dfn.contains(c.name)) {
                if (verbose) progress.echo("  " + c.toString + " " + c.serial)
                val cst = c.the_content
                val rhs = c.name match {
                  case s"${cname}_class.$rest" =>
                    Translate.add_cst(cname, c.name)
                    val altname = c.name + "_alt"
                    val firstcmd = Translate.const_decl(theory_name, altname, cst.typargs, cst.typ, None, No_Syntax, ignore_classes = true)
                    writer.command(firstcmd,notations)
                    val t = Term.Const(altname,cst.typargs.map(TFree.apply))
                    /*if (with_class_types) {
                      val secondcmd = Translate.const_of_class_type_decl(theory_name, cname, c.name, cst.typargs, cst.typ, t)
                      writer.command(secondcmd,notations)
                    }*/
                    Some(t)
                  case _ =>
                    None
                }
                val cmd = Translate.const_decl(theory_name, c.name, cst.typargs, cst.typ, rhs, cst.syntax)
                writer.command(cmd, notations)
              }
            }
            // write declarations related to defined constants
            writer.nl()
            writer.comment("Defined constants")
            for (c <- theory.consts.sortWith(le)) {
              // skip constants corresponding to classes
              if (!c.name.endsWith("_class")) {
                map_cst_dfn.get(c.name) match {
                  case None =>
                  case Some(dfn) =>
                    if (verbose) progress.echo("  " + c.toString + " " + c.serial)
                    val cst = c.the_content
                    val cmd = Translate.const_decl(theory_name, c.name, cst.typargs, cst.typ, Some(dfn), cst.syntax)
                    writer.command(cmd, notations)
                    if (with_class_types) {
                      c.name match {
                        case s"${cname}_class.$rest" =>
                          val t = Term.Const(c.name, cst.typargs.map(TFree.apply))
                          val other_cmd = Translate.const_of_class_type_decl(theory_name, cname, c.name, cst.typargs, cst.typ, t)
                          writer.command(other_cmd,notations)
                        case _ =>
                      }
                    }
                }
              }
            }
            // write declarations related to defined classes
            if (verbose) progress.echo("Defined classes")
            writer.nl()
            writer.comment("Defined classes")
            for (a <- theory.classes.sortWith(le)) {
              map_cst_dfn.get(a.name+"_class") match {
                case Some(d) =>
                  if (verbose) progress.echo("  "+a.toString+" "+a.serial+" := "+d.toString)
                  val cmd = Translate.class_decl(theory_name, a.name, Some(d))
                  writer.command(cmd,notations)
                  if (with_class_types && Translate.cdeps(Prelude.unqualify(a.name)).nonEmpty) {
                    val other_cmd = Translate.class_type_definition(theory_name, a.name)
                    writer.command(other_cmd,notations)
                  }
                case None =>
              }
            }
            // write declarations related to non-definitional axioms
            writer.nl()
            writer.comment("Axioms")
            for (a <- theory.axioms.sortWith(le)) {
              if (!map_axm_eqtyp.contains(a.name)) {
                if (verbose) progress.echo("  " + a.toString + " " + a.serial)
                val cmd = Translate.stmt_decl(Prelude.add_axiom_ident(a.name, theory_name), a.the_content.prop, None, a.name)
                writer.command(cmd, notations)
              }
            }
            // write declarations related to definitional lemmas
            writer.nl()
            writer.comment("Definitional theorems")
            for (a <- theory.axioms.sortWith(le)) {
              map_axm_eqtyp.get(a.name) match {
                case None =>
                case Some(eqtys,lhs) =>
                  if (verbose) progress.echo("  "+a.toString+" "+a.serial)
                  val p = a.the_content.prop
                  val prf = Appt(PAxm("Pure.reflexive",eqtys),lhs)
                  //println("proof of "+a.name+": "+prf.toString)
                  val aname = Prelude.add_axiom_ident(a.name,theory_name)
                  val original_name = lhs match {
                    case Term.Const(name,_) =>
                      name
                    case _ => a.name
                  }
                  val cmd = Translate.stmt_decl(aname, a.the_content.prop, Some(prf), original_name)
                  writer.command(cmd,notations)
              }
            }

            /** count the proofs that are removed */
            var n_proofs_rm: Int = 0

            /** function writing a declaration related to a theorem
             *
             *  @param name the name of the theorem
             *  @param prop the proposition proved by the theorem
             *  @param proof the proof of the theorem */
            def decl_thm(name: String, prop: Prop, proof: Term.Proof): Unit = {
              if (verbose) progress.echo("  "+ name)
              val cmd = Translate.stmt_decl(Prelude.add_thm_ident(name,theory_name), prop, Some(proof), name)
              writer.command(cmd, notations)
              if (with_class_types) {
                val thm_ref: Term.Proof = PThm(0, theory_name, Thm_Name(name, 0), prop.typargs.map(TFree.apply))
                val pre_proof = prop.args.foldLeft(thm_ref) { case (prf, (v, ty)) => Appt(prf, Free(v, ty)) }

                /** Processes head hypotheses of the form <code>[[OFCLASS]](...)</code>
                 *  and returns sort constraints, the stripped theorem and its proof.
                 *
                 * @param t the proposition to inspect
                 * @return a triple <code>(m,rest,prf)</code> where
                 *         <code>m</code> maps type variable names to their sorts,
                 *         <code>rest</code> is <code><span style="color:#FFC0CB;">t</span></code> stripped of its head
                 *         class-assignment hypotheses, and
                 *         <code>prf</code> is a proof of <code>rest</code> assuming that type
                 *         variables have the class type associated with their sort in <code>m</code>
                 */
                @tailrec
                def get_sorts(t : Term.Term, map: Map[String,String] = Map(), prf: Term.Proof = pre_proof,
                              init_state: Boolean = true): Option[(Map[String,String], Term.Term, Term.Proof)] = t match {
                  case (App(App(Term.Const(Pure_Thy.IMP, _), OFCLASS(T @ TFree(tvar, _), cname)), concl))
                    if Translate.cdeps(Prelude.unqualify(cname)).nonEmpty =>
                    map.get(tvar) match {
                      case None =>
                        val uqcname = Prelude.unqualify(cname)
                        val new_proof = AppP(prf, PThm(0, theory_name, Thm_Name(uqcname + "_class_type_def", 0), List(T)))
                        get_sorts(concl, map + (tvar -> uqcname), new_proof, false)
                      case _ => None
                    }
                  case _ =>
                    if (init_state) None else Some(map, t, prf)
                }
                for ((sortmap, rest, prf) <- get_sorts(prop.term)) {
                  if (verbose) progress.echo(s"  ${name}_alt")
                   val other_cmd = Translate.stmt_of_class_type_decl(theory_name, name, sortmap, prop.copy(term = rest), prf)
                  writer.command(other_cmd, notations)
                }
              }
            }

            /** map proof serial -> replacement.
             * replacement is <code>Some(name)</code> if it is to be replaced by a theorem
             * and <code>None</code> if it is to be erased. */
            var replace_serial: Map[Long, Option[String]] = Map()
            
            /** In $isa, Some theorem proofs are a reference to an unnamed lemma proving the exact same
             * statement. This function recursively inspects the proof of a theorem to delete all such useless lemmas
             * by updating the replace_serial map
             *
             * @param name               the name of the theorem
             * @param proof              the proof of the theorem
             * @param encountered_lemmas all lemmas to replace by the theorem when they are called,
             *                           where the last encountered (at the top of the list, the first one
             *                           in the numbering order) will have its declaration replaced by the
             *                           theorem's one
             * @return true if no such lemma was found, indicating that the theorem should be stated on its own
             * @define isa  <span style="color:#FFFF00">Isabelle</span>
             * @define arg  code><span style="color:#FFC0CB;"
             * @define arge /span></code
             */
            @tailrec
            def remove_useless_proofs(name: String, proof: Term.Proof, args: List[String],
                                      encountered_lemmas: List[Long] = Nil): Boolean = get_call(proof,args) match {
              case Some(PThm(serial, origin_theory, thm_name, _)) if thm_name.is_empty &&
                origin_theory == theory_name && !Translate.replace_serial.contains(serial) =>
                n_proofs_rm += 1
                Translate.replace_serial += serial -> (name,Export_Theory.Kind.THM)
                // otherwise scala does not recognise tail recursiveness
                val (next_proof,next_args) = use_proof(theory_name, serial) {
                  case (prf, prop) => (prf, prop.args.map(_._1).reverse)
                }
                remove_useless_proofs(name, next_proof, next_args, serial :: encountered_lemmas)
              case _ =>
                encountered_lemmas match {
                  case final_lemma :: remainder =>
                    replace_serial += final_lemma -> Some(name)
                    if (verbose) progress.echo(s"$name went down to $final_lemma")
                    for (lemma <- remainder) replace_serial += lemma -> None
                    false
                  case _ => true
                }
            }

            /** function writing the declaration of a lemma for an intermediary proof */
            def write_proof(prf: Long): Unit = {
              replace_serial.get(prf) match {
                case Some(Some(thm_name)) =>
                  use_proof(theory_name,prf){
                    case (proof,prop) => decl_thm(thm_name,prop,proof)
                  }
                case Some(None) =>
                  if (verbose) progress.echo("  ignoring proof" + prf)
                case _ =>
                  if (verbose) progress.echo("  proof " + prf)
                  use_proof(theory_name,prf){
                    case (proof,prop) => get_call(proof,prop.args.map(_._1).reverse) match {
                      case Some(PThm(serial,_,thm_name,_)) =>
                        n_proofs_rm += 1
                        val new_mapping = {
                          if (!thm_name.is_empty) (thm_name.name,Export_Theory.Kind.THM)
                          else Translate.replace_serial.getOrElse(serial,(f"proof_$serial", ""))
                        }
                        Translate.replace_serial += prf -> new_mapping
                      case _ =>
                        val cmd = Translate.stmt_decl(Prelude.ref_proof_ident(prf),prop,Some(proof))
                        writer.command(cmd, notations)
                    }
                  }
              }
            }
            
            /** function writing all non-redundant proofs in prfs as intermediary lemmas,
             *  also declaring all theorems in thms once their [[max_serial]] has been reached
             *
             * @param prfs proofs to handle
             * @param thms remaining theorems
             */
            def write_proofs(prfs: List[Long], thms: List[Entity[Thm]]) : Unit =
              thms match {
                case thm :: thms =>
                  val theorem = thm.the_content
                  write_proofs_body(prfs,thms,max_serial(theorem.proof),thm.name,theorem.prop,theorem.proof)
                case _ => for (prf <- prfs) {write_proof(prf)}
              }

            @tailrec
            def write_proofs_body(prfs: List[Long], thms: List[Entity[Thm]],
                                  thm_prf: Long, thm_name: String, thm_prop: Prop,
                                  thm_proof: Term.Proof): Unit =
              prfs match {
                case prf::prfs2 =>
                  if (prf > thm_prf) {
                    // all proofs <= thm_prf have been handled already
                    decl_thm(thm_name,thm_prop,thm_proof)
                    thms match {
                      case thm :: thms =>
                        val theorem = thm.the_content
                        write_proofs_body(prfs,thms,max_serial(theorem.proof),thm.name,theorem.prop,theorem.proof)
                      case _ => for (prf <- prfs) {write_proof(prf)}
                    }
                  } else {
                    write_proof(prf)
                    write_proofs_body(prfs2,thms,thm_prf,thm_name,thm_prop,thm_proof)
                  }
                case _ =>
              }
            // write declarations related to theorems
            writer.nl()
            writer.comment("Theorems")
            /** all proofs in increasing order */
            val prfs = map_theory_proofs(theory_name).toList

            /** remove all useless lemmas and keep the theorems that did not replace a lemma */
            val thms = for ( thm <- theory.thms.sortWith(le) if remove_useless_proofs(thm.name,
                               thm.the_content.proof, thm.the_content.prop.args.map(_._1).reverse) )
              yield thm

            write_proofs(prfs,thms)
            progress.echo("End writing "+mod_name_theory+extension)

            // Print amount of unnecessary proofs
            val n_proofs_total = prfs.length + theory.thms.length
            val rm_percentage = ((10000*n_proofs_rm.toFloat)/n_proofs_total).round.toFloat/100
            progress.echo(n_proofs_rm.toString + " proofs removed in theory " + theory_name +
                          " out of " + n_proofs_total.toString + " (" + rm_percentage.toString +
                          "%)")
          }
          progress.echo("End reading theory "+theory_name)
        }
        mk.close()
        progress.echo("End writing "+mod_name_session+extension)
      }
      progress.echo("End translating session "+session)
    }
  }
}
