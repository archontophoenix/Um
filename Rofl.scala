package um

import annotation.tailrec
import Fresh._
import Sexps._
import Uh.{Atomic,Exp,CharLiteral,Num,StringLiteral,Sym,uhString,uhStr}
import Parsing.{CodePoint,Hope,Err}
import Valids._

// Rules Organized For Logic ///////////////////////////////////////////////////

/*
 *  `?            variable sigil (needed when not atom starting with lowercase)
 *  `.            constant sigil (needed when atom starting with lowercase)
 *  _             anonymous always-fresh variable
 *  |:            cons (works on numbers, character codes, text strings;
 *                where 1 = S |: 0, 'b' = S |: 'a', and "xyz" = 'x' |: "yz")
 *  ~|            conclusion/premise separator
 *  Always        true query
 *  Never         false query
 *  ,             query conjunction
 *  |,            query disjunction
 *  t0 !!!> t1    expand and refresh t0, then unify with t1
 *  scrutinee *>  ( pat1 | query1 ; ... ; patn | queryn )
 *                pattern match (first applicable pattern is chosen)
 * TODO: recursive queries on a different rulebase (rulebase |~ query) --
 *       how best to represent rulebases and queries as data?
 */

object Rofl extends RoflMachine(true)
case class RoflMachine (allowRecursiveTerms: Boolean) {

  // Options ///////////////////////////////////////////////////////////////////

  var trace: Boolean = false
  var traceAll: Boolean = false
  var askAfterCount: Long = 1024

  // Terms: s-expressions that may contain Rofl variables //////////////////////

  type Term = Sexp[RoflAtom,Any]
  sealed trait RoflAtom
  def str (t: Term): String = {
    def uhAtom (a: RoflAtom): Option[Atomic] = a match {
      case Const(ua) => Some(ua)
      case _ => None
    }
    uhString(t,uhAtom _)
  }
  trait Var extends RoflAtom
  case class BaseVar (name: String) extends Var {
    override def toString: String = name
  }
  case class FreshVar (freshness: Freshness, v: Var) extends Var {
    override def toString: String = s"$v@$freshness"
  }
  class Recursion private (val v: Var, val term: Term) extends RoflAtom {
    override def toString: String = s"<<$v. ${str(term)}>>"
  }
  object Recursion {
    def apply (v: Var, term: Term): Recursion = {
      val fr = fresh()
      new Recursion(freshenVar(v,fresh()),mapFresh(term,fr))
    }
    def unapply (r: Recursion): Option[(Var,Term)] = Some((r.v,r.term))
  }
  case class Const (const: Atomic) extends RoflAtom {
    override def toString: String = uhStr(Atom(const))
  }
  def mapVarsToVars (t: Term, f: Var => Var): Term =
    t.map(a => a match {
      case Recursion(v,term) => Recursion(f(v),mapVarsToVars(term,f))
      case v: Var => f(v)
      case _ => a
    })
  def mapVarsToTerms (
      t: Term, f: Var => Term, except: Set[Var] = Set.empty[Var]): Term =
    t.flatMap(a => a match {
      case Recursion(v,term) =>
        Atom(Recursion(v,mapVarsToTerms(t,f,except + v)))
      case v: Var if except.contains(v) =>
        Atom(v)
      case v: Var =>
        f(v)
      case _ =>
        Atom(a)
    })
  def freshenVar (v: Var, fr: Freshness): Var = v match {
    case FreshVar(_,v) => FreshVar(fr,v)
    case _ => FreshVar(fr,v)
  }
  def mapFresh (t: Term, fr: Freshness): Term =
    mapVarsToVars(t,freshenVar(_,fr))
  def termFreeVariables (term: Term): Set[Var] = term match {
    case Atom(v: Var) => Set(v)
    case Atom(Recursion(v,term)) => termFreeVariables(term) - v
    case h |: t => termFreeVariables(h) ++ termFreeVariables(t)
    case _ => Set.empty
  }

  // Handling of |: for numbers, characters, text strings //////////////////////

  val S = Atom(Const(Sym("S")))
  implicit class SpecialConsTerm (t: Term) {
    def |*: (hd: Term): Term = (hd,t) match {
      case (S,Atom(Const(Num(name,num)))) =>
        val n = num + 1
        Atom(Const(Num(n.toString,n)))
      case (S,Atom(Const(CharLiteral(CodePoint(code))))) =>
        Atom(Const(CharLiteral(code + 1)))
      case (Atom(Const(CharLiteral(CodePoint(h)))),
            Atom(Const(StringLiteral(str)))) =>
        Atom(Const(StringLiteral(new String(Array(h),0,1) ++ str)))
      case _ =>
        hd |: t
    }
  }
  object |*: {
    def unapply (t: Term): Option[(Term,Term)] = t match {
      case Atom(Const(Num(_,num))) if num > 0 =>
        val n = num - 1
        Some((S,Atom(Const(Num(n.toString,n)))))
      case Atom(Const(CharLiteral(CodePoint(code)))) if code > 0 =>
        Some((S,Atom(Const(CharLiteral(code - 1)))))
      case Atom(Const(StringLiteral(str))) if str.size > 0 =>
        Some((
          Atom(Const(CharLiteral(str.head))),
          Atom(Const(StringLiteral(str.tail)))))
      case h |: t =>
        Some((h,t))
      case _ =>
        None
    }
  }

  // Fails (failed operations) /////////////////////////////////////////////////

  trait Fail
  trait UnifyFail extends Fail with Unif {
    def flatMap (f: Frame => Unif) = this
  }
  case class CannotUnify (m0: Term, m1: Term) extends UnifyFail {
    override def toString: String = s"Can't unify ${str(m0)} and ${str(m1)}"
  }
  case class RecursiveUnify (v0: Var, m0: Term, m1: Term) extends UnifyFail {
    override def toString: String =
      s"Infinite term unifying $v0=${str(m0)} with ${str(m1)}"
  }
  object FalseFail extends Fail {
    override def toString: String = "Never query"
  }
  object MatchExhausted extends Fail {
    override def toString: String = "No match"
  }
  case class NotRefreshable (v: Var, t: Term) extends Fail {
    override def toString: String =
      s"Cannot refresh $v: already defined as ${str(t)}"
  }

  // Frames (substitutions) and expansions /////////////////////////////////////

  trait Unif {
    def flatMap (f: Frame => Unif): Unif
  }
  case class Frame (subst: Map[Var,Term]) extends Unif {
    def flatMap (f: Frame => Unif) = f(this)
    def unify (
          m0: Term, m1: Term,
          alreadyUnifying: Set[(Var,Term)] = Set.empty[(Var,Term)]):
        Unif = 
      if (m0 eq m1) // cheap optimization
        this
      else (m0,m1) match {
        case (varAtom @ Atom(v0: Var),_) =>
          if (m1 == varAtom)
            this
          else subst.get(v0) match {
            case Some(m0) =>
              val unifying = v0 -> m1
              if (alreadyUnifying.contains(unifying)) {
                if (allowRecursiveTerms) this
                else RecursiveUnify(v0,m0,m1)
              } else
                unify(m0,m1,alreadyUnifying + unifying)
            case None =>
              Frame(subst + (v0 -> m1))
          }
        case (_,Atom(_: Var)) =>
          unify(m1,m0,alreadyUnifying)
        case (Atom(Recursion(v,body)),_) => // TODO: test unif of 2 Recursions
          val av = Atom(v)
          unify(av,body,alreadyUnifying).flatMap(_.unify(av,m1,alreadyUnifying))
        case (_,Atom(_: Recursion)) =>
          unify(m1,m0,alreadyUnifying)
        case (h0 |*: t0,h1 |*: t1) =>
          unify(h0,h1,alreadyUnifying).flatMap(_.unify(t0,t1,alreadyUnifying))
        case _ =>
          if (m0 == m1) this else CannotUnify(m0,m1)
      }
    def expansion (v: Var): Term = expansion(Atom(v))
    def expansion (term: Term): Term = expansionAndVars(term,Set.empty)._1
    def expansionAndVars (t: Term, expanding: Set[Var]): (Term,Set[Var]) =
      t match {
        case varAtom @ Atom(v: Var) =>
          if (expanding.contains(v))
            (varAtom,Set(v))
          else subst.get(v) match {
            case None =>
              (varAtom,Set(v))
            case Some(t) =>
              val (x,vs) = expansionAndVars(t,expanding + v)
              val exp: Term =
                if (! vs.contains(v))
                  x
                else {
                  val newV = FreshVar(fresh(),v)
                  mapVarsToVars(
                    Atom(Recursion(v,x)),u => if (u == v) newV else u)
                }
              (exp,vs)
          }
        case h |*: t =>
          val (hx,hvs) = expansionAndVars(h,expanding)
          val (tx,tvs) = expansionAndVars(t,expanding)
          (hx |*: tx,hvs ++ tvs)
        case _ =>
          (t,Set.empty)
      }
    override def toString: String =
      if (subst.isEmpty) "<empty frame>"
      else subst.map { case (v,t) => s"$v = ${str(t)}" }.mkString("\n")
    def answerString (query: Query): String = {
      val vars = subst.keySet & query.variables
      if (vars.isEmpty) "Yes"
      else vars.map(v => s"$v = ${str(expansion(v))}").mkString("\n")
    }
  }
  val EmptyFrame = Frame(Map.empty)
 
  // Searches: Fails, Frames, and more Searches ////////////////////////////////

 class Search (
      val frame: Frame, val base: Rulebase, val query: Query, val depth: Int,
      val constructors: List[Constructor]) {
    import java.lang.ref.SoftReference
    private var getRef: SoftReference[(Seq[Fail],Seq[Frame],Seq[Search])] = null
    def get: (Seq[Fail],Seq[Frame],Seq[Search]) = {
      val cached = if (getRef == null) null else getRef.get
      if (cached != null)
        cached
      else {
        val result = query.get(this,frame)
        getRef = new SoftReference(result)
        result
      }
    }
    def and (right: Query): Search =
      new Search(frame,base,AndQuery(query,right),depth,constructors)
    override def toString: String = {
      val sep = "\n    ... from ...\n"
      val ctorStr =
        if (constructors.isEmpty)
          ""
        else if (constructors.size < 2)
          constructors.map(_.expanded(frame)).mkString(sep,sep,"")
        else
          constructors.take(2).map(_.expanded(frame)).mkString(sep,sep,"...")
      s"${query.mapTerm(frame.expansion _)} at depth $depth$ctorStr"
    }
 }
  object Search {
    def apply (
          parent: Search, frame: Frame, query: Query,
          ctor: Option[Constructor] = None):
        Search =
      new Search(
        frame,parent.base,query,parent.depth + 1,
        ctor match {
          case None => parent.constructors
          case Some(c) => c :: parent.constructors
        })
    def apply (base: Rulebase, query: Query): Search =
      new Search(EmptyFrame,base,query,0,Nil)
  }

  // Queries: starting points for searches, given frame, rulebase, and depth ///

  trait Query {
    def get (search: Search, frame: Frame): (Seq[Fail],Seq[Frame],Seq[Search])
    def variables: Set[Var]
    def mapVar (f: Var => Var): Query
    def mapTerm (f: Var => Term): Query
  }
  object TrueQuery extends Query {
    def get (search: Search, frame: Frame) = (Seq.empty,Seq(frame),Seq.empty)
    def variables = Set.empty
    def mapVar (f: Var => Var) = this
    def mapTerm (f: Var => Term) = this
    override def toString: String = "Always"
  }
  object FalseQuery extends Query {
    def get (search: Search, frame: Frame) =
      (Seq(FalseFail),Seq.empty,Seq.empty)
    def variables = Set.empty
    def mapVar (f: Var => Var) = this
    def mapTerm (f: Var => Term) = this
    override def toString: String = "Never"
  }
  case class TermQuery (ruleHeadMatcher: Term) extends Query {
    def get (search: Search, frame: Frame) = {
      val (fails,searches) =
        search.base.refreshVariables.rules.foldLeft(
            (Seq.empty[Fail],Seq.empty[Search])) {
          case ((fails,searches),r) =>
            def describeMatch =
              s"trying rule $r\n" +
                s"matching $this with\n" +
                s"${str(r.conclusion)} in\n$frame"
            if (traceAll)
              println(s">>> traceAll: $describeMatch")
            frame.unify(ruleHeadMatcher,r.conclusion) match {
              case fr: Frame =>
                if (trace || traceAll) {
                  print(s"<<< trace: success ")
                  if (traceAll)
                    println
                  else
                    println(describeMatch)
                  println(s"******** Result:\n$fr\n")
                }
                (fails,Search(search,fr,r.premise,Some(r)) +: searches)
              case fail: UnifyFail =>
                if (traceAll)
                  println(s"<<< traceAll:\n$fail\n")
                (fail +: fails,searches)
            }
        }
      (fails.reverse,Seq.empty,searches.reverse)
    }
    def variables = termFreeVariables(ruleHeadMatcher)
    def mapVar (f: Var => Var) = TermQuery(mapVarsToVars(ruleHeadMatcher,f))
    def mapTerm (f: Var => Term) = TermQuery(mapVarsToTerms(ruleHeadMatcher,f))
    override def toString: String = str(ruleHeadMatcher)
  }
  case class AndQuery (left: Query, right: Query) extends Query {
    def get (search: Search, frame: Frame) = {
      val (fails,frames,searches) = left.get(search,frame)
      (fails,Seq.empty,
        frames.map(Search(search,_,right)) ++ searches.map(_.and(right)))
    }
    def variables = left.variables ++ right.variables
    def mapVar (f: Var => Var) = AndQuery(left.mapVar(f),right.mapVar(f))
    def mapTerm (f: Var => Term) = AndQuery(left.mapTerm(f),right.mapTerm(f))
    override def toString: String = s"$left,\n  $right"
  }
  case class OrQuery (left: Query, right: Query) extends Query {
    def get (search: Search, frame: Frame) =
      (Seq.empty,Seq.empty,
        Seq(
          Search(search,frame,left,Some(DisjunctionLeft)),
          Search(search,frame,right,Some(DisjunctionRight))))
    def variables = left.variables ++ right.variables
    def mapVar (f: Var => Var) = OrQuery(left.mapVar(f),right.mapVar(f))
    def mapTerm (f: Var => Term) = OrQuery(left.mapTerm(f),right.mapTerm(f))
    override def toString: String = s"$left |,\n    $right)"
  }
  case class RefreshQuery (refreshee: Term, pat: Term) extends Query {
    def get (search: Search, frame: Frame) =
      frame.unify(mapFresh(frame.expansion(refreshee),fresh()),pat) match {
        case fr: Frame => (Seq.empty,Seq(fr),Seq.empty)
        case fail: UnifyFail => (Seq(fail),Seq.empty,Seq.empty)
      }
    def variables = termFreeVariables(refreshee) ++ termFreeVariables(pat)
    def mapVar (f: Var => Var) =
      RefreshQuery(mapVarsToVars(refreshee,f),mapVarsToVars(pat,f))
    def mapTerm (f: Var => Term) =
      RefreshQuery(mapVarsToTerms(refreshee,f),mapVarsToTerms(pat,f))
    override def toString: String = s"(${str(refreshee)}) !!!> ${str(pat)}"
  }
  case class MatchQuery (
      scrutinee: Term, cases: Seq[Rule]) extends Query {
    def get (search: Search, frame: Frame) =
      cases.headOption match {
        case None =>
          (Seq(MatchExhausted),Seq.empty,Seq.empty)
        case Some(rule @ Rule(pat,query)) =>
          frame.unify(scrutinee,pat) match {
            case fr: Frame =>
              (Seq.empty,Seq.empty,Seq(Search(search,fr,query,Some(rule))))
            case fail: UnifyFail =>
              (Seq(fail),Seq.empty,
                Seq(Search(search,frame,MatchQuery(scrutinee,cases.tail))))
          }
      }
    def variables =
      cases.foldLeft(Set.empty[Var]) { case(vs,Rule(pat,query)) =>
        vs ++ termFreeVariables(pat) ++ query.variables
      }
    def mapVar (f: Var => Var) =
      MatchQuery(
        mapVarsToVars(scrutinee,f),
        cases.map { case Rule(pat,query) =>
          Rule(mapVarsToVars(pat,f),query.mapVar(f))
        })
    def mapTerm (f: Var => Term) =
      MatchQuery(
        mapVarsToTerms(scrutinee,f),
        cases.map { case Rule(pat,query) =>
          Rule(mapVarsToTerms(pat,f),query.mapTerm(f))
        })
    override def toString: String =
      s"(${str(scrutinee)}) *> " +
        cases.map { case Rule(pat,query) => s"${str(pat)} | $query" }.
          mkString("{\n","\n","}")
  }

  // Rulebases (databases of rules) ////////////////////////////////////////////

  case class Rulebase (rules: Seq[Rule]) {
    def refreshVariables: Rulebase = {
      val fr = fresh()
      Rulebase(rules.map(_.freshen(fr)))
    }
    override def toString: String = rules.mkString("\n","\n","\n")
  }

  // Rules and Constructors ////////////////////////////////////////////////////

  trait Constructor { // used to construct a proof
    def name: String
    // TODO: count the number of slots?
    def expanded (fr: Frame): Constructor
  }
  case class Rule (conclusion: Term, premise: Query) extends Constructor {
    def name = toString // TODO: give rules names
    def expanded (fr: Frame) =
      Rule(fr.expansion(conclusion),premise.mapTerm(fr.expansion _))
    def freshen (fr: Freshness): Rule =
      Rule(mapFresh(conclusion,fr),premise.mapVar(freshenVar(_,fr)))
    def variables: Set[Var] = termFreeVariables(conclusion) ++ premise.variables
    override def toString: String = s"${str(conclusion)} ~|\n  $premise"
  }
  object DisjunctionLeft extends Constructor {
    def name = toString
    def expanded (fr: Frame) = this
    override def toString: String = "Left"
  }
  object DisjunctionRight extends Constructor {
    def name = toString
    def expanded (fr: Frame) = this
    override def toString: String = "Right"
  }

  // Rofl parsing (turning an Exp into a Rulebase) /////////////////////////////

  def expected (msg: String, x: Exp): Bad[Err] =
    Bad(Atom(s"expected $msg: $x").notesFrom(x))
  def parseRulebase (in: Exp): Hope[Rulebase] =
    parseRules(in).map(rs => Rulebase(rs))
  def parseRules (in: Exp): Hope[Seq[Rule]] = in match {
    case Empty() =>
      Good(Seq.empty)
    case Atom(Sym(";")) :|: rule :|: rules :|: Empty() =>
      Valid.map2(parseRule(rule),parseRules(rules))(_ +: _)
    case _ =>
      parseRule(in).map(Seq(_))
  }
  def parseRule (in: Exp): Hope[Rule] = in match {
    case Atom(Sym("~|")) :|: tl => tl match {
      case conclusion :|: premise :|: Empty() =>
        Valid.map2(parseTerm(conclusion),parseQuery(premise))(Rule(_,_))
      case x =>
        expected("rule (<conclusion> ~| <premise>)",x)
    }
    case _ => parseTerm(in).map(Rule(_,TrueQuery))
  }
  def parseTerm (in: Exp): Hope[Term] = in match {
    case Empty() =>
      Good(Empty())
    case Atom(Sym(s)) =>
      Good(Atom(s match {
        case "_" => FreshVar(fresh(),BaseVar("_"))
        case _ if s.length > 0 && s.head.isLower => BaseVar((s))
        case _ => Const(Sym(s))
      }))
    case Atom(a) =>
      Good(Atom(Const(a)))
    case h :|: t => h match {
      case Atom(Sym("`?")) => t match {
        case Atom(Sym(a)) :|: Empty() => Good(Atom(BaseVar(a)))
        case x => expected("single symbol after `?",x)
      }
      case Atom(Sym("`.")) => t match {
        case Atom(a) :|: Empty() => Good(Atom(Const(a)))
        case x => expected("single atom after `.",x)
      }
      case Atom(Sym("|:")) => t match {
        case hh :|: tt :|: Empty() =>
          Valid.map2(parseTerm(hh),parseTerm(tt))(_ |*: _)
        case x =>
          expected("cons (<head> |: <tail>)",x)            
      }
      case h => Valid.map2(parseTerm(h),parseTerm(t))(_ |*: _)
    }
  }
  def parseQuery (in: Exp): Hope[Query] = in match {
    case Atom(Sym("Always")) => Good(TrueQuery)
    case Atom(Sym("Never")) => Good(FalseQuery)
    case Atom(Sym(op)) :|: tl =>
// println(s"\nParsing op = $op; tl = $tl\n")
 op match {
      case "," => tl match {
        case left :|: right :|: Empty() =>
          Valid.map2(parseQuery(left),parseQuery(right))(AndQuery(_,_))
        case x =>
          expected("query conjunction (<leftQuery>, <rightQuery>)",x)
      }
      case "|," => tl match {
        case left :|: right :|: Empty() =>
          Valid.map2(parseQuery(left),parseQuery(right))(OrQuery(_,_))
        case x =>
          expected("query disjunction (<leftQuery> |, <rightQuery>)",x)
      }
      case "!!!>" => tl match {
        case term :|: pat :|: Empty () =>
          Valid.map2(parseTerm(term),parseTerm(pat))(RefreshQuery(_,_))
        case x =>
          expected("refresh query (<term> !!!> <variable>)",x)
      }
      case "*>" => tl match {
        case scrutinee :|: cases :|: Empty() =>
          Valid.map2(parseTerm(scrutinee),parseMatchCases(cases))(
            MatchQuery(_,_))
        case x =>
          expected(
            "match query (scrutinee *> (pat1 | query1 ; ... ; patN queryN))",x)
      }
      case _ =>
        parseTerm(in).map(TermQuery(_))
    }
    case _ => parseTerm(in).map(TermQuery(_))
  }
  def parseMatchCases (in: Exp): Hope[Seq[Rule]] = in match {
    case Empty() =>
      Good(Seq.empty)
    case Atom(Sym(";")) :|: matchCase :|: matchCases :|: Empty () =>
      Valid.map2(parseMatchCase(matchCase),parseMatchCases(matchCases))(_ +: _)
    case _ =>
      parseMatchCase(in).map(Seq(_))
  }
  def parseMatchCase (in: Exp): Hope[Rule] = in match {
    case Atom(Sym("|")) :|: pattern :|: query :|: Empty () =>
      Valid.map2(parseTerm(pattern),parseQuery(query))(Rule(_,_))
    case x =>
      expected("match case (pattern | query)",x)
  }

  // Input /////////////////////////////////////////////////////////////////////

  def load [A] (in: Seq[Char], sourceName: String, f: Exp => Hope[A]): Hope[A] =
    Uh.wholeProgram.matchWith(Parsing.LocChs.fromChars(in,sourceName)).
      flatMap(f)
  def loadRulebase (fileNames: List[String]): Valid[Seq[Rule],Err] =
    fileNames match {
      case Nil =>
        Good(Seq.empty)
      case hd :: tl =>
        val src = io.Source.fromFile(hd)
        val maybeRules = load(src.toSeq,hd,parseRules)
        src.close
        Valid.map2(maybeRules,loadRulebase(tl))(_ ++ _)
    }

  // Search visitors (handle Fails and Frames for a given Search) //////////////

  trait Visitor [Result] { // Result is type of cumulative result, if any
    def result: Result
    def visit (
      search: Search, knownDuplicate: Boolean): Either[Result,Visitor[Result]]
  }
  case class Stats (
      failCount: Long = 0, frameCount: Long = 0, searchCount: Long = 0,
      maxDepth: Int = 0) {
    override def toString: String =
      s"answers: $frameCount   failures: $failCount" +
        s"   nodes visited: $searchCount   max depth: $maxDepth"
  }
  case class StatsVisitor (result: Stats) extends Visitor[Stats] {
    def visit (
        search: Search, knownDuplicate: Boolean): Either[Stats,StatsVisitor] = {
      val (fails,frames,_) = search.get
      Right(
        StatsVisitor(
          Stats(
            result.failCount + fails.size,result.frameCount + frames.size,
            result.searchCount + 1,result.maxDepth max search.depth)))
    }
  }
  case class AllAnswersVisitor (originalQuery: Query, result: List[String])
      extends Visitor[List[String]] {
    def visit (
          search: Search, knownDuplicate: Boolean):
        Either[List[String],AllAnswersVisitor] =
      if (knownDuplicate)
        Right(this)
      else {
        val (_,frames,_) = search.get
        Right(
          AllAnswersVisitor(
            originalQuery,
            frames.toList.map(_.answerString(originalQuery)) ++ result))
      }
  }
  case class DualVisitor [A,B] (vA: Visitor[A], vB: Visitor[B])
      extends Visitor[(A,B)] {
    def result = (vA.result,vB.result)
    def visit (
          search: Search, knownDuplicate: Boolean):
        Either[(A,B),DualVisitor[A,B]] =
      vA.visit(search,knownDuplicate) match {
        case Left(a) => Left((a,vB.result))
        case Right(vA1) => vB.visit(search,knownDuplicate) match {
          case Left(b) => Left((vA1.result,b))
          case Right(vB1) => Right(DualVisitor(vA1,vB1))
        }
      }
  }

  // Callback visitor //////////////////////////////////////////////////////////

  trait Callback {
    def foundAnswer (frame: Frame): Boolean
    def noMoreAnswers: Unit
    def reachedOperationLimit (opCount: Long, opLimit: Long): Option[Long]
  }
  case class CallbackVisitor (callback: Callback, opCount: Long, opLimit: Long)
      extends Visitor[Unit] {
    def result = callback.noMoreAnswers
    def visit (
          search: Search, knownDuplicate: Boolean):
        Either[Unit,CallbackVisitor] = {
      val (fails,frames,_) = search.get
      def go (frames: Seq[Frame]): Boolean = frames.headOption match {
        case None => true
        case Some(fr) => callback.foundAnswer(fr) && go(frames.tail)
      }
      if (! knownDuplicate && ! go(frames))
        Left(())
      else {
        val newCount = opCount + fails.size + frames.size + 1
        if (newCount < opLimit)
          Right(CallbackVisitor(callback,newCount,opLimit))
        else
          callback.reachedOperationLimit(newCount,opLimit) match {
            case None =>
              Left(())
            case Some(newLim) =>
              if (newLim <= newCount) Left(())
              else Right(CallbackVisitor(callback,newCount,newLim))
          }
      }
    }
  }
  
  // Search strategies (organize subsquent Searches for a given Search) ////////

  trait Strategy [State] { // State guides search, and is returned when done
    def startState (root: Search): State
    def nextSearch (
      state: State, search: Search): Either[State,(State,Boolean,Search)]
    @tailrec final def next [VR] (
        state: State, search: Search, knownDuplicate: Boolean,
        visitor: Visitor[VR]): (State,VR) =
      visitor.visit(search,knownDuplicate) match {
        case Left(result) => (state,result)
        case Right(nextVisitor) => nextSearch(state,search) match {
          case Left(finalState) =>
            (finalState,nextVisitor.result)
          case Right((newState,nextKnownDup,nextSearch)) =>
            next(newState,nextSearch,nextKnownDup,nextVisitor)
        }
      }
    def run [VR] (root: Search, initialVisitor: Visitor[VR]): (State,VR) =
      next(startState(root),root,false,initialVisitor)
  }
  object DepthFirst extends Strategy[List[Search]] {
    def startState (root: Search) = Nil
    def nextSearch (state: List[Search], search: Search) = {
      val (_,_,searches) = search.get
      val newSearches = searches.toList ++ state
      newSearches match {
        case Nil => Left(Nil)
        case h :: t => Right((t,false,h))
      }
    }
  }
  case class IterativeDeepeningState (
      root: Search, targetDepth: Int,
      deferredSearchesAtOrBelowTargetDepth: List[Search],
      searchesBeyondTargetDepth: Option[Vector[Search]]) {
    def showSearches (name: String, searches: Seq[Search]): String =
      if (searches.isEmpty)
        s"========== no $name searches =========="
     else
        s"========== $name searches ==========\n" +
          searches.mkString("\n\n") +
          s"\n========== end $name searches =========="
    override def toString: String =
      s"targDepth: $targetDepth    $root\n" +
        showSearches("deferred",deferredSearchesAtOrBelowTargetDepth) + "\n\n" +
        searchesBeyondTargetDepth.map(showSearches("beyond-target",_)).
          getOrElse("!!!!!!!!!! beyond-target searches overflowed !!!!!!!!!!")
  }
  object IterativeDeepening extends Strategy[IterativeDeepeningState] {
    val maxSearchesBeyondTargetDepth = 16384
    def startState (root: Search) =
      IterativeDeepeningState(root,0,Nil,Some(Vector.empty))
    def nextSearch (state: IterativeDeepeningState, search: Search) = {
      import state._
      val (_,_,searches) = search.get
      val (searchesAtOrBelowTarget,searchesBeyondTarget) =
        searches.partition(_.depth <= targetDepth)
      val searchesNow =
        searchesAtOrBelowTarget.toList ++ deferredSearchesAtOrBelowTargetDepth
      val searchesLater = searchesBeyondTargetDepth.flatMap { ss =>
        val ss1 = searchesBeyondTarget.toVector
        if (ss.size + ss1.size > maxSearchesBeyondTargetDepth) None
        else Some(ss ++ ss1)
      }
      searchesNow match {
        case Nil => // no more searches at this depth -- more searches deeper?
          searchesLater match {
            case Some(ss) =>
              if (ss.isEmpty) // no deeper searches left; all done
                Left(state)
              else // we kept the searches at next depth, so do them
                Right((
                  IterativeDeepeningState(
                    root,ss.map(_.depth).max,ss.tail.toList,Some(Vector.empty)),
                  false,ss.head))
            case None => // we had too many searches at next depth; restart
              Right((
                IterativeDeepeningState(
                  root,targetDepth + 1,Nil,Some(Vector.empty)),
                true,root))
          }
        case h :: t => // searches at or below target; do h next, and defer t
          Right((
            IterativeDeepeningState(root,targetDepth,t,searchesLater),
            h.depth < targetDepth,h))
      }
    }
  }
  case class VerboseStrategy [S] (s: Strategy[S]) extends Strategy[S] {
    def startState (root: Search) = s.startState(root)
    def nextSearch (state: S, search: Search) = {
      println(s"\n\n$state\n\n$search\n")
      io.StdIn.readLine
      s.nextSearch(state,search)
// TODO: allow "q" (quit), "a" (all frames) like Interactive
    }
  }

  // Interactive strategy //////////////////////////////////////////////////////

  object Interactive extends Strategy[List[Search]] {
    def startState (root: Search) = Nil
    def nextSearch (state: List[Search], search: Search) = {
      println(
        "\n==================================================================" +
          s"\n\n$search\nin frame:\n${search.frame}\n")
      val (fails,frames,searches) = search.get
      def commandLoop: Either[List[Search],(List[Search],Boolean,Search)] = {
        print("\nCommand (? for help): ")
        io.StdIn.readLine match {
          case "q" =>
            Left(state)
          case "" =>
            state match {
              case Nil => Left(Nil)
              case h :: t => Right((t,false,h))
            }
          case "a" =>
            println(s"\nFull answer frames here:\n${frames.mkString("\n")}\n")
            commandLoop
          case s =>
            val chosenSearch: Option[Search] =
              try {
                val n = s.toInt
                if (0 <= n && n < searches.size) Some(searches(n)) else None
              } catch {
                case (x: NumberFormatException) => None
              }
            chosenSearch match {
              case None =>
                println("""
Commands:
q           quit
<newline>   pop back to previous search, or quit if none
a           show *full* answer frames at this search
n           where n is the number of a search from here: choose it
otherwise   show this help message
""")
                commandLoop
              case Some(nextSearch) =>
                Right((search :: state,false,nextSearch))
            }
        }
      }
      if (! fails.isEmpty)
        println(s"\nFailures here:\n${fails.mkString("\n")}\n")
      if (! frames.isEmpty) {
        val originalQuery = (search :: state).last.query
        println(
          s"\nAnswer frames here:\n" +
            s"${frames.map(_.answerString(originalQuery)).mkString("\n")}\n")
      }
      if (searches.isEmpty)
        println("\nNo searches from here.\n")
      else {
        println(s"\nSearches from here:\n")
        println(
          searches.zipWithIndex.map { case (srch,i) => s"# $i:\n$srch" }.
            mkString("\n\n"))
      }
      commandLoop
    }  
  }

  // REPL //////////////////////////////////////////////////////////////////////

  object CommandHandler {
    def commandHelp =
      println(s"""
Commands:
newline        Continue (with doubled limit, if operation limit reached)
:ask=<n>       Ask to continue after <n> operations (currently $askAfterCount)
:trace         Turn on tracing of successful unifications (currently $trace)
:traceall      Turn on tracing of attempted unifications (currently $traceAll)
:notrace       Turn off :trace
:notraceall    Turn off :traceall
""")
    def command (s: String): Unit =
      try {
        println
        if (s.startsWith(":ask=")) {
          askAfterCount = s.drop(5).toInt
          println(s"Will ask to continue at depths at or above $askAfterCount.")
        } else if (s == ":trace") {
          trace = true
          println("Tracing of successful unifications is now on.")
        } else if (s == ":notrace") {
          trace = false
          println("Tracing of successful unifications is now off.")
        } else if (s == ":traceall") {
          traceAll = true
          println("Tracing of all unification attempts is now on.")
        } else if (s == ":notraceall") {
          traceAll = false
          println("Tracing of all unification attempts is now off.")
        } else
          commandHelp
      } catch {
        case e: IllegalArgumentException =>
          println(e)
          commandHelp
      }
  }
  case class REPLCallback (originalQuery: Query) extends Callback {
    def foundAnswer (frame: Frame): Boolean = {
      println(s"\n${frame.answerString(originalQuery)}\n")
      print("Continue? (<enter> for yes, . to stop, :help for commands): ")
      io.StdIn.readLine match {
        case "." =>
          false
        case s if s.startsWith(":") =>
          CommandHandler.command(s)
          true
        case "" =>
          true
        case x =>
          println(s"Don't understand $x")
          foundAnswer(frame)
      }
    }
    def noMoreAnswers =
      println("\nNo more answers.\n")
    def reachedOperationLimit (opCount: Long, opLimit: Long): Option[Long] = {
      val proposedLimit =
        if (opCount < opLimit * 2) opLimit * 2 else opCount * 2
      println(s"Reached $opCount operations (limit $opLimit). ")
      print(
        s"<enter> to raise limit to $proposedLimit, . to stop, or new limit: ")
      io.StdIn.readLine match {
        case "" =>
          Some(proposedLimit)
        case "." =>
          None
        case s =>
          try
            Some(s.toLong)
          catch {
            case e: IllegalArgumentException =>
              println(e)
              reachedOperationLimit(opCount,opLimit)
          }
      }
    }
  }
  case class  REPL [State] (
      base: Rulebase, strategy: Strategy[State] = IterativeDeepening) {
    def queryLoop (): Unit = {
      println("\nQuery (or . to stop, or :help for commands):")
      io.StdIn.readLine match {
        case "." =>
          ()
        case s if s.startsWith(":") =>
          CommandHandler.command(s)
          queryLoop()
        case qStr => 
          load(qStr,"input",parseQuery) match {
            case Good(q) =>
              println(s"Answering query $q...")
              val (_,(_,stats)) =
                strategy.run(
                  Search(base,q),
                  DualVisitor(
                    CallbackVisitor(REPLCallback(q),0,askAfterCount),
                    StatsVisitor(Stats())))
              println(s"\n$stats\n")
            case bad @ Bad(_,_) =>
              println(s"\nInvalid query:${bad.toList.mkString("\n","\n","\n")}")
          }
          queryLoop()
      }
    }
  }

  // Main program //////////////////////////////////////////////////////////////

  def main (args: Array[String]): Unit =
    loadRulebase(args.toList) match {
      case Good(rules) =>
        println(s"Loaded: ${rules.mkString("\n","\n","\n")}")
        REPL(Rulebase(rules)).queryLoop()
      case bad @ Bad(_,_) =>
        println("Errors:")
        println(bad.toList.map(_.notedString).mkString("\n"))
    }

}
