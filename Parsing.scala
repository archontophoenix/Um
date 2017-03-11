package um

import language.implicitConversions
import Sexps._
import Valids._

// Ad-hoc parser combinators ///////////////////////////////////////////////////
// Trying to do too much parsing with simple-minded combinators does not seem //
// to lead to good error messages //////////////////////////////////////////////
// These combinators evaluate their arguments eagerly, so wrap recursion in a //
// function (such as the splitter argument to Parser) //////////////////////////

object Parsing {

  // 32-bit Unicode code points ////////////////////////////////////////////////

  case class CodePoint (code: Int) {
    override def toString: String = 
      if (code == '\t') "tab"
      else if (code == '\n') "newline"
      else if (32 <= code && code <= 126) s"'${code.toChar}'"
      else s"character with code $code (0x${code.toHexString})"
  }
  implicit def codePointToInt (ch: CodePoint): Int = ch.code
  implicit def intToCodePoint (ch: Int): CodePoint = CodePoint(ch)

  // Where input comes from (for error reporting, etc.) ////////////////////////

  case class Location (source: String, pos: Long, lineNum: Long, charNum: Int) {
    def next (ch: CodePoint): Location = {
      val (nextLineNum,nextCharNum) =
        if (ch.code == '\n') (lineNum + 1,0) else (lineNum,charNum + 1)
      Location(source,pos + 1,nextLineNum,nextCharNum)
    }
    def > (that: Location): Boolean = {
      val thatSource = that.source
      if (this.source != thatSource)
        sys.error(s"Cannot compare locations in $source and $thatSource")
      pos > that.pos
    }
    override def toString: String =
      if (pos <= 0) s"start of $source"
      else s"$source, line $lineNum, col $charNum (pos $pos)"
  }

  // Generic input sequence of items of type `I` that keeps track of Location //

  trait Input [+I] {
    def split: (Option[I],Input[I])
    def where: Location
    def isEmpty: Boolean = split._1 == None
    def nonEmptySplit: (I,Input[I]) = split match {
      case (None,_) => sys.error(s"Unexpected empty input at $where")
      case (Some(i),rest) => (i,rest)
    }
    def itemString: String = split match {
      case (None,_) => s"$where, at end of input"
      case (Some(item),_) => s"$item at $where"
    }
  }

  // Input of CodePoints ///////////////////////////////////////////////////////

  object LocChs {
    private case class Chs (in: Seq[CodePoint], where: Location)
        extends Input[CodePoint] {
      def split = in.headOption match {
        case None => (None,this)
        case some @ Some(ch) => (some,Chs(in.tail,where.next(ch)))
      }
    }
    def apply (in: Seq[CodePoint], source: String = "input"): Input[CodePoint] =
      Chs(in,Location(source,0,1,0))
    def fromChars (in: Seq[Char], source: String = "input"): Input[CodePoint] =
      apply(in.map(CodePoint(_)),source)
  }

  // Error and validation types ////////////////////////////////////////////////

  type Err = Sexp[String,Location]
  def err (in: Input[_], msg: String): Bad[Err] = Bad(Atom(msg).note(in.where))
  type Hope[+A] = Valid[A,Err]

  // Parser combinators proper /////////////////////////////////////////////////

  type Splitter[I,+O] = Input[I] => (Hope[O],Input[I])
  case class Parser [I,+O] (split: Splitter[I,O]) { thisParser =>
    def map [B] (f: O => B): Parser[I,B] = Parser(in => {
      val (result,rest) = thisParser.split(in)
      (result.map(f),rest)
    })
    def flatMap [B] (f: O => Parser[I,B]): Parser[I,B] = Parser(in =>
      thisParser.split(in) match {
        case (Good(a),next) => f(a).split(next)
        case (Bad(b,bs),rest) => (Bad(b,bs),rest)
      })
    def hopeMap [B] (f: O => Hope[B]): Parser[I,B] = Parser(in =>
      thisParser.split(in) match {
        case (Good(a),next) => f(a) match {
          case success @ Good(_) => (success,next)
          case fail @ Bad(_,_) => (fail,in)
        }
        case (fail @ Bad(_,_),_) => (fail,in)
      })
    def expecting (what: String): Parser[I,O] = Parser(in =>
      thisParser.split(in) match {
        case success @ (Good(_),_) =>
          success
        case (bad @ Bad(_,_),rest) =>
          (err(in,s"expecting $what"),rest)
      })
    def matchWith (in: Input[I]): Hope[O] = {
      val (result,rest) = split(in)
      if (rest.isEmpty) result
      else result ++ err(rest,s"leftover text starting with ${rest.itemString}")
    }
    def * [B] (thatParser: => Parser[I,B]): Parser[I,(O,B)] =
      Parser.map2(thisParser,thatParser)((_,_))
    def & [OO >: O] (thatParser: => Parser[I,List[OO]]): Parser[I,List[OO]] =
      Parser.map2(thisParser,thatParser)(_ :: _)
    def :- [B] (thatParser: => Parser[I,B]): Parser[I,O] =
      Parser.map2(thisParser,thatParser)((a,b) => a)
    def -: [B] (thatParser: Parser[I,B]):  Parser[I,O] =
      Parser.map2(thatParser,thisParser)((b,a) => a)
    def interspersedWith [B] (thatParser: => Parser[I,B]):
        Parser[I,(O,List[(B,O)])] =
      thisParser * zeroOrMore1(thatParser * thisParser)
    def separatedBy (p: => Parser[I,_]): Parser[I,List[O]] =
      zeroOrOne(thisParser & zeroOrMore1(p -: thisParser))
    def testForError (test: O => Option[String], e: String): Parser[I,O] =
      Parser(in => thisParser.split(in) match {
        case good @ (Good(a),rest) => test(a) match {
          case None => good
          case Some(s) => (err(in,s),in)
        }
        case bad => bad
      })
    def suchThat (test: O => Boolean, e: String): Parser[I,O] =
      testForError(a => if (test(a)) None else Some(s"$a: not $e"),e)
  }
  object Parser {
    def validate [I,A] (v: Hope[A]) = Parser((in: Input[I]) => (v,in))
    def point [I,A] (a: A): Parser[I,A] = validate(Good(a))
    def endOfInput [I,A] (a: A): Parser[I,A] = Parser(in => in.split match {
      case (None,rest) => (Good(a),rest)
      case (Some(_),rest) => (err(in,"Not at end of input"),rest)
    })
    def next [I]: Parser[I,I] = Parser(in => in.split match {
      case (None,rest) => (err(in,"Empty input"),rest)
      case (Some(i),rest) => (Good(i),rest)
    })
    def map2 [I,A,B,C] (pa: Parser[I,A], pb: => Parser[I,B]) (
        f: (A,B) => C): Parser[I,C] =
      Parser(in => pa.split(in) match {
        case (aResult @ Good(_),next) =>
          val (bResult,rest) = pb.split(next)
          (Valid.map2(aResult,bResult)(f),rest)
        case (Bad(b,bs),next) =>
          (Bad(b,bs),next)
      })
    def app [I,A,B] (pf: Parser[I,A => B]) (pa: => Parser[I,A]): Parser[I,B] =
      map2(pf,pa)(_(_))
    def fail [I] (
          msg: String = "Failure", where: Option[Location] = None):
        Parser[I,Nothing] = Parser(in => {
      (Bad(Atom(msg).note(where.getOrElse(in.where))),in)
    })
  }
  implicit class ListParser [I,+A] (thisParser: Parser[I,List[A]]) {
    def +: [AA >: A] (thatParser: => Parser[I,AA]): Parser[I,List[AA]] =
      thatParser & thisParser
    def ++ [AA >: A] (thatParser: => Parser[I,List[AA]]): Parser[I,List[AA]] =
      Parser.map2(thisParser,thatParser)(_ ++ _)
  }
  def zilch [I]: Parser[I,Unit] = Parser.point(())
  def nada [I]: Parser[I,List[Nothing]] = Parser.point(Nil)
  def list [I,A] (p: Parser[I,A]): Parser[I,List[A]] = p.map(List(_))
  def maybe [I,A] (p: Parser[I,A]): Parser[I,A] = Parser((in: Input[I]) =>
    p.split(in) match {  // reset failure position so not committed
      case success @ (Good(_),_) => success
      case (fail @ Bad(_,_),_) => (fail,in)
    })
  def zeroOrOne1 [I,A] (p: Parser[I,A]): Parser[I,List[A]] = zeroOrOne(list(p))
  def zeroOrOne [I,A] (p: Parser[I,List[A]]): Parser[I,List[A]] =
    oneOf(maybe(p),nada)
  def zeroOrMore1 [I,A] (p: Parser[I,A]): Parser[I,List[A]] =
    zeroOrMore(list(p))
  def zeroOrMore [I,A] (p: Parser[I,List[A]]): Parser[I,List[A]] = {
    def accSplit (acc: List[A]) (in: Input[I]): (Hope[List[A]],Input[I]) =
      p.split(in) match {
        case (Good(as),next) => accSplit(acc ++ as)(next)
        case _ => (Good(acc),in)
      }
    Parser(accSplit(Nil))
  }
  def oneOrMore1 [I,A] (p: Parser[I,A]): Parser[I,List[A]] = p & zeroOrMore1(p)
  def oneOrMore [I,A] (p: Parser[I,List[A]]): Parser[I,List[A]] =
    p ++ zeroOrMore(p)
  /** Commits to the first alternative that consumes any characters, so
    * if any two alternatives have a common prefix, you should either
    * factor out the prefix or write a custom `Parser`.
    * Call `expecting` on the resulting parser if you want a sensible error
    * message.
    */
  def oneOf [I,A] (ps: Parser[I,A]*): Parser[I,A] = {
    def oneOfRemaining (qs: Seq[Parser[I,A]]): Parser[I,A] = Parser(in =>
      qs.headOption match {
        case None => (err(in,"No match"),in)
        case Some(q) => q.split(in) match {
          case success @ (Good(_),_) =>
            success
          case (fail1 @ Bad(_,_),next1) =>
            if (next1.where > in.where) (fail1,next1) // committed
            else oneOfRemaining(qs.tail).split(in)
        }
      })
    oneOfRemaining(ps)
  }
  def oneOfMaybe [I,A] (ps: Parser[I,A]*): Parser[I,A] =
    oneOf(ps.map(maybe(_)): _*)

  // Parsers for CodePoints ////////////////////////////////////////////////////

  implicit class ChParser [+A] (thisParser: Parser[CodePoint,A]) {
    /** Variant of `matchWith` for debugging from the REPL. */
    def |+| (s: String): Unit = {
      val (result,rest) = thisParser.split(LocChs.fromChars(s))
      println
      println(result)
      if (! rest.isEmpty)
        println(s"\n**** leftover text starting with ${rest.itemString} ****\n")
    }
  }
  type Ch = (CodePoint,Location)
  type ParseChs = Parser[CodePoint,List[Ch]]
  def charThat (matches: CodePoint => Boolean, e: String): ParseChs =
    Parser(in => in.split match {
      case (None,_) =>
        (err(in,s"expecting $e"),in)
      case (Some(ch),tail) =>
        if (matches(ch)) (Good(List((ch,in.where))),tail)
        else (err(in,s"not $e: ${CodePoint(ch)}"),in)
    })
  def char (ch: CodePoint): ParseChs = charThat(_ == ch,CodePoint(ch).toString)

}
