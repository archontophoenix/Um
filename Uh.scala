package um
import Alts._
import Parsing._
import Sexps._
import Valids._

// Uncomplicated parser for Humans /////////////////////////////////////////////

object Uh {

  // S-expression atom types ///////////////////////////////////////////////////

  trait Atomic
  trait SymLike extends Atomic {
    def name: String
    override def toString: String = name
  }
  case class Sym (name: String) extends SymLike
  case class Num (name: String, num: BigInt) extends SymLike {
    override def equals (that: Any) = that match {
      case Num(_,n) => n == num
      case _ => false
    }
    override def hashCode = 243 * num.hashCode
  }
  case class CharLiteral (char: CodePoint) extends Atomic {
    override def toString: String = char.toString
  }
  case class StringLiteral (string: String) extends Atomic {
    override def toString: String = "\"" + string + "\""
  }
  def atom (a: Atomic, loc: Location): Exp = Atom(a).note(loc)
  def atom (a: Atomic, t: Token): Exp = atom(a,t.where)
  def sym (t: Token) = atom(Sym(t.text),t)

  // Parser and parse result types /////////////////////////////////////////////

  /** A successful result is an s-expression with `Atomic` atoms, annotated with
   * `Location`s. */
  type Exp = Sexp[Atomic,Location]

  // Classification of character codes /////////////////////////////////////////

  val alphaCharTypes: Set[Byte] = { import Character._
    Set(
      UPPERCASE_LETTER,LOWERCASE_LETTER,TITLECASE_LETTER,MODIFIER_LETTER,
      OTHER_LETTER,COMBINING_SPACING_MARK,MODIFIER_SYMBOL,NON_SPACING_MARK)
  }
  val punctCharTypes: Set[Byte] = { import Character._
    Set(
      CURRENCY_SYMBOL,DASH_PUNCTUATION,MATH_SYMBOL,OTHER_PUNCTUATION,
      OTHER_SYMBOL)
  }
  val openDelimCharTypes: Set[Byte] = { import Character._
    Set(START_PUNCTUATION,INITIAL_QUOTE_PUNCTUATION)
  }
  val closeDelimCharTypes: Set[Byte] = { import Character._
    Set(END_PUNCTUATION,FINAL_QUOTE_PUNCTUATION)
  }
  def charType (ch: CodePoint): Byte = Character.getType(ch.code).toByte
  def isLinefeed (ch: CodePoint) = ch.code == '\n'
  def isWhite (ch: CodePoint) = Character.isWhitespace(ch.code)
  def isFlatWhite (ch: CodePoint) = isWhite(ch) && ! isLinefeed(ch)
  def isCaret (ch: CodePoint) = ch.code == '^'
  def isBackquote (ch: CodePoint) = ch.code == '`'
  def isAlpha (ch: CodePoint) =
    ! isCaret(ch) && ! isBackquote(ch) &&
      alphaCharTypes.contains(charType(ch))
  def isDigit (ch: CodePoint) = Character.isDigit(ch.code)
  def isDigitInRadix (radix: Int) (ch: CodePoint) =
    Character.digit(ch.code,radix) >= 0
  def isAlphaNum (ch: CodePoint) = isAlpha(ch) || isDigit(ch)
  def isHexDigit (ch: CodePoint) = isDigitInRadix(16)(ch)
  def isConnector (ch: CodePoint) =
    charType(ch) == Character.CONNECTOR_PUNCTUATION
  def isOpenBracket (ch: CodePoint) = ch.code == '['
  def isCloseBracket (ch: CodePoint) = ch.code == ']'
  def isAsciiSingleQuote (ch: CodePoint) = ch.code == '\''
  def isAsciiDoubleQuote (ch: CodePoint) = ch.code == '\"'
  def isAsciiQuote (ch: CodePoint) =
    isAsciiSingleQuote(ch) || isAsciiDoubleQuote(ch)
  def isBackslash (ch: CodePoint) = ch.code == '\\'
  def isNotBackslashOrNewline (ch: CodePoint) =
    ! isBackslash(ch) && ! isLinefeed(ch)
  def isOpenDelim (ch: CodePoint) = openDelimCharTypes.contains(charType(ch))
  def isCloseDelim (ch: CodePoint) = closeDelimCharTypes.contains(charType(ch))
  def isPunctuation (ch: CodePoint) =
    isCaret(ch) || (punctCharTypes.contains(charType(ch)) & ! isAsciiQuote(ch))
  def isOperatorStart (ch: CodePoint) = isBackquote(ch) || isPunctuation(ch)
  def isSemicolon (ch: CodePoint) = ch.code == ';'

  // Operator syntax (unary and binary) ////////////////////////////////////////

  /** Infix operator precedences, by starting character, where defined. */
  val infixPrecedences: Map[CodePoint,Int] =
      Seq(
        ";",
        "~",
        "|",
        "$",
        "\\",
        ",",
        ":",
        "?",
        "&",
        "!",
        "<=>",
        "#",
        "+-",
        "*/%",
        "^",
        "`", // precedence of operators made infix by leading backquote
        "@",
        ".").
      zipWithIndex.flatMap { case (s,i) => s.map(ch => CodePoint(ch) -> i) }.
      toMap
  val minBinaryPrecedence = 0
  val maxBinaryPrecedence = infixPrecedences.values.max
  /** Infix symbols ending in these characters are right-associative. */
  val infixRightAssocEndings: Set[CodePoint] =
    ";~|\\,:?&!^".map(ch => CodePoint(ch)).toSet

  // Parsing basic tokens (lists of CodePoint) /////////////////////////////////

  val alphaNum = charThat(isAlphaNum,"alphanumeric")
  val hexDigit = charThat(isHexDigit,"hexadecimal digit")
  val singleQuote = charThat(isAsciiSingleQuote,"single quote")
  val doubleQuote = charThat(isAsciiDoubleQuote,"double quote")
  val laterAlphaNum = // support single quote in its meaning of "prime"
    charThat(
      ch => isAlphaNum(ch) || isAsciiSingleQuote(ch),
      "continuation of alphanumeric symbol")
  val backslash = charThat(isBackslash,"backslash")
  val ordinaryInCharLiteral =
    charThat(
      isNotBackslashOrNewline,"any character except backslash or newline")
  val ordinaryInStringLiteral =
    charThat(
      ch => isNotBackslashOrNewline(ch) && ! isAsciiDoubleQuote(ch),
      "ordinary character in string literal (not backslash, newline, or quote)")
  val connect = charThat(isConnector,"connector")
  val punct = charThat(isPunctuation,"punctuation")
  val precPunct =
    charThat(
      ch => isPunctuation(ch) && infixPrecedences.contains(ch),
      "punctuation character with assigned precedence")
  val noPrecPunct =
    charThat(
      ch => isPunctuation(ch) && ! infixPrecedences.contains(ch),
      "punctuation character without assigned precedence")
  val newline = charThat(isLinefeed,"newline")
  val backquote = charThat(isBackquote,"backquote")
  val white = oneOrMore(charThat(isWhite,"whitespace"))
  val flatWhite = oneOrMore(charThat(isFlatWhite,"non-newline whitespace"))
  val openDelim = charThat(isOpenDelim,"opening delimiter")
  val closeDelim = charThat(isCloseDelim,"closing delimiter")
  val openBracket = charThat(isOpenBracket,"open bracket")
  val closeBracket = charThat(isCloseBracket,"close bracket")

  // Parsing integers //////////////////////////////////////////////////////////

  def integer (radix: Int): Parser[CodePoint,(BigInt,Location)] =
    oneOrMore(charThat(isDigitInRadix(radix),s"radix $radix digit")).map {
      chs =>
        (chs.foldLeft(BigInt(0)) {
            case (n,(codePoint,_)) =>
              n * radix + Character.digit(codePoint.code,radix)
          },
          chs.head._2)
    }

  // Parsing character escape sequences starting with backslash ////////////////
  // Basically the same as Haskell character escapes ///////////////////////////
  // except for \^@ through \^_ ////////////////////////////////////////////////

  def escapeMap (escapeSeq: String, ch: CodePoint) =
    escapeSeq.map(char(_)).reduce(_ ++ _).map { chs => List((ch,chs.head._2)) }
  val eatWhitespaceThroughBackslash = (white ++ backslash).map(_ => Nil)
  val emptyAmpersand = char('&').map(_ => Nil)
  val controlCodes =
    oneOf(
      Seq(
          "NUL","SOH","STX","ETX","EOT","ENQ","ACK","BEL","BS","HT","LF","VT",
          "FF","CR","SO","SI","DLE","DC1","DC2","DC3","DC4","NAK","SYN","ETB",
          "CAN","EM","SUB","ESC","FS","GS","RS","US","SP").zipWithIndex.map {
        case (s,i) => maybe(escapeMap(s,i))
      }: _*).
      expecting("control code abbreviation")
  val numericEscapes =
    oneOf(integer(10),char('o') -: integer(8),char('x') -: integer(16)).
      suchThat(_._1 <= Character.MAX_CODE_POINT,"valid Unicode code point").
      map { case (bigInt,loc) => List((CodePoint(bigInt.intValue),loc)) }.
      expecting("legal Unicode numeric character code")
  val charEscape =
    oneOf(
        numericEscapes,
        escapeMap("0",0),
        escapeMap("a",7),
        escapeMap("b",8),
        escapeMap("f",12),
        escapeMap("n",10),
        escapeMap("r",13),
        escapeMap("t",9),
        escapeMap("v",11),
        escapeMap("\"",'\"'),
        escapeMap("\'",'\''),
        escapeMap("\\",'\\'),
        emptyAmpersand,
        eatWhitespaceThroughBackslash,
        controlCodes,escapeMap("DEL",127)).
      expecting("character escape")
  val escapedChar =
    (backslash -: charEscape).expecting("backslash-escaped character code")

  // Parsing character and string literals as lists of CodePoint ///////////////
  
  val charLiteral =
    (singleQuote ++ oneOf(escapedChar,ordinaryInCharLiteral) ++ singleQuote).
      suchThat(_.size == 3,"a single non-empty character or character escape").
      expecting("character literal in single quotes")
  val stringLiteral =
    (doubleQuote ++ zeroOrMore(oneOf(escapedChar,ordinaryInStringLiteral)) ++
        doubleQuote).
      expecting("string literal in double quotes")

  // Parsing whitespace and comments starting with double semicolon ////////////

  val toEolComment =
    (char(';') ++ char(';') ++
        zeroOrOne(
          flatWhite ++ zeroOrMore(charThat(_.code != '\n',"non-newline"))) ++
            newline).
      expecting("to-end-of-line comment")
  val separator =
    oneOrMore(oneOf(toEolComment,white)).expecting("whitespace or comment")

  // Parsing unary and binary operators as lists of CodePoint //////////////////

  lazy val symCont: ParseChs =
    (connect ++ oneOf(oneOrMore(laterAlphaNum),oneOrMore(punct),nada) ++
        zeroOrMore(symCont)).
      expecting("symbol continuation starting with underscore")
  val identSym =
    oneOf(alphaNum ++ zeroOrMore(laterAlphaNum) ++ zeroOrOne(symCont),symCont).
      expecting("alphanumeric identifier")
  val leftUnSym =
    oneOf(identSym,charLiteral,stringLiteral).
      expecting("alphanumeric identifier or char or string literal")
  val rightUnSym =
    (backquote ++ zeroOrMore(punct) ++ zeroOrOne(symCont)).
      expecting(
        "backquote, " +
          "or right-associative prefix operator starting with backquote")
  val binSym =
    (oneOrMore(punct) ++ zeroOrOne(symCont)).
      expecting("infix binary operator symbol")

  // Tokens and token types ////////////////////////////////////////////////////

  trait TokenType
  object WhiteWithoutNewlineToken extends TokenType
  object WhiteWithNewlineToken extends TokenType
  object OpenDelimToken extends TokenType
  object CloseDelimToken extends TokenType
  object IdentifierToken extends TokenType
  object CharLiteralToken extends TokenType
  object StringLiteralToken extends TokenType
  object RightUnaryToken extends TokenType
  object BackquoteToken extends TokenType
  object BinaryToken extends TokenType
  trait Token {
    def text: String
    def where: Location
    def tokenType: TokenType
    def number: Hope[BigInt] = {
      val (radix,digits) =
        if (text.startsWith("0o") || text.startsWith("0O"))
          (8,text.drop(2))
        else if (text.startsWith("0x") || text.startsWith("0X"))
          (16,text.drop(2))
        else
          (10,text)
      integer(radix).matchWith(LocChs.fromChars(digits)).map(_._1)
    }
  }
  case class TextToken (text: String, where: Location) extends Token {
    lazy val tokenType = text.headOption match {
      case None =>
        WhiteWithoutNewlineToken
      case Some(h) =>
        def startsWithComment =
          text.size >= 3 && text.startsWith(";;") && isWhite(text(2))
        if (isWhite(h) || startsWithComment) {
          if (text.contains('\n')) WhiteWithNewlineToken
          else WhiteWithoutNewlineToken
        } else if (isOpenDelim(h))
          OpenDelimToken
        else if (isCloseDelim(h))
          CloseDelimToken
        else if (isAlphaNum(h) || isConnector(h))
          IdentifierToken
        else if (isAsciiSingleQuote(h))
          CharLiteralToken
        else if (isAsciiDoubleQuote(h))
          StringLiteralToken
        else if (isBackquote(h)) {
          if (text.size == 1) BackquoteToken else RightUnaryToken
        } else if (isPunctuation(h))
          BinaryToken
        else
          sys.error(s"Not a token: $text")
      }
    override def toString: String = "\"" + text + "\" at " + where
  }
  case class StartOfInputToken (where: Location) extends Token {
    def text = ""
    def tokenType = OpenDelimToken
    override def toString: String = where.toString
  }
  case class EndOfInputToken (where: Location) extends Token {
    def text = ""
    def tokenType = CloseDelimToken
    override def toString: String = s"end of input at $where"
  }

  // Transforming characters into tokens (first compilation pass) //////////////

  type Chs = Input[CodePoint]
  def chListToString (chs: List[Ch]): String =
    new String(chs.map(_._1.code).toArray,0,chs.size)
  val token: Parser[CodePoint,Token] = {
    def chsToToken (chs: List[Ch]): Token =
      if (chs.isEmpty) sys.error("Empty token!")
      else TextToken(chListToString(chs),chs.head._2)
    oneOf(separator,openDelim,closeDelim,leftUnSym,rightUnSym,binSym).
      map { chs: List[Ch] => chsToToken(chs) }
  }
  def tokens (in: Chs): (Hope[Input[Token]],EndOfInputToken) = {
    def go (
        in: Chs, revAcc: Hope[Seq[Token]]): (Hope[Seq[Token]],EndOfInputToken) =
      if (in.isEmpty) {
        val end = EndOfInputToken(in.where)
        (revAcc.map { ts => (end +: ts).reverse },end)
      } else {
        val (t,rest) = token.split(in)
        go(rest,Valid.map2(t,revAcc)(_ +: _))
      }
    val (hopeTs,e) = go(in,Good(Seq(StartOfInputToken(in.where))))
    (hopeTs.map { ts =>
      case class TokenInput (in: Seq[Token]) extends Input[Token] {
        // in will always contain at least EndOfInputToken
        def split = {
          val tl = in.tail
          (Some(in.head),if (tl.isEmpty) this else TokenInput(tl))
        }
        def where = in.head.where
      }
      TokenInput(ts)
    },
      e)
  }

  // Validation and general error handling /////////////////////////////////////

  def err (where: Location, msg: String): Bad[Err] = Bad(Atom(msg).note(where))

  // Token parsing /////////////////////////////////////////////////////////////

  type TokenParser = Parser[Token,Exp]
  def tkn (test: Token => Boolean, e: String): Parser[Token,Token] =
    Parser.next.suchThat(test,e)
  def tknType (tType: TokenType, e: String): Parser[Token,Token] =
    tkn(_.tokenType == tType,e)
  def tknText (text: String, e: String): Parser[Token,Token] =
    tkn(_.text == text,e)
  def atom (p: Parser[Token,Token]): TokenParser = p.map(sym _)
  // for debugging: testing token parsers
  def tt [A] (p: Parser[Token,A], tkns: String*) = {
    case class TokensInput (in: Seq[String], pos: Int = 0)
        extends Input[Token] {
      def split =
        if (in.isEmpty) (Some(EndOfInputToken(where)),this) 
        else (Some(TextToken(in.head,where)),TokensInput(in.tail,pos + 1))
      def where = Location("input",pos,1,pos)
    }
    val (result,rest) = p.split(TokensInput(tkns))
    println
    println(result)
    rest.split match {
      case (None,_) =>
        sys.error("token stream should never be empty")
      case (Some(EndOfInputToken(_)),_) =>
        ;
      case (Some(_),_) =>
        println(
          s"\n**** leftover tokens starting with ${rest.itemString} ****\n")
    }
    result
  }

  // Simple expressions (identifiers, and, recursively, delimited expressions) /

  val simple: TokenParser = Parser(in => in.split match {
    case (Some(t),rest) => t.tokenType match {
      case IdentifierToken =>
        t.number match {
          case Good(n) =>
            (Good(atom(Num(t.text,n),t)),rest)
          case Bad(_,_) =>
            val (next,after) = rest.nonEmptySplit
            if (next.text != "[")       // just an identifer...
              (Good(sym(t)),rest)
            else                        // ... or a compound delimiter?
              compoundDelimiter(t,next,t.text + "[",Nil).split(after)
        }
      case CharLiteralToken =>
        (Good(atom(CharLiteral(CodePoint(Character.codePointAt(t.text,1))),t)),
          rest)
      case StringLiteralToken =>
        (Good(atom(StringLiteral(t.text.drop(1).dropRight(1)),t)),rest)
      case OpenDelimToken =>
        delimited(t).split(rest)
      case _ =>
        (err(
            t.where,
            s"Expecting identifier, literal, or open delimiter: ${t.text}"),
          rest)
    }
    case _ => sys.error("simple should never see empty input")
  })

  // Parsing modes (between different delimiters, or with/without whitespace) //

  case class Mode (
    separator: Parser[Token,_], leftUnarySeparator: Parser[Token,_],
    primitive: TokenParser,  override val toString: String)
  val tightSpacingMode = Mode(zilch,zilch,simple,"tightly spaced")
  lazy val tightBinary = binary(tightSpacingMode)
  val nonNewlineWhite =
    tknType(WhiteWithoutNewlineToken,"newline-free whitespace")
  val newlineWhite =
    tknType(WhiteWithNewlineToken,"whitespace with newline(s)")
  val anyWhite = oneOf(nonNewlineWhite,newlineWhite).expecting("whitespace")
  lazy val looseSpacingMode =
    Mode(anyWhite,anyWhite,tightBinary,"loosely spaced")
  lazy val inferSemicolonMode =
    Mode(
      anyWhite,nonNewlineWhite,tightBinary,
      "loosely spaced (inferring semicolons)")

  // Right-associative unary prefix expressions ////////////////////////////////

  def rightUnTkn = tknType(RightUnaryToken,"right-associative unary oeprator")
  def rightUnary (mode: Mode): TokenParser =
    oneOf(
      maybe(
        ((rightUnTkn :- mode.separator) * rightUnary(mode)).map {
          case (rightUnaryOperator,operand) =>
            Liss(sym(rightUnaryOperator),operand)
          }),
      mode.primitive)

  // Left-associative unary prefix expressions /////////////////////////////////

  def leftUnary (mode: Mode): TokenParser = {
    def simple = rightUnary(mode)
    (simple * zeroOrMore1(mode.leftUnarySeparator -: simple)).map {
      case (e,es) => if (es.isEmpty) e else Liss(e :: es: _*)
    }.expecting(s"$mode left-associatve unary expression")
  }

  // Keeping track of the structure of binary operations ///////////////////////

  trait Bin { // common prefix of binary operators (BinOp) and operands (BinArg)
    def exp: Exp // underlying Exp
  }
  case class BinOp (exp: Exp, precedenceOverride: Option[Int] = None)
      extends Bin {
    def associativityAndPrecedence: (BinAssoc,Option[Int]) =
      precedenceOverride match {
        case Some(prec) => (LeftBin,precedenceOverride)
        case None => exp match {
          case Atom(s: SymLike) if s.name.size > 0 =>
            val nm = s.name
            val (head,last) = (nm.codePointAt(0),nm.codePointBefore(nm.size))
            (if (infixRightAssocEndings.contains(last)) RightBin else LeftBin,
              infixPrecedences.get(head))
          case _ =>
            sys.error(
              s"non-symbol BinOp: no precedence ovveride: ${exp.notedString}")
        }
      }
  }
  case class BinArg (exp: Exp) extends Bin
  type FullBin = OdAlt[BinArg,BinOp]
  type OpHeadBin = EvAlt[BinOp,BinArg]
  abstract class BinAssoc (val what: String) {
    def apply (bins: FullBin): Exp = bins match {
      case BinArg(arg) *: EvNil =>
        arg
      case BinArg(arg0) *: BinOp(op1,_) *: BinArg(arg1) *: tl =>
        makeLiss(arg0,op1,arg1,tl)
    }
    def makeLiss (arg0: Exp, op1: Exp, arg1: Exp, tail: OpHeadBin): Exp
  }
  object RightBin extends BinAssoc("right-associative") {
    def makeLiss (arg0: Exp, op1: Exp, arg1: Exp, tail: OpHeadBin) =
      Liss(
        op1,arg0,tail match {
          case EvNil => arg1
          case BinOp(op,_) *: BinArg(arg) *: tl => makeLiss(arg1,op,arg,tl)
        })
  }
  object LeftBin extends BinAssoc("left-associative") {
    def makeLiss (arg0: Exp, op1: Exp, arg1: Exp, tail: OpHeadBin) = {
      val e = Liss(op1,arg0,arg1)
      tail match {
        case EvNil => e
        case BinOp(op,_) *: BinArg(arg) *: tl => makeLiss(e,op,arg,tl)
      }
    }
  }

  // Binary operands and operators, quoted and otherwise ///////////////////////

  def binArg (mode: Mode): Parser[Token,BinArg] = leftUnary(mode).map(BinArg(_))
  def sepBinArg (mode: Mode): Parser[Token,BinArg] =
    mode.separator -: binArg(mode)
  lazy val binOp: Parser[Token,BinOp] =
    oneOf(
      tknText("`","backquote") -: backquotedBinOp,
      atom(tknType(BinaryToken,"binary operator")).map(BinOp(_)))
  lazy val backquotedBinOp: Parser[Token,BinOp] =
    Parser(
      simple.split.andThen {
        case (Good(exp),rest) =>
          (exp match {
            case Atom(_: SymLike) | _: Liss[Atomic,_] =>
              Good(BinOp(exp,Some(infixPrecedences('`'))))
            case a @ Atom(StringLiteral(s)) =>
              Good(BinOp(Atom(Sym(s)).notesFrom(a),Some(infixPrecedences('`'))))
            case _ =>
              val where = exp.notes.headOption.getOrElse(rest.where)
              err(where,s"cannot turn into a symbol with backquote: $exp")
          },rest)
        case (Bad(b,bs),rest) =>
          (Bad(b,bs),rest)
      })
  def sepBinOp (mode: Mode): Parser[Token,BinOp] =
    zeroOrOne1(mode.separator) -: binOp

  // Parsing abbreviated expressions -- (arg op), (op arg), (op) ///////////////

  val flipOp = Atom(Sym("`^"))
  val abbreviatedExpr: TokenParser = {
    def argThenOp (mode: Mode) =
      (binArg(mode) * sepBinOp(mode)).map {
        case (arg,op) => Liss(op.exp,arg.exp)
      }
    def opThenArg (mode: Mode) =
      (binOp * sepBinArg(mode)).map {
        case (op,arg) => Liss(Liss(flipOp,op.exp),arg.exp)
        case x => sys.error(s"abbreviatedExpr: malformed: $x")
      }
    oneOfMaybe(
        argThenOp(looseSpacingMode),
        argThenOp(tightSpacingMode),
        opThenArg(looseSpacingMode),
        opThenArg(tightSpacingMode),
        binOp.map(_.exp),
        rightUnTkn.map(sym(_))).
      expecting("abbreviated expression")
  }

  // Parsing full binary expressions ///////////////////////////////////////////

  def binary (mode: Mode): TokenParser =
    (binArg(mode) * zeroOrMore1(sepBinOp(mode) * sepBinArg(mode))).hopeMap {
      case (arg0,Nil) =>
        Good(arg0.exp)
      case (arg0,(op0,arg1) :: tl) =>
        fullBinaryExpr(arg0 *: EvNil,op0,arg1 *: evAlt(tl))
    }
  /**
   * `reversedBefore` is an alternating sequence of operands and operators,
   * starting and ending with an operand. If it contains any operators, either
   * they have no precedence and are all the same operator, or they are
   * ordered by descending precedence, and all operators with the same
   * precedence have the same associativity. `reversedBefore` is in reverse
   * order with respect to the input.
   *
   * `op` is the current operator to examine. It came just after
   * `reversedBefore` in the input.
   *
   * `after` is an alternating sequence of operands and operators, starting
   * and ending with an operand. It is whatever followed `op` in the input.
   *
   * If `reversedBefore` contains no operators, keep going.
   *
   * Otherwise, if `op` has no precedence, then check that it is the same as
   * the operators in `reversedBefore`; keep going.
   *
   * Otherwise, while `reversedBefore`'s last operator has higher precedence
   * than `op`'s, collapse the trailing portion of `reversedBefore` with
   * that higher precedence into a single operand and recurse.
   *
   * Otherwise, if `reversedBefore`'s last operator has lower precedence than
   * `op`, keep going.
   *
   * Otherwise, `reversedBefore`'s last operator must have the same precedence
   * as `op`; check that it has the same associativity; keep going.
   *
   * &ldquo;To keep going&rdquo; means: Push `op` and the head of `after`
   * onto `reversedBefore`. If the rest of `after` is empty, collapse all of
   * `reversedBefore` into a single expression (return which); otherwise,
   * recurse with the first operator in `after` as the new `op`.
   */
  def fullBinaryExpr (
      reversedBefore: FullBin, op: BinOp, after: FullBin): Hope[Exp] = {
    def lastOp (bins: FullBin): Option[BinOp] = bins match {
      case BinArg(_) *: EvNil => None
      case BinArg(_) *: (op @ BinOp(_,_)) *: _ => Some(op)
    }
    def partitionByPrecedence (
          bins: FullBin, pr: Int, acc: OpHeadBin = EvNil):
        (FullBin,OpHeadBin) =
      // first return value is prefix of bins whose operators have precedence pr
      // second is the rest of bins (starting with a BinOp, not a BinArg)
      // first return value is in reverse order with respect to bins
      bins match {
        case arg0 *: op *: tl if op.associativityAndPrecedence._2.get == pr =>
          partitionByPrecedence(tl,pr,op *: arg0 *: acc)
        case arg0 *: tl =>
          (arg0 *: acc,tl)
      }
    def collapseGreaterPrecedence (bins: FullBin, minPrecedence: Int): FullBin =
      lastOp(bins) match {
        case None => bins
        case Some(op) => op.associativityAndPrecedence match {
          case (direction,None) =>  // no-precedence expression: collapse it all
            BinArg(direction(bins.reverse)) *: EvNil
          case (direction,Some(pr)) =>
            if (pr <= minPrecedence) // all ops in bins have lower precedence
              bins                   //  so we're done
            else {                   // collapse highest precedence in bins...
              val (exprToCollapse,rest) = partitionByPrecedence(bins,pr)
              collapseGreaterPrecedence(  // ... and try again
                BinArg(direction(exprToCollapse)) *: rest,minPrecedence)
            }
        }
      }
    def keepGoing: Hope[Exp] = {
      val (aftHd @ BinArg(_)) *: aftTl = after
      val newRevBefore = aftHd *: op *: reversedBefore
      if (aftTl.isEmpty) {
        val BinArg(wholeExp) *: EvNil =
          collapseGreaterPrecedence(newRevBefore,minBinaryPrecedence - 1)
        Good(wholeExp)
      } else {
        val (newOp @ BinOp(_,_)) *: newAfter = aftTl
        fullBinaryExpr(newRevBefore,newOp,newAfter)
      }
    }
    def oops (where: BinOp, msg: String) = {
      val bad = Bad(Atom(msg).notesFrom(where.exp))
      after match {
        case arg *: EvNil => bad
        case arg *: op *: tl => bad +++ fullBinaryExpr(arg *: EvNil,op,tl)
      }
    }
    def mixedNoPrec (noPrecOp: BinOp, otherOp: BinOp) =
      oops(
        otherOp,
        s"Can't use a different operator $otherOp in an " +
           "expression with a no-precedence binary operator " +
            s"($noPrecOp from ${noPrecOp.exp.noteString})")
    (lastOp(reversedBefore),op.associativityAndPrecedence) match {
      case (None,_) =>                // reversedBefore is just a single operand
        keepGoing                     //  so keepGoing will collapse and return
      case (Some(prev),(_,None)) =>   // op has no precedence
        if (prev == op) keepGoing
        else mixedNoPrec(op,prev)
      case (Some(prev),(curDirection,Some(curPrec))) =>
        prev.associativityAndPrecedence match {
          case (_,None) =>            // op has precedence, prev none
            mixedNoPrec(prev,op)
          case (prevDirection,Some(prevPrec)) =>
            if (prevPrec > curPrec)   // prev has higher precedence than op
              fullBinaryExpr(
                collapseGreaterPrecedence(reversedBefore,curPrec),op,after)
            else if (prevPrec < curPrec)  // prev has lower precedence
              keepGoing
            else if (prevDirection != curDirection)  // same precedence
              oops(
                op,
                "Binary operators of the same precedence with mixed " +
                  "associativities: " +
                  s"${prev.exp} (${prevDirection.what}) and " +
                  s"${op.exp} (${curDirection.what})")
            else                      // same precedence and direction
              keepGoing
        }
    }
  }

  // Delimited token sequences /////////////////////////////////////////////////

// TODO: allow choice of operator to infer between { and }.
// Prefix { with operator.
//   { ... }   is synonym for   ;{ ... }
// but could allow, e.g.,
//   +{ ... }   to add a bunch of complicated things
//   ::{ ... }   to make a list of complicated things
// etc.
//   id{ ... }   infers `id
// operator can be binary or id
  def delimited (open: Token): TokenParser = {
    val (contentParsers,what,closerText): (Seq[TokenParser],String,String) =
      open.text match {
        case "" =>
          (inferSemicolons,"expressions separated by newlines or semicolons","")
        case "{" =>
          (inferSemicolons,
            "expressions separated by newlines or semicolons","}")
        case "(" =>
          (parenthesized,"expression or abbreviated expression",")")
        case "[" =>
          (spaceSeparatedList,"whitespace-separated expressions","]")
        case _ =>
          (Seq(Parser.fail(s"Undefined open delimiter: $open")),"","")
      }
    val optWhite = zeroOrOne1(anyWhite)
    val closer =
      tknType(CloseDelimToken,closerText).
        suchThat(_.text == closerText,s"closer matching $open")
    val restOfDelimParsers =
      contentParsers.map(p => optWhite -: p :- optWhite :- closer)
    oneOf(
      oneOfMaybe(restOfDelimParsers: _*),
      Parser.fail("Expected $what after $open"))
  }

  // Expressions, inferring semicolons at newline //////////////////////////////

  val semicolonOp = BinOp(Atom(Sym(";")))
  val inferSemicolons: Seq[TokenParser] =
    Seq(
      binary(inferSemicolonMode).separatedBy(newlineWhite).map { _ match {
        case Nil =>
          Empty()
        case hd :: tl =>
          RightBin(
            BinArg(hd) *:
              evAlt(
                Stream.continually(semicolonOp).zip(tl.map(BinArg(_))).toList))
      }})

  // Expressions, not inferring semicolons /////////////////////////////////////

  val parenthesized: Seq[TokenParser] =
    Seq(
      binary(looseSpacingMode),
      abbreviatedExpr,
      zilch.map(_ => Empty()))

  // Whitespace-separated lists ////////////////////////////////////////////////

  val spaceSeparatedList: Seq[TokenParser] =
    Seq(binary(tightSpacingMode).separatedBy(anyWhite).map(listToLiss _))

  // Compound delimiters: id[...]id[...] ... [...]id ///////////////////////////

// TODO: extend to allow binOpOrID[...]binOpOrID[ ... ] ...
// TODO: also allow binOpOrID[...][...] ... [...] (i.e., optional intervening)
  def compoundDelimiter (
      firstOpener: Token, latestOpenBracket: Token, delimiterText: String,
      accumContents: List[Exp]): TokenParser = Parser(in =>
    delimited(latestOpenBracket).split(in) match {
      case (Good(exp),rest) =>
        def args = (exp :: accumContents).reverse
        def fun (s: String) = atom(Sym(s),firstOpener)
        val (t0,after0) = rest.nonEmptySplit
        val dText = delimiterText + "]"
        if (t0.tokenType != IdentifierToken)
          (Good(Liss((fun(dText) :: args): _*)),rest)
        else {
          val (t1,after1) = after0.nonEmptySplit
          if (t1.text != "[")
            (Good(Liss((fun(dText + t0.text) :: args): _*)),after0)
          else
            compoundDelimiter(
                firstOpener,t1,dText + t0.text + "[",exp :: accumContents).
              split(after1)
        }
      case failure =>
        failure
    })

  // Parsing a whole program (treated as if between curly braces) //////////////

  val programFromTokens: TokenParser =
    tknText("","start of input").flatMap(opener => delimited(opener))
  val wholeProgram: Parser[CodePoint,Exp] = Parser(in => {
    val (hopeTs,end) = tokens(in)
    val aftermath = new Input[CodePoint] {
      def split = (None,this)
      def where = end.where
    }
    tokens(in) match {
      case (Good(ts),_) => programFromTokens.split(ts) match {
        case (Good(prog),after) => after.split match {
          case (Some(EndOfInputToken(_)),_) =>
            (Good(prog),aftermath)
          case (Some(uhOh),_) =>
            (err(uhOh.where,s"Unexpected trailing $uhOh"),aftermath)
          case _ =>
            sys.error("wholeProgram: empty input")
        }
        case (fail @ Bad(_,_),_) => (fail,aftermath)
      }
      case (fail @ Bad(_,_),_) => (fail,aftermath)
    }
  })

  // Conversion of Exp to string, recognizing Uh expression syntax /////////////

  def uhStringPrecedenceLeftAssoc [A] (
        sexp: Sexp[A,_], uhAtom: A => Option[Atomic]):
      (String,Option[(Int,Boolean)]) = {
    object UhAtom {
      def unapply (a: A): Option[Atomic] = uhAtom(a)
    }
    def valid (s: String, p: ParseChs): Boolean =
      p.matchWith(LocChs.fromChars(s)) match {
        case Good(_) => true
        case Bad(_,_) => false
      }
    def validId (s: String) = valid(s,identSym)
    def validRightUn (s: String) = valid(s,rightUnSym)
    def validBin (s: String) = valid(s,binSym)
    def maybeParen (sexp: Sexp[A,_], prec: Int, assoc: Boolean): String =
      uhStringPrecedenceLeftAssoc(sexp,uhAtom) match {
        case (s,Some((p,a))) =>
          if ((p < prec || (p == prec && a != assoc))
              && ! (s.startsWith("(") || s.startsWith("[")))
            s"($s)"
          else
            s
        case (s,None) =>
          s
      }
    def lissString (liss: Liss[A,_]): String =
      liss.mapElems((e: Sexp[A,_]) => maybeParen(e,Integer.MAX_VALUE,true)).
        mkString("["," ","]")
    def compoundHead: Parser[CodePoint,List[List[Ch]]] =
      zeroOrOne(oneOf(identSym,binSym)).separatedBy(openBracket * closeBracket)
    def compound (op: String, args: Liss[A,_]): Option[String] =
      compoundHead.matchWith(LocChs.fromChars(op)) match {
        case Bad(_,_) =>
          None
        case Good(components) =>
          def go (
                components: List[List[Ch]], args: Liss[A,_], acc: String):
              Option[String] =
            (components,args) match {
              case (cpt :: Nil,Empty()) =>
                Some(acc ++ chListToString(cpt))
              case (cpt :: cpts,(arg: Liss[A,_]) :|: args) =>
                go(cpts,args,acc ++ chListToString(cpt) ++ lissString(arg))
              case _ =>
                None
            }
          if (components.size < 2) None else go(components,args,"")
      }
    sexp match {
      case Empty () =>
        ("()",None)
      case Atom(UhAtom(Sym(s))) =>
        (if (validId(s)) s
            else if (validRightUn(s) || validBin(s)) s"($s)"
            else "(`\"" ++ s ++ "\")",
          None)
      case Atom(a) =>
        (a.toString,None)
      case Atom(UhAtom(Sym(s))) :|: arg :|: Empty() if validRightUn(s) =>
        val (pr,assoc) = (maxBinaryPrecedence + 2,false)
        (s"$s ${maybeParen(arg,pr,assoc)}",Some((pr,assoc)))
      case Atom(UhAtom(Sym(s))) :|: arg0 :|: arg1 :|: Empty() if validBin(s) =>
        val assoc = ! infixRightAssocEndings.contains(s.last)
        val (inPrL,inPrR,outPr) =
          infixPrecedences.get(CodePoint(s.codePointAt(0))) match {
            case Some(p) => if (assoc) (p,p + 1,p) else (p + 1,p,p)
            case None => (Integer.MAX_VALUE,Integer.MAX_VALUE,Integer.MIN_VALUE)
          }
        (s"${maybeParen(arg0,inPrL,assoc)} $s ${maybeParen(arg1,inPrR,assoc)}",
          Some((outPr,assoc)))
      case liss @ (Atom(UhAtom(Sym(s))) :|: arg0 :|: args) if validId(s) =>
        val (pr,assoc) = (maxBinaryPrecedence + 1,true)
        (liss.mapElems((e: Sexp[A,_]) => maybeParen(e,pr + 1,assoc)).
            mkString(" "),
          Some((pr,assoc)))
      case liss @ (Atom(UhAtom(Sym(s))) :|: tail) => compound(s,tail) match {
        case Some(rslt) => (rslt,None)
        case None => (lissString(liss),None)
      }
      case liss: Liss[A,_] =>
        (lissString(liss),None)
      case hd |: tl =>
        val (pr,assoc) = (infixPrecedences('|'),false)
        (s"${maybeParen(hd,pr,assoc)} |: ${maybeParen(tl,pr,assoc)}",
          Some(pr,assoc))
    }
  }
  def uhString [A] (sexp: Sexp[A,_], uhAtom: A => Option[Atomic]): String =
    uhStringPrecedenceLeftAssoc(sexp,uhAtom)._1
  def uhStr (sexp: Exp): String = uhString(sexp,(a: Atomic) => Some(a))

  // Testing ///////////////////////////////////////////////////////////////////

  def testParse (s: String): Either[String,Exp] =
    wholeProgram.matchWith(LocChs.fromChars(s)) match {
      case Good(res) =>
        Right(res)
      case bad: Bad[_] =>
        Left(s"\n${bad.toList.map(_.notedString).mkString("\n")}\n")
    }
  def test (s: String, e: Exp): Boolean =
    testParse(s) match {
      case Right(res) =>
        res == e || {
          println(s"Expected ${uhStr(e)} from '$s', but got ${uhStr(res)}")
          false
        }
      case Left(errMsg) =>
        println(s"Parsing $s, got:\n$errMsg")
        false
    }
  def testShouldFail (s: String): Boolean =
    testParse(s) match {
      case Right(res) =>
        println(s"'$s' should not have parsed, but it did: ${uhStr(res)}")
        false
      case Left(_) =>
        true
    }
  def main (args: Array[String]): Unit = args.headOption match {
    case Some("test") =>
      runTests
    case Some("try") =>
      tryItOut
    case _ =>
      println("""
Usage: Uh [test|try]
test:  run tests
try:   try parsing expressions interactively
""")
  }
  def runTests: Unit = {
    def atm (s: String) = Atom(Sym(s))
    def lis (ss: String*) = Liss(ss.map(s => atm(s)): _*)
    println
    val tests =
      List(
        test("",Empty()),
        test("a",atm("a")),
        test("()",Empty()),
        test("{}",Empty()),
        test("[]",Empty()),
        test("{a}",atm("a")),
        test("(a)",atm("a")),
        test("[a]",Liss(atm("a"))),
        test("{ a }",atm("a")),
        test("( a )",atm("a")),
        test("[ a ]",lis("a")),
        test("`-a",lis("`-","a")),
        test("`- a",lis("`-","a")),
        test("`-`+a",Liss(atm("`-"),lis("`+","a"))),
        test("`- `+ a",Liss(atm("`-"),lis("`+","a"))),
        test("`- `+a",Liss(atm("`-"),lis("`+","a"))),
        testShouldFail("`-`+ a"),
        test("{a\nb}",lis(";","a","b")),
        test("{\na\nb\n}",lis(";","a","b")),
        test("a b",lis("a","b")),
        test("a\nb",lis(";","a","b")),
        test("\na\nb\n",lis(";","a","b")),
        test(" a b ",lis("a","b")),
        test("a b c",lis("a","b","c")),
        test("a `-b c",Liss(atm("a"),lis("`-","b"),atm("c"))),
        test("a `- b c",Liss(atm("a"),lis("`-","b"),atm("c"))),
        test(
          "a `+ `- b c",
          Liss(atm("a"),Liss(atm("`+"),lis("`-","b")),atm("c"))),
        test("a (b c) d",Liss(atm("a"),lis("b","c"),atm("d"))),
        test("a * b",lis("*","a","b")),
        test("a * b + c",Liss(atm("+"),lis("*","a","b"),atm("c"))),
        test("a + b * c",Liss(atm("+"),atm("a"),lis("*","b","c"))),
        test("a * b+c",Liss(atm("*"),atm("a"),lis("+","b","c"))),
        test("a+b * c",Liss(atm("*"),lis("+","a","b"),atm("c"))),
        test("(\na\nb\n)",lis("a","b")),
        test("(+)",atm("+")),
        test("a (+) b",lis("a","+","b")),
        test("(`-)",atm("`-")),
        test("a (`-) b",lis("a","`-","b")),
        test("a `and b",lis("and","a","b")),
        test("a `and b + c",Liss(atm("+"),lis("and","a","b"),atm("c"))),
        test("a `\"and\" b",lis("and","a","b")),
        test("(a+)",lis("+","a")),
        test("(a +)",lis("+","a")),
        test("(+a)",Liss(lis("`^","+"),atm("a"))),
        test("(+ a)",Liss(lis("`^","+"),atm("a"))),
        test("((a))",atm("a")),
        test("(`\"a b\")",atm("a b")),
        test("(`\"\")",atm("")),
        testShouldFail("`a"),
        test("(())",Empty()),
        test("[()]",Liss(Empty())),
        test("[[[]]]",Liss(Liss(Empty()))),
        test(
          "(a b (c d (e f) g) h)i",
          Liss(
            Liss(
              atm("a"),atm("b"),Liss(atm("c"),atm("d"),lis("e","f"),atm("g")),
              atm("h")),
            atm("i"))),
        test(
          "[a b] c [d e (f g h)]",
          Liss(lis("a","b"),atm("c"),Liss(atm("d"),atm("e"),lis("f","g","h")))),
        test("a b(c)",Liss(atm("a"),lis("b","c"))),
        test("a(b) c",Liss(lis("a","b"),atm("c"))),
        test(
          "[[[a b] c] d] e",
          Liss(Liss(Liss(lis("a","b"),atm("c")),atm("d")),atm("e"))),
        test(
          "a e{b\nc}d",Liss(atm("a"),Liss(atm("e"),lis(";","b","c"),atm("d")))),
        test(
          "[a (b {c d} e) f]",
          Liss(atm("a"),Liss(atm("b"),lis("c","d"),atm("e")),atm("f"))),
        test("a+b+c",Liss(atm("+"),lis("+","a","b"),atm("c"))),
        test("a+:b+:c",Liss(atm("+:"),atm("a"),lis("+:","b","c"))),
        test("a + b+c",Liss(atm("+"),atm("a"),lis("+","b","c"))),
        test("a+:b +: c",Liss(atm("+:"),lis("+:","a","b"),atm("c"))),
        testShouldFail("a +: b + c"),
        test("a+b * c-d",Liss(atm("*"),lis("+","a","b"),lis("-","c","d"))),
        testShouldFail("("),
        testShouldFail("}"),
        testShouldFail("(a + +)"),
        testShouldFail("(+ a +)"),
        testShouldFail("(+ + a)"),
        testShouldFail("+"),
        testShouldFail("a+"),
        testShouldFail("+a"),
        testShouldFail("\"a"),
        testShouldFail("a\""),
        test("a'",atm("a'")),
        testShouldFail("'a"),
        testShouldFail("\"a'"),
        testShouldFail("(a [b)]"),
        test("\"\\t\"",Atom(StringLiteral("\t"))),
        test("\"\\9\"",Atom(StringLiteral("\t"))),
        test("\"\\&\"",Atom(StringLiteral(""))),
        testShouldFail("\"\\z\""),
        test("a ;; comment\nb",lis(";","a","b")),
        testShouldFail("\u2045 a \u2046"), // left/right square bracket w/quill
        // inverted exclamation mark (valid binary op): \u00a1
        // inverted question mark (valid binary op): \u00bf
        test(
          "a \u00a1 b \u00a1 c",
          Liss(atm("\u00a1"),lis("\u00a1","a","b"),atm("c"))),
        test(
          "a \u00bf b \u00bf c",
          Liss(atm("\u00bf"),lis("\u00bf","a","b"),atm("c"))),
        testShouldFail("a \u00a1 b \u00bf c"),
        testShouldFail("a \u00bf b \u00a1 c")
      )
    val (passed,failed) = tests.partition(bo => bo)
    println(
      s"Of ${tests.size} tests, ${passed.size} passed, ${failed.size} failed.")
  }
  def tryItOut: Unit = {
    println("End each multiline expression with ` (backquote) alone on a line,")
    println("or `` (two backquotes) to quit altogehter.")
    def next: Unit = {
      println("Type an Uh expression to parse:")
      def takeLines (acc: List[String]): (String,Boolean) =
        io.StdIn.readLine match {
          case "`" => (acc.reverse.mkString("\n"),false)
          case "``" => (acc.reverse.mkString("\n"),true)
          case s => takeLines(s :: acc)
        }
      val (in,stop) = takeLines(Nil)
      testParse(in) match {
        case Right(res) =>
          println(
            s"\n$res\n\n${uhStr(res)}\n\n${res.notedString}\n\n" ++
              s"${res.fullyNotedString}\n")
        case Left(errMsg) =>
          println(errMsg)
      }
      if (! stop)
        next
    }
    next
  }

}
