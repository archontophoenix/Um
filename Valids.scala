package um

// Applicative and monadic validation //////////////////////////////////////////
// map2 obeys applicative functor laws; flatMap obeys monad laws ///////////////
// but map2 is not implemented in terms of flatMap /////////////////////////////
// which appears to violate an unwritten law ///////////////////////////////////
// but it's useful to treat validation sometimes applicatively, sometimes //////
// monadically /////////////////////////////////////////////////////////////////

object Valids {

  sealed trait Valid [+G,+B] {
    def map [H] (f: G => H): Valid[H,B] = Valid.app(Valid(f))(this)
    def flatMap [H,BB >: B] (f: G => Valid[H,BB]): Valid[H,BB] = this match {
      case Good(g) => f(g)
      case Bad(b,bs) => Bad(b,bs)
    }
    def ++ [BB >: B] (bad: Bad[BB]): Bad[BB] = this match {
      case Good(_) => bad
      case Bad(b,bs) => Bad(b,bs ++ (bad.head :: bad.tail))
    }
    def isGood: Boolean = this match {
      case Good(_) => true
      case _ => false
    }
    def mapBad [C] (f: B => C): Valid[G,C] = this match {
      case Good(g) => Good(g)
      case Bad(b,bs) => Bad(f(b),bs.map(f))
    }
  }
  object Valid {
    def apply [A] (a: A): Valid[A,Nothing] = Good(a)
    def map2 [X,Y,Z,B]
        (vx: Valid[X,B], vy: Valid[Y,B]) (f: (X,Y) => Z): Valid[Z,B] =
      vx match {
        case Good(x) => vy match {
          case Good(y) => Good(f(x,y))
          case Bad(by,bys) => Bad(by,bys)
        }
        case Bad(bx,bxs) => vy match {
          case Good(_) => Bad(bx,bxs)
          case Bad(by,bys) => Bad(bx,bxs ++ (by :: bys))
        }
      }
    def flatten [G,B] (v: Valid[Valid[G,B],B]): Valid[G,B] = v match {
      case Good(Good(g)) => Good(g)
      case Good(Bad(b,bs)) => Bad(b,bs)
      case Bad(b,bs) => Bad(b,bs)
    }
    def flatMap2 [X,Y,Z,B,BB >: B]
          (vx: Valid[X,B], vy: Valid[Y,B]) (f: (X,Y) => Valid[Z,BB]):
        Valid[Z,BB] =
      flatten(map2(vx,vy)(f))
    def app [X,Y,B] (vf: Valid[X => Y,B]) (vx: Valid[X,B]): Valid[Y,B] =
      map2(vf,vx)(_(_))
  }
  case class Good [+A] (a: A) extends Valid[A,Nothing]
  case class Bad [+B] (head: B, tail: List[B] = Nil) extends Valid[Nothing,B] {
    def toList = head :: tail
    def +++ [BB >: B] (v: Valid[_,BB]): Bad[BB] = v match {
      case Good(_) => this
      case fail @ Bad(_,_) => this ++ fail
    }
  }

}
