package um

// Lists of items of alternating types, of even length or odd length ///////////

object Alts {

  sealed trait Alt[+A,+B] {
    def *: [BB >: B] (newHead: BB): Alt[BB,A]
  }
  sealed trait EvAlt[+A,+B] extends Alt[A,B] {
    def isEmpty: Boolean = this match {
      case EvNil => true
      case _ => false
    }
    def reverse: EvAlt[B,A] = prependReversed(this,EvNil)
    def *: [BB >: B] (newHead: BB): OdAlt[BB,A] = OdAlt(newHead,this)
    def :* [AA >: A] (newLast: AA): OdAlt[AA,B] = (newLast *: reverse).reverse
    def ++ [AA >: A,BB >: B] (that: EvAlt[AA,BB]): EvAlt[AA,BB] =
      prependReversed(reverse,that)
    def ++ [AA >: A,BB >: B] (that: OdAlt[AA,BB]): OdAlt[AA,BB] =
      prependReversed(reverse,that)
  }
  case class EvCons [+A,+B] (head: A, tail: OdAlt[B,A]) extends EvAlt[A,B]
  object EvNil extends EvAlt[Nothing,Nothing]
  case class OdAlt [+A,+B] (head: A, tail: EvAlt[B,A]) extends Alt[A,B] {
    def reverse: OdAlt[A,B] = prependReversed(tail,OdAlt(head,EvNil))
    def *: [BB >: B] (newHead: BB): EvAlt[BB,A] = EvCons(newHead,this)
    def :* [BB >: B] (newLast: BB): EvAlt[A,BB] = (newLast *: reverse).reverse
    def ++ [AA >: A,BB >: B] (that: EvAlt[BB,AA]): OdAlt[AA,BB] =
      prependReversed(reverse,that)
    def ++ [AA >: A,BB >: B] (that: OdAlt[BB,AA]): EvAlt[AA,BB] =
      prependReversed(reverse,that)
  }
  object *: {
    def unapply [A,B] (alt: EvAlt[A,B]): Option[(A,OdAlt[B,A])] = alt match {
      case EvNil => None
      case EvCons(hd,tl) => Some((hd,tl))
    }
    def unapply [A,B] (alt: OdAlt[A,B]): Option[(A,EvAlt[B,A])] = alt match {
      case OdAlt(hd,tl) => Some((hd,tl))
    }
  }
  def prependReversed [A,B] (src: EvAlt[A,B], dst: EvAlt[B,A]): EvAlt[B,A] =
    src match {
      case EvNil => dst
      case h0 *: h1 *: tl => prependReversed(tl,h1 *: h0 *: dst)
    }
  def prependReversed [A,B] (src: EvAlt[A,B], dst: OdAlt[B,A]): OdAlt[B,A] =
    src match {
      case EvNil => dst
      case h0 *: h1 *: tl => prependReversed(tl,h1 *: h0 *: dst)
    }
  def prependReversed [A,B] (src: OdAlt[A,B], dst: EvAlt[B,A]): OdAlt[A,B] =
    src match {
      case h0 *: h1 *: tl => prependReversed(tl,h1 *: h0 *: dst)
    }
  def prependReversed [A,B] (src: OdAlt[A,B], dst: OdAlt[B,A]): EvAlt[A,B] =
    src match {
      case h0 *: h1 *: tl => prependReversed(tl,h1 *: h0 *: dst)
    }
  def evAlt [A,B] (items: List[(A,B)], acc: EvAlt[B,A] = EvNil): EvAlt[A,B] =
    items match {
      case Nil => acc.reverse
      case (a,b) :: tl => evAlt(tl,b *: a *: acc)
    }
}
