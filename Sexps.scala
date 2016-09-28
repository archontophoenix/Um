package um

import language.implicitConversions

// S-expressions (possibly annotated) //////////////////////////////////////////
// parameterized by atom type, annotation type /////////////////////////////////

object Sexps {

  sealed trait Sexp [+A,+N] {
    def map [B] (f: A => B): Sexp[B,N]
    def flatMap [B,M >: N] (f: A => Sexp[B,M]): Sexp[B,M]
    def notes: List[N]
    def mapNotes [M >: N] (f: List[N] => List[M]): Sexp[A,M]
    def unnote: Sexp[A,Nothing]
    def note [M >: N] (note: M): Sexp[A,M] = mapNotes(_ => List(note))
    def addNote [M >: N] (note: M): Sexp[A,M] = mapNotes(_ => note :: notes)
    def notesFrom [M >: N] (sexp: Sexp[_,M]): Sexp[A,M] =
      mapNotes(_ => sexp.notes)
    def noteString =
      if (notes.isEmpty) "" else s"from ${notes.reverse.mkString(", from ")}"
    def notedString: String = s"$noteString: $this"
    def fullyNotedString: String = {
      def notate (s: String) = if (notes.isEmpty) s else s"$s ($noteString)"
      this match {
        case Atom(a) => notate(a.toString)
        case Liss(l) => notate(l.map(_.fullyNotedString).mkString("["," ","]"))
        case h |: t => notate(s"${h.fullyNotedString} |: ${t.fullyNotedString}")
      }
    }
    def |: [B >: A,M >: N] (newHead: Sexp[B,M]): Pair[B,M] = Pair(newHead,this)
    override def equals (that: Any): Boolean = (this,that) match {
      case (Empty(),Empty()) => true
      case (Atom(a),Atom(b)) => a == b
      case (h0 |: t0,h1 |: t1) => h0 == h1 && t0 == t1
      case _ => false
    }
    override def hashCode: Int = this match {
      case Empty() => 33977
      case Atom(a) => (a.hashCode + 4703) * 5349
      case h |: t => ((h.hashCode + 7347) * 4341 + t.hashCode + 7417) * 7155
    }
    def structureString: String = super.toString
    override def toString: String = this match {
      case Atom(a) => a.toString
      case Liss(l) => l.map(_.toString).mkString("["," ","]")
      case h |: t => s"($h |: $t)"
    }
  }
  object Sexp {
    def apply [A,N] (a: A): Sexp[A,N] = Atom(a)
  }
  trait Liss[+A,+N] extends Sexp[A,N] {
    def map [B] (f: A => B): Liss[B,N]
    def flatMap [B,M >: N] (f: A => Sexp[B,M]): Liss[B,M]
    def mapNotes [M >: N] (f: List[N] => List[M]): Liss[A,M]
    def unnote: Liss[A,Nothing]
    def :|: [B >: A,M >: N] (newHead: Sexp[B,M]): ProperCons[B,M] =
      ProperCons(newHead,this)
    def mapElems [B >: A,C,M >: N] (f: Sexp[B,M] => C): List[C] = this match {
      case Empty() => Nil
      case h :|: t => f(h) :: t.mapElems(f)
    }
  }
  object Liss {
    def apply [A,N] (sexps: Sexp[A,N]*): Liss[A,N] =
      sexps.headOption match {
        case None => Empty()
        case Some(h) => h :|: Liss(sexps.tail: _*)
      }
    def of [A] (as: A*): Liss[A,Nothing] = Liss(as.map(Atom(_)): _*)
    def unapply [A,N] (l: Liss[A,N]): Option[List[Sexp[A,N]]] =
      Some(lissToList(l))
  }
  implicit def listToLiss [A,N] (ss: List[Sexp[A,N]]): Liss[A,N] =
    Liss(ss: _*)
  implicit def lissToList [A,N] (ss: Liss[A,N]): List[Sexp[A,N]] =
    ss match {
      case Empty() => Nil
      case h :|: t => h :: lissToList(t)
    }
  trait Empty [+N] extends Liss[Nothing,N] {
    def map [B] (f: Nothing => B): Empty[N]
    def flatMap [B,M >: N] (f: Nothing => Sexp[B,M]): Empty[M]
    def mapNotes [M >: N] (f: List[N] => List[M]): Empty[M]
    def unnote: Empty[Nothing]
  }
  object Empty {
    private case class NotedEmpty [+N] (notes: List[N]) extends Empty[N] {
      def map [B] (f: Nothing => B) = this
      def flatMap [B,M >: N] (f: Nothing => Sexp[B,M]) = this
      def mapNotes [M >: N] (f: List[N] => List[M]) = NotedEmpty(f(notes))
      def unnote = NotedEmpty(Nil)
    }
    def apply (): Empty[Nothing] = NotedEmpty(Nil)
    def unapply (e: Empty[_]): Boolean = true
  }
  trait Atom [+A,+N] extends Sexp[A,N] {
    def atom: A
    def map [B] (f: A => B): Atom[B,N]
    def mapNotes [M >: N] (f: List[N] => List[M]): Atom[A,M]
    def unnote: Atom[A,Nothing]
  }
  object Atom {
    private case class NotedAtom [+A,+N] (atom: A, notes: List[N])
        extends Atom[A,N] {
      def map [B] (f: A => B) = NotedAtom(f(atom),notes)
      def flatMap [B,M >: N] (f: A => Sexp[B,M]) = f(atom).mapNotes(_ => notes)
      def mapNotes [M >: N] (f: List[N] => List[M]) = NotedAtom(atom,f(notes))
      def unnote = NotedAtom(atom,Nil)
    }
    def apply [A] (a: A): Atom[A,Nothing] = NotedAtom(a,Nil)
    def unapply [A,_] (atom: Atom[A,_]): Option[A] = Some(atom.atom)
  }
  trait Pair [+A,+N] extends Sexp[A,N] {
    def head: Sexp[A,N]
    def tail: Sexp[A,N]
    def map [B] (f: A => B): Pair[B,N]
    def flatMap [B,M >: N] (f: A => Sexp[B,M]): Pair[B,M]
    def mapNotes [M >: N] (f: List[N] => List[M]): Pair[A,M]
    def unnote: Pair[A,Nothing]
  }
  object Pair {
    private case class NotedImproperCons [+A,+N] (
          head: Sexp[A,N], tail: Sexp[A,N], notes: List[N])
        extends Pair[A,N] {
      def map [B] (f: A => B) = NotedImproperCons(head.map(f),tail.map(f),notes)
      def flatMap [B,M >: N] (f: A => Sexp[B,M]) =
        // might turn into a proper cons!
        (head.flatMap(f) |: tail.flatMap(f)).mapNotes(_ => notes)
      def mapNotes [M >: N] (f: List[N] => List[M]) =
        NotedImproperCons(head,tail,f(notes))
      def unnote = NotedImproperCons(head.unnote,tail.unnote,Nil)
    }
    def apply [A,N] (h: Sexp[A,N], t: Sexp[A,N]): Pair[A,N] = t match {
      case l: Liss[A,N] => h :|: l
      case _ => NotedImproperCons(h,t,h.notes)
    }
  }
  object |: {
    def unapply [A,N] (p: Pair[A,N]): Option[(Sexp[A,N],Sexp[A,N])] =
      Some((p.head,p.tail))
  }
  trait ProperCons [+A,+N] extends Pair[A,N] with Liss[A,N] {
    def tail: Liss[A,N]
    def map [B] (f: A => B): ProperCons[B,N]
    def flatMap [B,M >: N] (f: A => Sexp[B,M]): ProperCons[B,M]
    def mapNotes [M >: N] (f: List[N] => List[M]): ProperCons[A,M]
    def unnote: ProperCons[A,Nothing]
  }
  object ProperCons {
    private case class NotedProperCons [+A,+N] (
          head: Sexp[A,N], tail: Liss[A,N], notes: List[N])
        extends ProperCons[A,N] {
      def map [B] (f: A => B) = NotedProperCons(head.map(f),tail.map(f),notes)
      def flatMap [B,M >: N] (f: A => Sexp[B,M]) =
        NotedProperCons(head.flatMap(f),tail.flatMap(f),notes)
      def mapNotes [M >: N] (f: List[N] => List[M]) =
        NotedProperCons(head,tail,f(notes))
      def unnote = NotedProperCons(head.unnote,tail.unnote,Nil)
    }
    def apply [A,N] (h: Sexp[A,N], t: Liss[A,N]): ProperCons[A,N] =
      NotedProperCons(h,t,h.notes)
  }
  object :|: {
    def unapply [A,N] (p: ProperCons[A,N]): Option[(Sexp[A,N],Liss[A,N])] =
      Some((p.head,p.tail))
  }

}
