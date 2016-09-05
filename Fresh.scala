package um

// Freshness: a distinct (at each allocation) value, with no visible data //////

// TODO: make String conversion go through a separately allocated object. This
// would eliminate side effects that might occur from using Freshnesses without
// exporting them.

object Fresh {
  private val nextID = new java.util.concurrent.atomic.AtomicLong(0)
  private val nextName = new java.util.concurrent.atomic.AtomicLong(0)
  def fresh (): Freshness = new Freshness(nextID.getAndIncrement())
  sealed class Freshness (private[Fresh] val id: Long) {
    override def equals (that: Any): Boolean = that match {
      case that: Freshness => this.id == that.id
      case _ => false
    }
    override def hashCode: Int =
      (id.toInt + 443582355) * 4435 + (id >> 32).toInt * 82355
    override lazy val toString: String = nextName.getAndIncrement().toString
  }
}
