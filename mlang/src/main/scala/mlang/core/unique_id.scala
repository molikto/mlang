package mlang.core


// TODO atomic long
private var uniqueIdGen =  0L

private[core] def newUniqueId(): Long = {
  val p = uniqueIdGen
  uniqueIdGen += 1
  p
}