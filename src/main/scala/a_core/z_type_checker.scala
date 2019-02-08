package a_core


class TypeChecker extends Evaluator with ContextBuilder[Value] {

  override protected def layers: Layers = Seq.empty

  type Self = TypeChecker

  override protected def newBuilder(ls: Layers): Self = new TypeChecker() {
    override protected def layers: Layers = ls.asInstanceOf[this.Layers] // wtf??
  }

  /**
    * **value is context dependent**, infer always produce a value in current context
    */
  protected def infer(term: Term): Value = {
    term match {
      case VariableReference(index) => abstractionType(index).get
      case Pi(domain, body) =>
        newAbstractionLayer(checkIsTypeThenEval(domain)).checkIsType(body)
        UniverseValue
      case Lambda(domain, body) =>
        val pty = checkIsTypeThenEval(domain)
        val ctx = newAbstractionLayer(pty)
        val vty = ctx.infer(body)
        PiValue(pty, v => Value.rebound(ctx.layerId(0).get, v, vty))
      case Application(left, right) =>
        infer(left) match {
          case PiValue(domain, map) =>
            map(checkThenEval(right, domain))
          case _ => throw new Exception("Cannot infer Application")
        }
      case Record(acyclic) =>
        var ctx = newDeclarationLayer()
        acyclic.flatten.foreach {
          case TypeDeclaration(name, body) =>
            ctx = ctx.newTypeDeclaration(name, ctx.checkIsTypeThenEval(body))
        }
        UniverseValue
      case Make(declarations) =>
        var ctx = newDeclarationLayer()
        declarations.foreach {
          case TypeDeclaration(name, body) =>
            ctx = ctx.newTypeDeclaration(name, ctx.checkIsTypeThenEval(body))
          case ValueDeclaration(name, body) =>
            ctx = declarationType(0, name) match {
              case Some(value) =>
                ctx.newDeclaration(name, ctx.checkThenEval(body, value), value)
              case None =>
                val it = ctx.infer(body)
                ctx.newDeclaration(name, ctx.eval(body), it)
            }
        }
        // for anonymous we always produce a non-dependent record type with all stuff inline
        RecordValue(AcyclicValuesGraph(ctx.declarationTypes(0).get, _ => AcyclicValuesGraph.empty))
      case Projection(left, name) =>
        infer(left) match {
          case RecordValue(map) =>
            val ev = eval(left)
            var cur = map
            var ret: Value = null
            while (cur.initials.nonEmpty && ret == null) {
              if (cur.initials.contains(name)) {
                ret = cur.initials(name)
              }
              cur = cur.remaining.apply(cur.initials.map(pair => (pair._1, ev.projection(pair._1))))
            }
            assert(ret != null)
            ret
          case _ => throw new Exception("Cannot infer Projection")
        }
      case DeclarationReference(index, name) =>
        declarationType(index, name).get
      case Sum(branches) =>
        assert(branches.map(_.name).toSet.size == branches.size, "Duplicated branches in Sum")
        branches.foreach(k => checkIsType(k.term))
        UniverseValue
      case Construct(_, _) =>
        throw new IllegalStateException("Inferring Construct directly is not supported, always annotate with type instead")
      case Split(left, right) =>
        infer(left) match {
          case SumValue(ts) => // right is bigger
            assert(ts.keySet.toSeq.sorted == right.map(_.name).sorted, "Split with duplicated or missing branches")
            if (ts.isEmpty) {
              throw new IllegalArgumentException("This can be any type, annotate it instead")
            } else {
              nonEmptyJoin(ts.map(pair => {
                val at = pair._2
                val term = right.find(_.name == pair._1).get.term
                newAbstractionLayer(at).infer(term)
                // LATER we should check the levels is correct here
              }).toSeq)
            }
          case _ => throw new Exception("Cannot infer Split")
        }

    }
  }


  /**
    * when checking, the type to be checked with will always be defined by a super-context of current context
    */
  protected def check(term: Term, typ: Value): Unit = {
    (term, typ) match {
      case (Lambda(domain, body), PiValue(pd, pv)) =>
        assert(equal(checkIsTypeThenEval(domain), pd))
        val ctx = newAbstractionLayer(pd)
        // this is really handy, to unbound this parameter
        ctx.check(body, pv(OpenVariableReference(ctx.layerId(0).get)))
      case (Make(makes), RecordValue(fields)) =>
        assert(makes.forall(_.isInstanceOf[ValueDeclaration]), "Type checked Make syntax should not contains type declarations")
        val vs = makes.map(_.asInstanceOf[ValueDeclaration])
        assert(vs.map(_.name).toSet.size == vs.size, "Duplicated make expression names")
        // type checking makes should not have mutual reference
        var cur = fields
        var ctx = newDeclarationLayer()
        while (cur.initials.nonEmpty) {
          // we don't allow this kind of thing
          //
          // a: A
          // c: C
          // a: A = ta
          // c: C = tc
          // where a, c is name, and other is term, and also ta depends on c and C depends on a
          for (pair <- cur.initials) {
            ctx = ctx.newTypeDeclaration(pair._1, pair._2)
          }
          val nv = cur.initials.map(pair => {
            val name = pair._1
            val body = vs.find(_.name == name).get.body
            check(body, pair._2)
            val v = eval(body)
            ctx = ctx.newDeclaration(name, v, pair._2)
            pair._1 -> v
          })
          cur = cur.remaining.apply(nv)
        }
      case (Construct(name, data), SumValue(ts)) =>
        assert(ts.contains(name))
        check(data, ts(name))
      case (_, _) =>
        assert(equal(infer(term), typ))
    }
  }


  /**
    * utilities
    */

  protected def checkThenEval(t: Term, v: Value): Value = { check(t, v); eval(t) }
  protected def checkIsTypeThenEval(t: Term): Value = { checkIsType(t); eval(t) }
  // no need to go inside check for now
  protected def checkIsType(t: Term): Unit = assert(equal(infer(t), UniverseValue))


  /**
    * main method
    */
  def check(module: Make): Value = infer(module)

}

