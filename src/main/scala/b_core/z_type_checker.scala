package b_core

import a_utils.debug

import scala.collection.mutable


/**
  * a value is valid only in it's producing context and context extensions. you should not HAVE REFERENCE
  * to a invalid value
  */
class TypeChecker extends Evaluator with ContextBuilder[Value] {

  override protected def layers: Layers = Seq.empty

  type Self = TypeChecker


  override protected def newBuilder(ls: Layers): Self = new TypeChecker() {
    override protected def layers: Layers = ls.asInstanceOf[this.Layers] // wtf??
  }

  /**
    * **value is context dependent**, infer always produce a value in current context
    *
    * the returned type WILL NOT contains any empty proxy
    */
  protected def infer(term: Term): Value = {
    debug(s"Infer $term")
    term match {
      case VariableReference(index) => abstractionType(index).get
      case Pi(domain, body) =>
        newAbstractionLayer(checkIsTypeThenEval(domain)).checkIsType(body)
        UniverseValue
      case Primitive(name) =>
        Primitives.typ(name)
      case Lambda(domain, body) =>
        val pty = checkIsTypeThenEval(domain)
        val ctx = newAbstractionLayer(pty)
        val vty = ctx.infer(body)
        PiValue(pty, VP(v => Value.rebound(ctx.layerId(0).get, v, vty)))
      case Application(left, right) =>
        infer(left) match {
          case PiValue(domain, map) =>
            map(checkThenEval(right, domain))
          case _ => throw new Exception("Cannot infer Application")
        }
      case Cast(a, b) =>
        val v = checkIsTypeThenEval(b)
        check(a, v)
        v
      case Record(fields) =>
        var ctx = newDeclarationLayer()
        fields.foreach {
          case TypeDeclaration(name, body) =>
            ctx = ctx.newTypeDeclaration(name, ctx.checkIsTypeThenEval(body))
        }
        UniverseValue
      case m@Make(declarations) =>
        var ctx = newDeclarationLayer()
        val evaluated = mutable.Set.empty[String]
        val notEvaluated = mutable.Map.empty[String, (Term, Value)]
        declarations.foreach {
          case TypeDeclaration(name, body) =>
            ctx = ctx.newTypeDeclaration(name, ctx.checkIsTypeThenEval(body))
          case ValueDeclaration(name, body) =>
            val it = ctx.declarationType(0, name) match {
              case Some(ty) =>
                ctx.check(body, ty)
                ty
              case None =>
                body match { // allows inductive type to self reference
                  case Sum(_) => ctx = ctx.newTypeDeclaration(name, UniverseValue)
                  case _ =>
                }
                ctx.infer(body)
            }
            val component = m.mutualDependencies.find(_.contains(name)).get
            if (component.size == 1 && !m.directValueDependencies(name).contains(name)) {
              evaluated += name
              ctx = ctx.newDeclaration(name, ctx.eval(body), it)
            } else {
              notEvaluated.put(name, (body, it))
              if (
                component.forall(name => notEvaluated.keySet(name) &&
                    m.directValueDependencies(name).forall(a => evaluated(a) || notEvaluated.keySet.contains(a)))) {
                val toEvaluate = notEvaluated.filterKeys(component)
                // when eval, we eval in declaration order
                val values = ctx.eval(m.valueDeclarations.map(_.name).filter(toEvaluate.keySet).map(n => (n, toEvaluate(n)._1)))
                for (v <- values) {
                  ctx = ctx.newDeclaration(v._1, v._2, toEvaluate(v._1)._2)
                }
                evaluated ++= component
                notEvaluated --= component
              } else {
                ctx = ctx.newTypeDeclaration(name, it)
              }
            }
        }
        assert(notEvaluated.isEmpty && evaluated.size == m.valueDeclarations.size)
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
              cur = cur(cur.initials.map(pair => (pair._1, ev.projection(pair._1))))
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
          case SumValue(keys, ts) => // right is bigger
            assert(keys.toSeq.sorted == right.map(_.name).sorted, "Split with duplicated or missing branches")
            if (keys.isEmpty) {
              throw new IllegalArgumentException("This can be any type, annotate it instead")
            } else {
              CompareValue.nonEmptyJoin(keys.map(k => {
                val at = ts(k)
                val term = right.find(_.name == k).get.term
                newAbstractionLayer(at).infer(term)
                // LATER we should check the levels is correct here
              }).toSeq)
            }
          case _ => throw new Exception("Cannot infer Split")
        }

    }
  }


  protected def check(term: Term, typ: Value): Unit = {
    debug(s"Check $term")
    (term, typ) match {
      case (Lambda(domain, body), PiValue(pd, pv)) =>
        assert(CompareValue.equal(checkIsTypeThenEval(domain), pd))
        val ctx = newAbstractionLayer(pd)
        // this is really handy, to unbound this parameter
        ctx.check(body, pv(OpenVariableReference(ctx.layerId(0).get)))
      case (Make(makes), RecordValue(fields)) =>
        assert(makes.forall(_.isInstanceOf[ValueDeclaration]), "Type checked Make syntax should not contains type declarations (yet)")
        val vs = makes.map(_.asInstanceOf[ValueDeclaration])
        val names = vs.map(_.name).toSet
        assert(names.size == vs.size, "Duplicated make expression names")
        var cur = fields
        var ctx = newDeclarationLayer()
        while (cur.initials.nonEmpty) {
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
          cur = cur(nv)
        }
      case (Construct(name, data), SumValue(ks, ts)) =>
        assert(ks.contains(name))
        check(data, ts(name))
      case (_, _) =>
        assert(CompareValue.equal(infer(term), typ))
    }
  }


  /**
    * utilities
    */

  protected def checkThenEval(t: Term, v: Value): Value = { check(t, v); eval(t) }
  protected def checkIsTypeThenEval(t: Term): Value = { checkIsType(t); eval(t) }
  // no need to go inside check for now
  protected def checkIsType(t: Term): Unit = assert(CompareValue.equal(infer(t), UniverseValue))


  /**
    * main method
    */
  def check(module: Make): Value = infer(module)
}

