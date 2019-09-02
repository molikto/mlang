package mlang.compiler



sealed trait ElaborateException extends CompilerException

object ElaborateException {


  // syntax
  case class FieldsDuplicated() extends ElaborateException
  case class TagsDuplicated() extends ElaborateException
  case class MustBeNamed() extends ElaborateException
  case class EmptyTelescope() extends ElaborateException
  case class EmptyArguments() extends ElaborateException

  // elimination mismatch
  case class UnknownAsType() extends ElaborateException
  case class UnknownProjection() extends Exception(s"Unknown projection") with ElaborateException
  case class UnknownAsFunction() extends ElaborateException


  case class CannotInferLambda() extends ElaborateException
  case class CannotInferReturningTypeWithPatterns() extends ElaborateException

  case class CannotInferObjectNow()  extends ElaborateException


  case class TypeMismatch() extends ElaborateException

  case class ForbiddenModifier() extends ElaborateException

  case class DeclarationWithoutDefinition() extends ElaborateException

  case class ExpectingDimension() extends ElaborateException

  case class PathEndPointsNotMatching() extends ElaborateException
  case class InferPathEndPointsTypeNotMatching() extends ElaborateException

  case class ExpectingLambdaTerm() extends ElaborateException

  case class CapNotMatching() extends ElaborateException
  case class FacesNotMatching() extends ElaborateException

  case class RequiresValidRestriction() extends ElaborateException
  case class TermICanOnlyAppearInDomainOfFunction() extends ElaborateException


  case class CannotInferMakeExpression() extends ElaborateException
  case class CannotInferVMakeExpression() extends ElaborateException

  case class VProjCannotInfer() extends ElaborateException

  case class CannotInferMeta() extends ElaborateException

  case class NotDefinedReferenceForTypeExpressions() extends ElaborateException


  case class NotExpectingImplicitArgument() extends ElaborateException

  case class RecursiveTypesMustBeDefinedAtTopLevel() extends ElaborateException

  case class UpCanOnlyBeUsedOnTopLevelDefinitionOrUniverse()  extends ElaborateException

  case class AlreadyDeclared() extends ElaborateException
  case class AlreadyDefined() extends ElaborateException
  case class NotDeclared() extends ElaborateException
  case class SeparateDefinitionCannotHaveTypesNow() extends ElaborateException
  case class DimensionLambdaCannotBeImplicit() extends ElaborateException
  case class CannotInferPathTypeWithoutBody() extends ElaborateException

  // TODO maybe we should just show a warning
  case class RemoveFalseFace() extends ElaborateException
  case class RemoveConstantVType() extends ElaborateException
  case class VTypeDimensionInconsistent() extends ElaborateException

  case class VMakeMismatch() extends ElaborateException
}

