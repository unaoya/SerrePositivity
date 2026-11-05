module
public import SerrePositivity.KST.Fibration.SpanCompatibleTransportRepresentation
public import SerrePositivity.InfinityCategories.F1.Transport.PointedFamilyPointHom

/-! # 指定復元 span の同じ三角を元の全空間の点と pointed space で評価する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
namespace StrictTransportComparisonSpan
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  {p : E ⟶ nerve I} [LeftFibration p] (s : _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan p)

/-- 相対三角の元の全空間への像。元の二脚と同じ比較射を使う。 -/
def representationTriangle :
    FunctorIso (s.coherentSource ≫ s.coherentComparison.hom) s.coherentTarget :=
  VertexIso.map s.coherentComparison.triangle
    (vertexFiberι
      ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj s.total)).map
        (leftUnstraighteningProjection (leftCoherentTransport p)))
      (functorVertex s.coherentBase))

/-- 元の指定点で同じ三角を評価した全空間の比較。 -/
def representationTotalPointIso (z : s.total _⦋0⦌) : VertexIso
    ((s.coherentSource ≫ s.coherentComparison.hom).app (Opposite.op ⦋0⦌) (ULift.up z))
    (s.coherentTarget.app (Opposite.op ⦋0⦌) (ULift.up z)) := by
  have : InnerFibration s.projection := s.inner
  have : Quasicategory s.total := quasicategory_of_innerFibration s.projection
  exact s.representationTriangle.app (ULift.up z)

/-- 表現の同じ pointed map と weighted 脚の同じ指定点を結ぶ実比較。 -/
def representationPointedPointIso (z : s.total _⦋0⦌) : VertexIso
    ((s.coherentSource ≫ s.representation.pointedMap).app
      (Opposite.op ⦋0⦌) (ULift.up z))
    ((s.coherentTarget ≫ pullback.fst pointedSpaceProjection (leftCoherentTransport p)).app
      (Opposite.op ⦋0⦌) (ULift.up z)) :=
  VertexIso.map (s.representationTotalPointIso z)
    (pullback.fst pointedSpaceProjection (leftCoherentTransport p))

/-- 同じ指定点比較の底への作用は、元の点の射を保持する。 -/
theorem representationPointedPointIso_pointHom (z : s.total _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom ((s.coherentSource ≫ s.representation.pointedMap).app
      (Opposite.op ⦋0⦌) (ULift.up z)) ≫
      (hoFunctor.map pointedSpaceProjection).toFunctor.map
        (s.representationPointedPointIso z).hom =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom
      ((s.coherentTarget ≫ pullback.fst pointedSpaceProjection (leftCoherentTransport p)).app
        (Opposite.op ⦋0⦌) (ULift.up z)) := by
  have h := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom_comp_projection
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexFiberPoint ((s.coherentSource ≫ s.representation.pointedMap).app
      (Opposite.op ⦋0⦌) (ULift.up z)))
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexFiberPoint
      ((s.coherentTarget ≫ pullback.fst pointedSpaceProjection (leftCoherentTransport p)).app
        (Opposite.op ⦋0⦌) (ULift.up z)))
    (s.representationPointedPointIso z).hom
  change _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom ((s.coherentSource ≫ s.representation.pointedMap).app
    (Opposite.op ⦋0⦌) (ULift.up z)) ≫
      (𝟙 _ ≫ (hoFunctor.map pointedSpaceProjection).toFunctor.map
        (s.representationPointedPointIso z).hom ≫ 𝟙 _) =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom
      ((s.coherentTarget ≫ pullback.fst pointedSpaceProjection (leftCoherentTransport p)).app
        (Opposite.op ⦋0⦌) (ULift.up z)) at h
  simpa only [Category.id_comp, Category.comp_id] using h

end StrictTransportComparisonSpan
end SerrePositivity.KST.Fibration
