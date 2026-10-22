module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowEndpointCompatibility
public import SerrePositivity.InfinityCategories.F2.Ind.RightIntervalUniverseShape
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationExtension

/-!
概要：元の全試験族から構成する二段補間の、全図式と全境界を保持するデータ。
方針：始点全錐・元の円柱の slice 持ち上げ・終点 comma の全円柱延長を束ねる。
規約：元の図式 comma の余錐への帰還は別工程。使われ方：射図式の filtered 性。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の全試験族と全錐族を保った、実終点 comma 内の全円柱延長データ。 -/
structure IndArrowInterpolationData (κ : Cardinal.{u}) {C A : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D) where
  sourceCone : (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u})) ⟶
    pullback (indYoneda κ C) (sliceOverProjection D)
  sourceRestriction : (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ≫ sourceCone ≫
    diagramConePointRestriction κ D (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) =
      q ≫ diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  slicePrism : IndArrowSlicePrism κ D q
    ((SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ≫ sourceCone)
  extension : (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}) ⊗ Δ[1]) ⟶
    leftKanShape (indYoneda κ C)
      (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2))))
  old : (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0] ▷ (Δ[1] : SSet.{u})) ≫
    extension = rightIntervalUniverseShape A ≫ indArrowEndpointFamily κ D q
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ≫ sourceCone) slicePrism
  source : (SSet.uliftFunctor.{u + 1, u}).map SSet.ι₀ ≫ extension =
    indArrowSourceEndpointFamily κ D sourceCone

end SerrePositivity.InfinityCategories.F2.Ind
