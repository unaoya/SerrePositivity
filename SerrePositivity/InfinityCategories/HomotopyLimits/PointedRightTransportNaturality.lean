module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PointedRightMorphismTransport

/-!
概要：右 Hom の恒等点による fiber 比較は、元の Kan 射と元の辺輸送に自然。
方針：動く一点係数の全族を合成輸送の同じ四角形へ入力する。
規約：一点係数も元の射も反転しない。使われ方：既存の値比較の自然性への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 動く元の点の族を右 Hom へ送り恒等点を輸送すると、指定右 fiber 比較の前合成になる。 -/
lemma pointedRightFiberComparison_parameter (K : KanObject.{u}) {P : SSet.{u + 1}}
    (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj) :
    diagonalFiberTransport pointedSpaceProjection (SSet.const pointedSpaceIdentityPoint)
      (x ≫ (SSet.uliftFunctor.{u + 1, u}).map (pointFunctorEvaluationIso K.obj).inv ≫
        coherentKanRightHomInterval pointKanObject K) = x ≫ pointedRightFiberComparison K := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 元の Kan 射と元の coherent 辺に沿う輸送は、右 fiber 比較を介して全点で可換。 -/
def pointedRightFiberComparison_transportIso {K L : KanObject.{u}} (f : K ⟶ L) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map f ≫ pointedRightFiberComparison L)
      (pointedRightFiberComparison K ≫ edgeTransport pointedSpaceProjection
        (pointedRightMorphismEdge f)) := by
  let x := (SSet.uliftFunctor.{u + 1, u}).map (pointFunctorEvaluationIso K.obj).inv
  let y : (SSet.uliftFunctor.{u + 1, u}).obj K.obj ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L) :=
    SSet.const (ULift.up (functorVertex f))
  have e := coherentKanRightCompositionTransport_diagonalIso pointKanObject K L
    pointedSpaceIdentityPoint x y
  have hs : diagonalFiberTransport pointedSpaceProjection (SSet.const pointedSpaceIdentityPoint)
      (x ≫ coherentKanRightHomInterval pointKanObject K) = pointedRightFiberComparison K := by
    simpa only [Category.id_comp] using pointedRightFiberComparison_parameter K (𝟙 _)
  have hy : y ≫ coherentKanRightHomInterval K L =
      SSet.const (intervalMappingVertexOfEdge (pointedRightMorphismEdge f)) := by
    rw [SSet.const_comp, coherentKanRightHomInterval_morphism]
  have hl : lift x y ≫ coherentHomComposition pointKanObject K L ≫
      coherentKanRightHomInterval pointKanObject L =
      (SSet.uliftFunctor.{u + 1, u}).map f ≫
        (SSet.uliftFunctor.{u + 1, u}).map (pointFunctorEvaluationIso L.obj).inv ≫
          coherentKanRightHomInterval pointKanObject L := by
    rw [← Category.assoc, coherentRightPointCoefficient_post, Category.assoc]
  rw [hs, hy, hl, pointedRightFiberComparison_parameter] at e
  exact e.symm ≪≫ diagonalFiberTransport_edgeIso pointedSpaceProjection
    (pointedRightMorphismEdge f) (pointedRightFiberComparison K)

end SerrePositivity.InfinityCategories.HomotopyLimits
