module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.StrictTransportEnrichedDiagram
public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryEnrichedDiagramRealization
public import SerrePositivity.InfinityCategories.F1.Cocartesian.StraighteningCoherent

/-!
概要：元の strict transport の豊穣図式の実現は、構成済みの同じ分類主写像。
方針：底と全 fibration の共同単体の各 Hom を、同じ section の混合作用へ戻す。
規約：対象の値だけでなく、主写像の全対象・全高次で厳密に一致する。
使われ方：底変換比較を同じ分類主写像の間の比較へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 同じ底と全 fibration の対角評価は、元の section の混合作用による評価と一致する。 -/
lemma cocartesianStrictTransportEnrichedDiagram_diagonal
    {C J : Type u} [Category.{u} C] [LinearOrder J] (A : J ⥤ C)
    (T : EnrichedFunctor SSet.{u} (SimplicialThickening J)
      (CocartesianFibrationCategory (nerve C))) :
    diagonalQuasicategoryDiagramEvaluation A
      (T.comp SSet (cocartesianStrictTransportEnrichedDiagram C).toCoreEnrichedFunctor) =
    diagonalCocartesianSectionsEvaluation (A.op ⋙ underNerveDiagram C) T := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  have hij := SimplicialThickening.Path.le (P.obj 0)
  change (diagonalQuasicategoryDiagramHom A
    (T.comp SSet (cocartesianStrictTransportEnrichedDiagram C).toCoreEnrichedFunctor) i j).app n P =
    (diagonalCocartesianSectionsHom (A.op ⋙ underNerveDiagram C) T i j).app n P
  erw [diagonalQuasicategoryDiagramHom_of_le _ _ i j hij,
    diagonalCocartesianSectionsHom_of_le _ _ i j hij]
  rfl

/-- 元の strict transport の豊穣図式の実現は、元の同じ Cat∞ 値分類主写像そのもの。 -/
lemma cocartesianStrictTransportEnrichedDiagram_realization (C : Type u) [Category.{u} C] :
    (cocartesianStrictTransportEnrichedDiagram C).realization =
      cocartesianStraighteningCoherentMap C := by
  apply uncurry_injective
  rw [QuasicategoryEnrichedDiagram.realization, uncurry_natural_left,
    quasicategoryDiagramRealization, uncurry_curry, cocartesianStraighteningCoherentMap_uncurry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, T⟩
  exact cocartesianStrictTransportEnrichedDiagram_diagonal (strictDiagramSimplexBase σ.down) T

end SerrePositivity.InfinityCategories
