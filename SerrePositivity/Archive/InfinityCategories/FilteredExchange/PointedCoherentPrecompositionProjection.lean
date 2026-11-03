module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedFamily

/-!
概要：元の全 coslice 前合成を pointed space に正規化しても元の射影を保持する。
方針：既存の全前合成の射影と標準正規化の射影を合成する。
規約：元の全反転 Hom と同じ図式を保持する。
使われ方：零面の全係数円柱の底固定条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 全係数の正規化した前合成は元の coslice 射影を厳密に被覆する。 -/
lemma pointedCoherentSourcePrecomposition_projection (K : KanObject.{u}) :
    (coherentCosliceSourcePrecomposition pointKanObject K ≫ pointedCoherentCosliceIso.hom) ≫
      pointedSpaceProjection =
    fst (sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex K)))
      ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom pointKanObject K).op) ≫
        sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex K)) := by
  rw [Category.assoc, pointedCoherentCosliceIso_projection,
    coherentCosliceSourcePrecomposition_over]

end SerrePositivity.InfinityCategories.F2
