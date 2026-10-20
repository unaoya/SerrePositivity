module

public import SerrePositivity.InfinityCategories.F1.CoherentLeftIntervalComparison
public import SerrePositivity.InfinityCategories.F1.PointedReverseFiberCoordinates

/-!
概要：実際の pointed 輸送の辺パラメーターと、既存の左 Hom の区間比較の一致。
方針：反対 Kan nerve から戻す同型を一般の反転区間比較へ代入する。
規約：標準頂点への表示変更だけを行い、辺や fiber の逆同値を選ばない。
使われ方：反転した合成の輸送族を既存の左解像比較と同じ Hom の族で使用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 実際の pointed 輸送の反転した辺の族は、既存の左 Hom の区間族そのもの。 -/
lemma pointedReverseKanHomInterval_eq_left (K L : KanObject.{u}) :
    pointedReverseKanHomInterval K L = coherentLeftHomInterval K L := by
  rw [coherentLeftHomInterval_eq_reverse]
  rfl

/-- 同じ辺パラメーター射は、端点表示を揃えると左 coslice Hom の区間比較に一致する。 -/
lemma pointedReverseKanHomIntervalMap_eq_left (K L : KanObject.{u}) :
    intervalMappingCurryOfEndpoints (pointedReverseKanHomInterval K L)
      (pointedReverseKanHomInterval_zero K L) (pointedReverseKanHomInterval_one K L) =
    ((HomotopyLimits.uliftOppositeIso (SimplicialCategory.sHom K L)).inv ≫
      HomotopyLimits.coherentCosliceFiberComparison K L ≫
      cosliceFiberToIntervalMappingSpace (coherentNerveVertex K) (coherentNerveVertex L)) ≫
    intervalMappingPostOfEq (𝟙 SpaceInfinity.{u}) (coherentNerveVertex K) (coherentNerveVertex L)
      (spaceInfinityVertex_eq_coherent K).symm (spaceInfinityVertex_eq_coherent L).symm := by
  apply intervalMappingUncurry_injective _ _
  rw [intervalMappingUncurry_curryOfEndpoints, intervalMappingPostOfEq_uncurry]
  exact (pointedReverseKanHomInterval_eq_left K L).trans (Category.comp_id _).symm

end SerrePositivity.InfinityCategories
