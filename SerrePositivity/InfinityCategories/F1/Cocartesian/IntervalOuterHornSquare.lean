module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.IntervalOuterHorn

/-!
概要：実際の第二三角形の外ホーン制限は、元の第一三角形の写像と厳密に可換。
方針：外ホーンの二辺で対角と標的辺を比較する。
規約：同じ第二三角形と元の可縮な合成三角形空間を保持する。
使われ方：外ホーン延長の pullback の可換性と持ち上げの入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
local notation "c" => (ULift.up (1 : Fin 2))
variable (v : (intervalMappingSpace (coherentNerveVertex (cocartesianTransportDiagramValue F c))
  (coherentNerveVertex (cocartesianTransportDiagramValue G c))) _⦋0⦌)
local notation "E" => (vertexFiber (cocartesianHomIntervalEvaluation F G c) v)

/-- 元の固定成分 fiber の二つの三角形は、第二三角形の同じ外ホーン上で厳密に可換。 -/
lemma cocartesianIntervalOuterHornSquare :
    cocartesianIntervalSecondTriangleMap F G v ≫ ((pre (horn 2 2).ι).app CatInfinity.{u}) =
      cocartesianIntervalCompositionTriangleMap F G v ≫ cocartesianIntervalOuterHornMap F G v := by
  apply uncurry_injective
  rw [uncurry_pre_app]
  have hU := cocartesianIntervalSecondTriangleMap_uncurry F G v (𝟙 E)
  have hC := cocartesianIntervalCompositionTriangleMap_uncurry F G v (𝟙 E)
  simp only [Category.id_comp] at hU hC
  rw [hU]
  apply (horn₂₂.isPushout.map (tensorRight E)).hom_ext
  · change (horn₂₂.ι₀₂ ▷ E) ≫ ((horn 2 2).ι ▷ E) ≫
        cocartesianIntervalHomTriangle F G v 1 (𝟙 E) =
      (horn₂₂.ι₀₂ ▷ E) ≫ uncurry
        (cocartesianIntervalCompositionTriangleMap F G v ≫ cocartesianIntervalOuterHornMap F G v)
    rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι,
      cocartesianIntervalOuterHornMap_diagonal, hC,
      cocartesianIntervalHomTriangle_diagonal, cocartesianIntervalHomTriangle_diagonal]
  · change (horn₂₂.ι₁₂ ▷ E) ≫ ((horn 2 2).ι ▷ E) ≫
        cocartesianIntervalHomTriangle F G v 1 (𝟙 E) =
      (horn₂₂.ι₁₂ ▷ E) ≫ uncurry
        (cocartesianIntervalCompositionTriangleMap F G v ≫ cocartesianIntervalOuterHornMap F G v)
    rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι,
      cocartesianIntervalSecondTriangle_target, cocartesianIntervalOuterHornMap_target]

/-- 同じ外ホーンの比較条件は、元の二つの全三角形の対角の厳密な一致を与える。 -/
lemma cocartesianIntervalOuterHornComparison_diagonal {T : SSet.{u + 1}}
    (a : T ⟶ (ihom (Δ[2] : SSet.{u + 1})).obj CatInfinity.{u})
    (b : T ⟶ cocartesianIntervalCompositionSpace F G v)
    (h : a ≫ ((pre (horn 2 2).ι).app CatInfinity.{u}) =
      b ≫ cocartesianIntervalOuterHornMap F G v) :
    (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ innerTriangleExtensionUncurry b =
      (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ uncurry a := by
  have hh := congrArg (fun k => (horn₂₂.ι₀₂ ▷ T) ≫ uncurry k) h
  rw [uncurry_pre_app, ← Category.assoc, ← comp_whiskerRight, horn.ι_ι,
    cocartesianIntervalOuterHornMap_diagonal] at hh
  exact hh.symm

/-- 同じ外ホーンの比較条件は、第二三角形の元の標的辺の固定条件を与える。 -/
lemma cocartesianIntervalOuterHornComparison_target {T : SSet.{u + 1}}
    (a : T ⟶ (ihom (Δ[2] : SSet.{u + 1})).obj CatInfinity.{u})
    (b : T ⟶ cocartesianIntervalCompositionSpace F G v)
    (h : a ≫ ((pre (horn 2 2).ι).app CatInfinity.{u}) =
      b ≫ cocartesianIntervalOuterHornMap F G v) :
    (stdSimplex.δ (0 : Fin 3) ▷ T) ≫ uncurry a =
      fst (Δ[1] : SSet.{u + 1}) T ≫
        SSet.yonedaEquiv.symm (cocartesianIntervalCompositionFirstEdge G).edge := by
  have hh := congrArg (fun k => (horn₂₂.ι₁₂ ▷ T) ≫ uncurry k) h
  rw [uncurry_pre_app, ← Category.assoc, ← comp_whiskerRight, horn.ι_ι,
    cocartesianIntervalOuterHornMap_target] at hh
  exact hh

end SerrePositivity.InfinityCategories
