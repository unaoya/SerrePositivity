module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFacesGluing

/-! # 単射への面の持ち上げによる整合性

概要：同じ単体の面を単射の定義域へ持ち上げると、持ち上げた面は整合的。
方針：単射を合成して共通の順序写像の値を比較する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：実際の slice 境界からの部分境界写像。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite
open scoped _root_.Simplicial

/-- 概要：単射に沿って持ち上げた面を写像で評価すると整合的な面の族になる。
方針：単射を打ち消し、どちらも元の単体の同じ順序写像による制限になることを示す。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：slice 境界の二セルを部分境界へ貼る。 -/
lemma compatible_of_lifts {n : ℕ} {X Y Z : SSet.{u}}
    (S : Finset (Fin (n + 2))) (ι : Y ⟶ Z) [Mono ι] (f : Δ[n + 1] ⟶ Z)
    (lifts : ∀ j ∈ S, Δ[n] ⟶ Y)
    (hLift : ∀ j hj, lifts j hj ≫ ι = SSet.stdSimplex.δ j ≫ f) (σ : Y ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Compatible S (fun j hj => SSet.yonedaEquiv (lifts j hj ≫ σ)) := by
  intro m θ j l hjS hlS hj hl
  rw [SSet.yonedaEquiv_naturality, SSet.yonedaEquiv_naturality]
  apply congrArg SSet.yonedaEquiv
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply (cancel_mono ι).1
  rw [Category.assoc, hLift j hjS, Category.assoc, hLift l hlS,
    ← Category.assoc, ← Category.assoc]
  change (SSet.stdSimplex.map (SimplexCategory.factor_δ θ j) ≫
    SSet.stdSimplex.map (SimplexCategory.δ j)) ≫ f =
      (SSet.stdSimplex.map (SimplexCategory.factor_δ θ l) ≫
        SSet.stdSimplex.map (SimplexCategory.δ l)) ≫ f
  rw [← Functor.map_comp, ← Functor.map_comp,
    SimplexCategory.factor_δ_spec θ j hj, SimplexCategory.factor_δ_spec θ l hl]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
