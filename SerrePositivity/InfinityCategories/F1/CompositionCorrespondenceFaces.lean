module

public import SerrePositivity.InfinityCategories.F1.CompositionCorrespondence

/-!
概要：合成三角形全体の普遍三角形の二つの辺を厳密に計算する。
方針：内ホーン制限と元の可変ホーンの二つの辺の式を使う。
規約：第一辺の全高次と指定第二辺を保持する。
使われ方：合成三角形の対角評価を同じ終点間の Hom 空間へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {X : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)

/-- 同じ全合成三角形の第一辺は、元の第一辺への射影の区間族。 -/
lemma compositionCorrespondenceEvaluation_first :
    (stdSimplex.δ (2 : Fin 3) ▷ compositionCorrespondence x g) ≫
        compositionCorrespondenceEvaluation x g =
      intervalMappingUncurry (compositionCorrespondenceFirst x g) := by
  calc
    _ = (horn₂₁.ι₀₁ ▷ compositionCorrespondence x g) ≫
        ((horn 2 1).ι ▷ compositionCorrespondence x g) ≫
          compositionCorrespondenceEvaluation x g := by
      rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι]
    _ = _ := by
      rw [compositionCorrespondenceEvaluation_horn, composableHomHornMap_first]

/-- 同じ全合成三角形の第二辺は、元の指定第二辺に定値。 -/
lemma compositionCorrespondenceEvaluation_last :
    (stdSimplex.δ (0 : Fin 3) ▷ compositionCorrespondence x g) ≫
        compositionCorrespondenceEvaluation x g =
      fst (Δ[1] : SSet.{u}) (compositionCorrespondence x g) ≫
        SSet.yonedaEquiv.symm g.edge := by
  calc
    _ = (horn₂₁.ι₁₂ ▷ compositionCorrespondence x g) ≫
        ((horn 2 1).ι ▷ compositionCorrespondence x g) ≫
          compositionCorrespondenceEvaluation x g := by
      rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι]
    _ = _ := by
      rw [compositionCorrespondenceEvaluation_horn, composableHomHornMap_last]

end SerrePositivity.InfinityCategories
