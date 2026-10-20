module
public import SerrePositivity.KST.SConstruction.CorrectionInterchangePasting

/-! # 六面複体内の元の交換ホーンの両全辺
概要：元の四面複体から貼ったホーンの両辺を、同じ交換第二面の両全辺として回収する。
方針：元のホーン包含・三角形包含の pushout の厳密な可換性を使う。
規約：実複体内の全区間の等号であり、写像先での一致だけにしない。
使われ方：外側二部分面を貼るための共有頂点の厳密な回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 元のホーン第一辺は、同じ六面複体内で交換第二面の同じ全下面。 -/
lemma correctionInterchangePasting_lower :
    correctionPastingLower.{u} ≫ correctionInterchangePastingOriginal =
      stdSimplex.δ 2 ≫ correctionInterchangePastingSecond := by
  unfold correctionInterchangePastingOriginal correctionInterchangePastingSecond
  calc
    _ = horn₂₁.ι₀₁ ≫ correctionPastingHorn ≫ correctionPastingTriangleOriginal ≫
        correctionInterchangePastingIntermediate := by
      simp only [← Category.assoc, correctionPastingHorn_lower]
    _ = horn₂₁.ι₀₁ ≫ (SSet.horn 2 (1 : Fin 3)).ι ≫ correctionPastingTriangleCell ≫
        correctionInterchangePastingIntermediate := by
      simpa only [Category.assoc] using
        congrArg (fun q => horn₂₁.ι₀₁ ≫ q ≫ correctionInterchangePastingIntermediate)
          correctionPastingTriangle_shared.{u}
    _ = _ := by rw [← Category.assoc, SSet.horn.ι_ι]

/-- 元のホーン第二辺も、同じ六面複体内で交換第二面の同じ全上面。 -/
lemma correctionInterchangePasting_upper :
    correctionPastingUpper.{u} ≫ correctionInterchangePastingOriginal =
      stdSimplex.δ 0 ≫ correctionInterchangePastingSecond := by
  unfold correctionInterchangePastingOriginal correctionInterchangePastingSecond
  calc
    _ = horn₂₁.ι₁₂ ≫ correctionPastingHorn ≫ correctionPastingTriangleOriginal ≫
        correctionInterchangePastingIntermediate := by
      simp only [← Category.assoc, correctionPastingHorn_upper]
    _ = horn₂₁.ι₁₂ ≫ (SSet.horn 2 (1 : Fin 3)).ι ≫ correctionPastingTriangleCell ≫
        correctionInterchangePastingIntermediate := by
      simpa only [Category.assoc] using
        congrArg (fun q => horn₂₁.ι₁₂ ≫ q ≫ correctionInterchangePastingIntermediate)
          correctionPastingTriangle_shared.{u}
    _ = _ := by rw [← Category.assoc, SSet.horn.ι_ι]

end SerrePositivity.KST.SConstruction
