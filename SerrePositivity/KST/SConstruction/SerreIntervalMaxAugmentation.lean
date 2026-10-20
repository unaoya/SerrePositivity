module
public import SerrePositivity.KST.SConstruction.SerreIntervalMaxSymmetry

/-! # 元の max connection の増大保存
概要：元の max connection は、tensor 余モノイドの増大写像を保存する。
方針：元の全斉次生成元の対で判定し、端点は単位、辺は零へ写す式を使う。
規約：元の単位射を保持する。使われ方：connection の余モノイド射への束ね。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の max connection は、元の tensor 単位射に沿って増大を保存する。 -/
lemma serreIntervalMax_augmentation :
    serreIntervalMax A ≫ serreIntervalAugmentation A =
      (serreIntervalAugmentation A ⊗ₘ serreIntervalAugmentation A) ≫
        (λ_ (𝟙_ (Complex A))).hom := by
  apply serreIntervalTensor_hom_ext A
  intro i j n hn
  simp only [chain_comp_apply]
  fin_cases i <;> fin_cases j
  all_goals
    first
    | have hn' : n = 0 := by simpa [serreIntervalGeneratorDegree] using hn.symm
    | have hn' : n = -1 := by simpa [serreIntervalGeneratorDegree] using hn.symm
    | have hn' : n = -2 := by simpa [serreIntervalGeneratorDegree] using hn.symm
    rcases hn' with rfl
    dsimp only [serreIntervalGeneratorDegree, serreIntervalGenerator]
    rw [tensorMap_apply]
    simp only [serreIntervalMax_zero_apply, serreIntervalMax_one_apply,
      serreIntervalMax_edge_zero, serreIntervalMax_edge_one, serreIntervalMax_edge_edge,
      chain_comp_apply, serreIntervalAugmentation_zero_value,
      serreIntervalAugmentation_one_value, serreIntervalAugmentation_edge,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero,
      leftUnitor_hom_generator]
  all_goals
    first
    | rfl
    | exact congrArg (fun f => f.f 0 (1 : A)) (serreIntervalAugmentation_one A)

end SerrePositivity.KST.SConstruction
