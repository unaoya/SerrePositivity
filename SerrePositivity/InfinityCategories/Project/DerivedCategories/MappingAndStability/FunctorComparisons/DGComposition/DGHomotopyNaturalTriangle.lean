module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Residual
/-!
概要：augmentation の自然性ホモトピーを使って、混合三角形の実二次係数を補正する。
方針：同じ次数 −1 の自然性成分を引き、二つの微分の中間項を消去する。
規約：任意の dg 圏。使われ方：augmentation prism の相 011 の HA 方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
/-- 自然性ホモトピーによる混合三角形の同じ補正は、実 HA 二次方程式を満たす。 -/
lemma dgHomotopyNaturalTriangle_differential (R : Type u) [CommRing R]
    {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {P₀ P₁ P₂ Y₁ Y₂ : D}
    (b₀₁ : GradedHom R P₀ P₁ 0) (b₁₂ : GradedHom R P₁ P₂ 0)
    (b₀₂ : GradedHom R P₀ P₂ 0) (b₀₁₂ : GradedHom R P₀ P₂ (-1))
    (a₁₂ : GradedHom R Y₁ Y₂ 0) (t₁ : GradedHom R P₁ Y₁ 0)
    (t₂ : GradedHom R P₂ Y₂ 0) (h₁₂ : GradedHom R P₁ Y₂ (-1))
    (ht₂ : (homObject R D P₂ Y₂).d 0 1 t₂ = 0) (hb₀₁ : (homObject R D P₀ P₁).d 0 1 b₀₁ = 0)
    (hb : (homObject R D P₀ P₂).d (-1) 0 b₀₁₂ = compose R (n := 0) b₁₂ b₀₁ (by omega) - b₀₂)
    (hh : (homObject R D P₁ Y₂).d (-1) 0 h₁₂ = compose R (n := 0) t₂ b₁₂ (by omega) -
      compose R (n := 0) a₁₂ t₁ (by omega)) :
    (homObject R D P₀ Y₂).d (-1) 0 (compose R (n := -1) t₂ b₀₁₂ (by omega) -
      compose R (n := -1) h₁₂ b₀₁ (by omega)) =
      compose R (n := 0) a₁₂ (compose R (n := 0) t₁ b₀₁ (by omega)) (by omega) -
        compose R (n := 0) t₂ b₀₂ (by omega) := by
  have h₁ : (homObject R D P₀ Y₂).d (-1) 0
      (compose R (n := -1) t₂ b₀₁₂ (by omega)) =
      compose R (n := 0) t₂ ((homObject R D P₀ P₂).d (-1) 0 b₀₁₂) (by omega) := by
    have hd := differential_compose R (D := D) (x := P₀) (y := P₂) (z := Y₂)
      (p := -1) (q := 0) (n := -1) t₂ b₀₁₂ (by omega)
    change (homObject R D P₀ Y₂).d (-1) 0
        (compose R (n := -1) t₂ b₀₁₂ (by omega)) =
      compose R (n := 0) ((homObject R D P₂ Y₂).d 0 1 t₂) b₀₁₂ (by omega) +
      (0 : ℤ).negOnePow • compose R (n := 0) t₂
        ((homObject R D P₀ P₂).d (-1) 0 b₀₁₂) (by omega) at hd
    simpa only [ht₂, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, Int.negOnePow_zero, one_smul, zero_add] using! hd
  have h₂ : (homObject R D P₀ Y₂).d (-1) 0
      (compose R (n := -1) h₁₂ b₀₁ (by omega)) =
      compose R (n := 0) ((homObject R D P₁ Y₂).d (-1) 0 h₁₂) b₀₁ (by omega) := by
    have hd := differential_compose R (D := D) (x := P₀) (y := P₁) (z := Y₂)
      (p := 0) (q := -1) (n := -1) h₁₂ b₀₁ (by omega)
    change (homObject R D P₀ Y₂).d (-1) 0
        (compose R (n := -1) h₁₂ b₀₁ (by omega)) =
      compose R (n := 0) ((homObject R D P₁ Y₂).d (-1) 0 h₁₂) b₀₁ (by omega) +
      (-1 : ℤ).negOnePow • compose R (n := 0) h₁₂
        ((homObject R D P₀ P₁).d 0 1 b₀₁) (by omega) at hd
    simpa only [hb₀₁, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, add_zero] using! hd
  calc
    _ = (homObject R D P₀ Y₂).d (-1) 0 (compose R (n := -1) t₂ b₀₁₂ (by omega)) -
        (homObject R D P₀ Y₂).d (-1) 0 (compose R (n := -1) h₁₂ b₀₁ (by omega)) :=
      ((homObject R D P₀ Y₂).d (-1) 0).hom.map_sub _ _
    _ = _ := by
      rw [h₁, h₂, hb, hh, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right,
        compose_assoc R b₀₁ b₁₂ t₂ (by omega), compose_assoc R b₀₁ t₁ a₁₂ (by omega)]
      abel
end SerrePositivity.InfinityCategories.Project.DerivedCategories
