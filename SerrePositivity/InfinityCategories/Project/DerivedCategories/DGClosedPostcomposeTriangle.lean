module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Residual
/-!
概要：閉次数零射の後合成で、実三角形の同じ二次方程式を保存する。
方針：全 dg Leibniz 則の零次数因子と実結合律を使う。
規約：任意の dg 圏。使われ方：augmentation prism の相 001 の実二次係数。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
/-- 同じ閉零射で後合成した実三角係数の微分方程式。 -/
lemma dgClosedPostcomposeTriangle_differential (R : Type u) [CommRing R]
    {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {P₀ P₁ P₂ Y : D}
    (b₀₁ : GradedHom R P₀ P₁ 0) (b₁₂ : GradedHom R P₁ P₂ 0)
    (b₀₂ : GradedHom R P₀ P₂ 0) (b₀₁₂ : GradedHom R P₀ P₂ (-1))
    (t : GradedHom R P₂ Y 0) (ht : (homObject R D P₂ Y).d 0 1 t = 0)
    (hb : (homObject R D P₀ P₂).d (-1) 0 b₀₁₂ =
      compose R (n := 0) b₁₂ b₀₁ (by omega) - b₀₂) :
    (homObject R D P₀ Y).d (-1) 0 (compose R (n := -1) t b₀₁₂ (by omega)) =
      compose R (n := 0) (compose R (n := 0) t b₁₂ (by omega)) b₀₁ (by omega) -
        compose R (n := 0) t b₀₂ (by omega) := by
  have hd := differential_compose R (D := D) (x := P₀) (y := P₂) (z := Y)
    (p := -1) (q := 0) (n := -1) t b₀₁₂ (by omega)
  change (homObject R D P₀ Y).d (-1) 0 (compose R (n := -1) t b₀₁₂ (by omega)) =
    compose R (n := 0) ((homObject R D P₂ Y).d 0 1 t) b₀₁₂ (by omega) +
    (0 : ℤ).negOnePow • compose R (n := 0) t
      ((homObject R D P₀ P₂).d (-1) 0 b₀₁₂) (by omega) at hd
  have he : (homObject R D P₀ Y).d (-1) 0 (compose R (n := -1) t b₀₁₂ (by omega)) =
      compose R (n := 0) t ((homObject R D P₀ P₂).d (-1) 0 b₀₁₂) (by omega) := by
    simpa only [ht, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, Int.negOnePow_zero, one_smul, zero_add] using! hd
  rw [he, hb, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right, compose_assoc R b₀₁ b₁₂ t (by omega)]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
