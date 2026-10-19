module
public import SerrePositivity.InfinityCategories.Derived.DGGradedClosedPrecomposition

/-! # 始点の次数零細分に沿う二未知残差の式

概要：始点を次数零射で細分した三面の R・K は、元の残差の同じ射による前合成になる。
方針：通常順の結合則と加法性で二つの残差を計算する。
規約：次数零射の閉性も不要。使われ方：実細分三面からの R・K と回収した Q・A の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 欠けた三角形の残差は、始点の次数零前合成で厳密に移る。 -/
lemma dgTriangleMissingResidual_precompose {q x₀ x₁ x₂ : D}
    (s : GradedHom A q x₀ 0) (f₀₁ : GradedHom A x₀ x₁ 0)
    (f₀₂ : GradedHom A x₀ x₂ 0) (f₁₂ : GradedHom A x₁ x₂ 0) :
    compose A (n := 0) f₁₂ (compose A (n := 0) f₀₁ s (by decide)) (by decide) -
      compose A (n := 0) f₀₂ s (by decide) =
      compose A (n := 0) (compose A (n := 0) f₁₂ f₀₁ (by decide) - f₀₂) s (by decide) := by
  rw [compose_sub_left, compose_assoc A s f₀₁ f₁₂ (by decide)]

/-- 最上位式の既知残差も、同じ始点の次数零前合成で厳密に移る。 -/
lemma dgTriangleTopResidual_precompose {q x₀ x₁ x₃ : D}
    (s : GradedHom A q x₀ 0) (f₀₁ : GradedHom A x₀ x₁ 0)
    (h₀₁₃ h₀₂₃ : GradedHom A x₀ x₃ (-1)) (h₁₂₃ : GradedHom A x₁ x₃ (-1)) :
    compose A (n := -1) h₀₂₃ s (by decide) -
      compose A (n := -1) h₁₂₃ (compose A (n := 0) f₀₁ s (by decide)) (by decide) -
      compose A (n := -1) h₀₁₃ s (by decide) =
      compose A (n := -1) (h₀₂₃ - compose A (n := -1) h₁₂₃ f₀₁ (by decide) - h₀₁₃)
        s (by decide) := by
  rw [compose_sub_left, compose_sub_left, compose_assoc A s f₀₁ h₁₂₃ (by decide)]

end SerrePositivity.InfinityCategories
