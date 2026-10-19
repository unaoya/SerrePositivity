module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornFaceDifferentials

/-! # 最後外ホーンの二残差の微分整合性

概要：Q を解く前から、既知残差 K の微分は最後の閉辺と Q 側残差 R の合成の負になる。
方針：指定三面の微分式、最初の辺の閉性、Leibniz と結合則を使う。
規約：dR = 0、dK = −f23 R。使われ方：最後の閉辺の cone に入る閉成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 三つの三角形の微分式から、二未知式の既知残差の微分を計算する。 -/
lemma dgTriangleResidual_differential {x₀ x₁ x₂ x₃ : D}
    (f₀₁ : GradedHom A x₀ x₁ 0) (f₀₂ : GradedHom A x₀ x₂ 0)
    (f₀₃ : GradedHom A x₀ x₃ 0) (f₁₂ : GradedHom A x₁ x₂ 0)
    (f₁₃ : GradedHom A x₁ x₃ 0) (f₂₃ : GradedHom A x₂ x₃ 0)
    (h₀₁₃ h₀₂₃ : GradedHom A x₀ x₃ (-1)) (h₁₂₃ : GradedHom A x₁ x₃ (-1))
    (d₀₁ : differential A f₀₁ = 0)
    (d₀₁₃ : differential A h₀₁₃ = compose A f₁₃ f₀₁ (by decide) - f₀₃)
    (d₀₂₃ : differential A h₀₂₃ = compose A f₂₃ f₀₂ (by decide) - f₀₃)
    (d₁₂₃ : differential A h₁₂₃ = compose A f₂₃ f₁₂ (by decide) - f₁₃) :
    differential A (h₀₂₃ - compose A h₁₂₃ f₀₁ (by decide) - h₀₁₃) =
      -compose A f₂₃ (compose A f₁₂ f₀₁ (by decide) - f₀₂) (by decide) := by
  rw [differential_sub, differential_sub, differential_compose, d₀₁,
    compose_zero, smul_zero, add_zero, d₀₂₃, d₁₂₃, d₀₁₃, compose_sub_left,
    ← compose_assoc A f₀₁ f₁₂ f₂₃ (by decide), compose_sub_right]
  abel

open CategoryTheory SSet
open scoped Simplicial

/-- 実三次最後外ホーンの既知残差は、最後の閉辺と Q 側残差を微分で結ぶ。 -/
lemma dgLastHornTopResidual_differential
    (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ dgNerve A D) :
    differential A (dgLastHornTopResidual σ) =
      -compose A ((HornData.knownData σ).edgeHom 2 3 (by decide))
        (dgLastHornMissingResidual σ) (by decide) := by
  let s := HornData.knownData σ
  exact dgTriangleResidual_differential
    (s.edgeHom 0 1 (by decide)) (s.edgeHom 0 2 (by decide)) (s.edgeHom 0 3 (by decide))
    (s.edgeHom 1 2 (by decide)) (s.edgeHom 1 3 (by decide)) (s.edgeHom 2 3 (by decide))
    (s.tripleHom 0 1 3 (by decide) (by decide)) (s.tripleHom 0 2 3 (by decide) (by decide))
    (s.tripleHom 1 2 3 (by decide) (by decide)) (dgLastHornFirstEdge_closed σ)
    (dgLastHornKnownFace_differential σ 2 (by decide))
    (dgLastHornKnownFace_differential σ 1 (by decide))
    (dgLastHornKnownFace_differential σ 0 (by decide))

end SerrePositivity.InfinityCategories
