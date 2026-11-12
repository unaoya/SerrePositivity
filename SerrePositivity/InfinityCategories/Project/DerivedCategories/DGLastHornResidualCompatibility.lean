module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornFaceDifferentials

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 三つの三角形の微分式から、二未知式の既知残差の微分を計算する。 -/
lemma dgTriangleResidual_differential {x₀ x₁ x₂ x₃ : D}
    (f₀₁ : _root_.SerrePositivity.DifferentialGraded.GradedHom A x₀ x₁ 0) (f₀₂ : _root_.SerrePositivity.DifferentialGraded.GradedHom A x₀ x₂ 0)
    (f₀₃ : _root_.SerrePositivity.DifferentialGraded.GradedHom A x₀ x₃ 0) (f₁₂ : _root_.SerrePositivity.DifferentialGraded.GradedHom A x₁ x₂ 0)
    (f₁₃ : _root_.SerrePositivity.DifferentialGraded.GradedHom A x₁ x₃ 0) (f₂₃ : _root_.SerrePositivity.DifferentialGraded.GradedHom A x₂ x₃ 0)
    (h₀₁₃ h₀₂₃ : _root_.SerrePositivity.DifferentialGraded.GradedHom A x₀ x₃ (-1)) (h₁₂₃ : _root_.SerrePositivity.DifferentialGraded.GradedHom A x₁ x₃ (-1))
    (d₀₁ : _root_.SerrePositivity.DifferentialGraded.differential A f₀₁ = 0)
    (d₀₁₃ : _root_.SerrePositivity.DifferentialGraded.differential A h₀₁₃ = _root_.SerrePositivity.DifferentialGraded.compose A f₁₃ f₀₁ (by decide) - f₀₃)
    (d₀₂₃ : _root_.SerrePositivity.DifferentialGraded.differential A h₀₂₃ = _root_.SerrePositivity.DifferentialGraded.compose A f₂₃ f₀₂ (by decide) - f₀₃)
    (d₁₂₃ : _root_.SerrePositivity.DifferentialGraded.differential A h₁₂₃ = _root_.SerrePositivity.DifferentialGraded.compose A f₂₃ f₁₂ (by decide) - f₁₃) :
    _root_.SerrePositivity.DifferentialGraded.differential A (h₀₂₃ - _root_.SerrePositivity.DifferentialGraded.compose A h₁₂₃ f₀₁ (by decide) - h₀₁₃) =
      -_root_.SerrePositivity.DifferentialGraded.compose A f₂₃ (_root_.SerrePositivity.DifferentialGraded.compose A f₁₂ f₀₁ (by decide) - f₀₂) (by decide) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_sub, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_sub, differential_compose, d₀₁,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, add_zero, d₀₂₃, d₁₂₃, d₀₁₃, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_left,
    ← compose_assoc A f₀₁ f₁₂ f₂₃ (by decide), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right]
  abel

open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 実三次最後外ホーンの既知残差は、最後の閉辺と Q 側残差を微分で結ぶ。 -/
lemma dgLastHornTopResidual_differential
    (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    differential A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTopResidual σ) =
      -compose A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 2 3 (by decide))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingResidual σ) (by decide) := by
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ
  exact dgTriangleResidual_differential
    (s.edgeHom 0 1 (by decide)) (s.edgeHom 0 2 (by decide)) (s.edgeHom 0 3 (by decide))
    (s.edgeHom 1 2 (by decide)) (s.edgeHom 1 3 (by decide)) (s.edgeHom 2 3 (by decide))
    (s.tripleHom 0 1 3 (by decide) (by decide)) (s.tripleHom 0 2 3 (by decide) (by decide))
    (s.tripleHom 1 2 3 (by decide) (by decide)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFirstEdge_closed σ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornKnownFace_differential σ 2 (by decide))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornKnownFace_differential σ 1 (by decide))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornKnownFace_differential σ 0 (by decide))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
