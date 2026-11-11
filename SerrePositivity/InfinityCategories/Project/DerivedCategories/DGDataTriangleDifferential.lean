module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataLowDimensionalPullback
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-! # 指定実三角形からデータの三点微分式を回収する

概要：単射の制限が実三角形に一致するデータから、同じ辺成分の三点微分式を得る。
方針：対象と辺・三点成分の異種等式を、微分・合成・差の代数則で輸送する。
規約：符号は実三角形の微分式。使われ方：最後外ホーンの三つの既知面の残差計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 実三角形への制限から、元のデータの対応する三点微分方程式を回収する。 -/
lemma dgDataTriangle_differential {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2)
    (α : Fin 3 →o Fin (n + 1)) (hα : Function.Injective α)
    (h : s.pullback α = t.toSimplexData) (h₀₁ : α 0 < α 1) (h₁₂ : α 1 < α 2) :
    _root_.SerrePositivity.DifferentialGraded.differential A (s.tripleHom (α 0) (α 1) (α 2) h₀₁ h₁₂) =
      _root_.SerrePositivity.DifferentialGraded.compose A (s.edgeHom (α 1) (α 2) h₁₂) (s.edgeHom (α 0) (α 1) h₀₁) (by decide) -
        s.edgeHom (α 0) (α 2) (h₀₁.trans h₁₂) := by
  have hx : s.obj (α 0) = t.obj 0 := congrArg (fun d => d.obj 0) h
  have hy : s.obj (α 1) = t.obj 1 := congrArg (fun d => d.obj 1) h
  have hz : s.obj (α 2) = t.obj 2 := congrArg (fun d => d.obj 2) h
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom_heq_of_pullback_eq s t.toSimplexData α hα h
    0 1 2 (by decide) (by decide) h₀₁ h₁₂
  have htop : t.toSimplexData.tripleHom 0 1 2 (by decide) (by decide) = t.triangleHom := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.triangleHom
    congr 1
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq hx hz rfl _ _ (ht.trans (heq_of_eq htop))
  have h₀₁' := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq s t.toSimplexData α hα h
    0 1 (by decide) h₀₁
  have h₁₂' := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq s t.toSimplexData α hα h
    1 2 (by decide) h₁₂
  have h₀₂' := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq s t.toSimplexData α hα h
    0 2 (by decide) (h₀₁.trans h₁₂)
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq hx hy hz rfl rfl rfl _ _ _ _ h₁₂' h₀₁'
    (show (0 : ℤ) + 0 = 0 from by decide) (by decide)
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_sub_heq hx hz rfl _ _ _ _ hc h₀₂'
  exact eq_of_heq (hd.trans ((heq_of_eq t.differential_triangleHom).trans hr.symm))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
