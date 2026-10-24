module

public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorCompositionTriangle
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalComposition
public import SerrePositivity.InfinityCategories.Derived.ConstantEdgeFamily
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorFamilyPrism

/-!
概要：選択済みの元の区間 Hom 前合成を、同じ三辺を持つ三角形の全族で表示する。
方針：元の h Fun での合成仕様から指定三辺の実際の三角形を回収する。
規約：選択済みの前合成写像と元の辺を保持し、別の合成代表へ置き換えない。
使われ方：Yoneda 評価と元の前合成族の全パラメータでの両立。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の区間族のホモトピーを prism に戻すと、同じ元の区間族を厳密に回収する。 -/
lemma intervalFamilyHomotopy_prism {K X : SSet.{u}} {a b : X _⦋0⦌}
    (t : K ⟶ intervalMappingSpace a b) :
    functorFamilyPrism (curry (intervalFamilyHomotopy t).h) = intervalMappingUncurry t := by
  rw [functorFamilyPrism, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨i, k⟩
  rfl

/-- 元の h Fun の合成等式を、同じ三つの元の区間族を持つ三角形の全族へ戻す。 -/
lemma intervalFamilyHom_triangle_exists {K X : SSet.{u}} [Quasicategory X]
    {a b c : X _⦋0⦌} (t₀₁ : K ⟶ intervalMappingSpace a b)
    (t₁₂ : K ⟶ intervalMappingSpace b c) (t₀₂ : K ⟶ intervalMappingSpace a c)
    (h : intervalFamilyHom t₀₁ ≫ intervalFamilyHom t₁₂ = intervalFamilyHom t₀₂) :
    ∃ H : (Δ[2] : SSet.{u}) ⊗ K ⟶ X,
      (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ H = intervalMappingUncurry t₀₁ ∧
      (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ H = intervalMappingUncurry t₁₂ ∧
      (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ H = intervalMappingUncurry t₀₂ := by
  obtain ⟨T⟩ := nonempty_functorCompositionTriangle_of_homEq
    (intervalFamilyHomotopy t₀₁) (intervalFamilyHomotopy t₁₂) (intervalFamilyHomotopy t₀₂) h
  refine ⟨functorFamilyPrism T.diagram, ?_, ?_, ?_⟩
  · rw [functorFamilyPrism_restrict, T.face_two, intervalFamilyHomotopy_prism]
  · rw [functorFamilyPrism_restrict, T.face_zero, intervalFamilyHomotopy_prism]
  · rw [functorFamilyPrism_restrict, T.face_one, intervalFamilyHomotopy_prism]

/-- 元の指定辺と選択済みの区間 Hom 前合成は、同じ三角形の全族を持つ。 -/
lemma intervalPrecompose_triangleFamily_exists {X : SSet.{u}} [Quasicategory X]
    {a b : X _⦋0⦌} (e : SSet.Edge a b) (c : X _⦋0⦌) :
    ∃ H : (Δ[2] : SSet.{u}) ⊗ intervalMappingSpace b c ⟶ X,
      (stdSimplex.δ (2 : Fin 3) ▷ intervalMappingSpace b c) ≫ H =
        intervalMappingUncurry (SSet.const (intervalMappingVertexOfEdge e)) ∧
      (stdSimplex.δ (0 : Fin 3) ▷ intervalMappingSpace b c) ≫ H =
        intervalMappingUncurry (𝟙 (intervalMappingSpace b c)) ∧
      (stdSimplex.δ (1 : Fin 3) ▷ intervalMappingSpace b c) ≫ H =
        intervalMappingUncurry (intervalPrecompose c
          (SSet.Truncated.HomotopyCategory.homMk e.toTruncated)) := by
  apply intervalFamilyHom_triangle_exists
  rw [intervalFamilyHom_const_edge]
  exact (intervalPrecompose_hom c (SSet.Truncated.HomotopyCategory.homMk e.toTruncated)).symm

end SerrePositivity.InfinityCategories.HomotopyLimits
