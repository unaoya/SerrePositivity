module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-!
概要：三つの実際の円柱を面に持つ全 Hom の三角形から、辺の類の合成等式を得る。
方針：同じ三角形の族を curry し、指定した三つの円柱の関手辺の合成三角形と読む。
規約：代表の選び直しはしない。三つの raw な面をそのまま使う。
使われ方：評価固定三角形を共通 path end における比較の辺の整合性へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {T X : SSet.{u}} {f g h : T ⟶ X}
  (H₀ : SSet.Homotopy f g) (H₁ : SSet.Homotopy g h) (H₂ : SSet.Homotopy f h)
  (F : T ⊗ (Δ[2] : SSet.{u}) ⟶ X)
  (h₀ : (T ◁ stdSimplex.δ (2 : Fin 3)) ≫ F = H₀.h)
  (h₁ : (T ◁ stdSimplex.δ (0 : Fin 3)) ≫ F = H₁.h)
  (h₂ : (T ◁ stdSimplex.δ (1 : Fin 3)) ≫ F = H₂.h)

/-- 同じ全 Hom の三角形を、三つの指定円柱の実際の関手辺の合成三角形として読む。 -/
def homotopyTriangleCompStruct : SSet.Truncated.Edge.CompStruct
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H₁)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H₂) where
  simplex := SSet.yonedaEquiv (curry F)
  d₂ := by
    change ((ihom T).obj X).δ 2 (SSet.yonedaEquiv (curry F)) = SSet.yonedaEquiv (curry H₀.h)
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    apply congrArg SSet.yonedaEquiv
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry]
    exact h₀
  d₀ := by
    change ((ihom T).obj X).δ 0 (SSet.yonedaEquiv (curry F)) = SSet.yonedaEquiv (curry H₁.h)
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    apply congrArg SSet.yonedaEquiv
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry]
    exact h₁
  d₁ := by
    change ((ihom T).obj X).δ 1 (SSet.yonedaEquiv (curry F)) = SSet.yonedaEquiv (curry H₂.h)
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    apply congrArg SSet.yonedaEquiv
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry]
    exact h₂

include F h₀ h₁ h₂ in
/-- 三角形を成す三つの実際の円柱の辺の類は、指定した順に合成する。 -/
lemma homotopyTriangle_homMk_comp [Quasicategory X] :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H₀) ≫
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H₁) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H₂) :=
  SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (homotopyTriangleCompStruct H₀ H₁ H₂ F h₀ h₁ h₂)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
