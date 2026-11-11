module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.CompositionTriangleComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilySquareInverse

/-!
概要：合成三角形の相対比較を、端点固定の写像空間の族のホモトピーへ移す。
方針：固定頂点の条件を正方形の両側辺の条件へ変え、正方形の厳密な逆表示を使う。
規約：元の相対比較の正方形を保持し、Hom の等式から path を選び直さない。
使われ方：B1 の comma 比較の coherence を保った構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：二辺を共有する合成三角形の対角の族は、指定比較に沿ってホモトピック。
方針：三角形の相対ホモトピーの端点固定条件を、族のホモトピーへ転置する。
規約：両端の関手は定値、パラメータは任意の単体集合。
使われ方：元の三角形から写像空間での実際の経路を得る。 -/
noncomputable def FunctorCompositionTriangle.familyHomotopy
    {A X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌} {V : A ⟶ X}
    {l : SSet.Homotopy (SSet.const x) V} {r : SSet.Homotopy V (SSet.const y)}
    {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y}
    (T₀ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f))
    (T₁ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy g)) : SSet.Homotopy f g := by
  let H := T₀.diagonalHomotopy T₁
  let e : (Δ[1] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) ⊗ Δ[1] :=
    lift (stdSimplex.isTerminalObj₀.from Δ[1]) (𝟙 _)
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ H.h =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : A ⟶ X)) := by
    have hv : e ≫
        (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    have h := congrArg (fun f ↦ e ≫ f)
      (T₀.diagonalHomotopy_source T₁)
    simp only [← Category.assoc] at h
    rw [hv] at h
    simpa only [Category.assoc, SSet.comp_const] using h
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ H.h =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y : A ⟶ X)) := by
    have hv : e ≫
        (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    have h := congrArg (fun f ↦ e ≫ f)
      (T₀.diagonalHomotopy_target T₁)
    simp only [← Category.assoc] at h
    rw [hv] at h
    simpa only [Category.assoc, SSet.comp_const] using h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyHomotopyOfSquare H.h H.h₀ H.h₁ hl hr

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
