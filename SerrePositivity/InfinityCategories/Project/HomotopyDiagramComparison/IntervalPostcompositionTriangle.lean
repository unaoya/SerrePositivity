module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.IntervalPrecompositionTriangle

/-!
概要：元の区間 Hom の後合成を、指定三辺の三角形族で表示する。
方針：元の h Fun での後合成仕様を既存の三角形回収へ渡す。
規約：選択済み後合成射を別の代表へ取り替えない。
使われ方：G14 の Yoneda 評価の標的自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 指定辺による元の後合成は、同じ三辺を持つ全パラメータの三角形で表せる。 -/
lemma intervalPostcompose_triangleFamily_exists {X : SSet.{u}} [Quasicategory X]
    (a : X _⦋0⦌) {b c : X _⦋0⦌} (e : SSet.Edge b c) :
    ∃ H : (Δ[2] : SSet.{u}) ⊗ intervalMappingSpace a b ⟶ X,
      (stdSimplex.δ (2 : Fin 3) ▷ intervalMappingSpace a b) ≫ H =
        intervalMappingUncurry (𝟙 (intervalMappingSpace a b)) ∧
      (stdSimplex.δ (0 : Fin 3) ▷ intervalMappingSpace a b) ≫ H =
        intervalMappingUncurry (SSet.const (intervalMappingVertexOfEdge e)) ∧
      (stdSimplex.δ (1 : Fin 3) ▷ intervalMappingSpace a b) ≫ H =
        intervalMappingUncurry (intervalPostcompose a
          (SSet.Truncated.HomotopyCategory.homMk e.toTruncated)) := by
  apply intervalFamilyHom_triangle_exists
  rw [intervalFamilyHom_const_edge]
  exact (intervalPostcompose_hom a
    (SSet.Truncated.HomotopyCategory.homMk e.toTruncated)).symm

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
