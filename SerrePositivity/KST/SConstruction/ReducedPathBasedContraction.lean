module
public import SerrePositivity.KST.SConstruction.ReducedPathContraction
public import SerrePositivity.KST.Spectra.PathContractibility

/-! # 元の点つき経路商の基点に相対な収縮
概要：元の商の収縮を、基点生成部分複体に相対な実際のホモトピーとして表す。
方針：基点固定の式を単体集合の相対ホモトピーの条件へ移す。
規約：Kan 性を要求しない。使われ方：零行上の基点固定 loop 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

/-- 元の点つき経路商の収縮は、基点生成部分複体に相対な実際のホモトピー。 -/
def reducedPathDiagonalBasedContraction (D : SimplicialObject SSet.{u}) :
    (RelativeMorphism.const : RelativeMorphism
      (.ofSimplex (reducedPathDiagonal D).basepoint) (.ofSimplex (reducedPathDiagonal D).basepoint)
        (SSet.const ⟨(reducedPathDiagonal D).basepoint,
          Subcomplex.mem_ofSimplex_obj (reducedPathDiagonal D).basepoint⟩)).Homotopy
      (RelativeMorphism.ofSimplex₀ (𝟙 (reducedPathDiagonal D).right)
        (reducedPathDiagonal D).basepoint (reducedPathDiagonal D).basepoint rfl) where
  h := reducedPathDiagonalCylinder D
  h₀ := (reducedPathDiagonalCylinder_zero D).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const _ _)
  h₁ := reducedPathDiagonalCylinder_one D
  rel := by
    rw [Subcomplex.ofSimplex_ι, ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const (reducedPathDiagonal D),
      comp_whiskerRight_assoc, reducedPathDiagonalCylinder_point, comp_toUnit_assoc]
    simp only [comp_toUnit_assoc]

end SerrePositivity.KST.SConstruction
