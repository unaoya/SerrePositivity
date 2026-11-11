module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedRelativePrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedLinearBoundaryEdgeEndpoints

/-! # 全次元の指定最上位比較の実相対ホモトピー

概要：全真部分集合の一致と指定最上位原始元から、全境界を固定する実ホモトピーを得る。
方針：零次元の指定原始元辺と、正次元の錐 prism を組み合わせる。
規約：始点は第二単体、終点は第一単体。使われ方：商の全次元相対写像空間比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 指定最上位比較から、零次元も含む実単体的ホモトピーを得る。 -/
def PinchedTopComparison.homotopy {n : ℕ} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n}
    (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) :
    SSet.Homotopy (SSet.yonedaEquiv.symm t.toPinched) (SSet.yonedaEquiv.symm s.toPinched) := by
  cases n with
  | zero => exact c.homotopy_zero
  | succ n => exact c.homotopy_positive

/-- 全次元で構成した実ホモトピーは、標準単体の全境界上で厳密に定値。 -/
lemma PinchedTopComparison.homotopy_boundary {n : ℕ} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n}
    (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) :
    (∂Δ[n]).ι ▷ Δ[1] ≫ c.homotopy.h =
      fst _ _ ≫ (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm t.toPinched := by
  cases n with
  | zero =>
    rw [SSet.boundary_zero]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.2
  | succ n => exact c.homotopy_positive_boundary

/-- 実単体的ホモトピーと、その全境界上の厳密な定値性を同時に保持する。 -/
structure PinchedRelativeHomotopy {n : ℕ} (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n) where
  homotopy : SSet.Homotopy (SSet.yonedaEquiv.symm t.toPinched) (SSet.yonedaEquiv.symm s.toPinched)
  boundary : (∂Δ[n]).ι ▷ Δ[1] ≫ homotopy.h =
    fst _ _ ≫ (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm t.toPinched

/-- 指定最上位比較から、全境界を固定する実ホモトピーとその定値性を得る。 -/
def PinchedTopComparison.relativeHomotopy {n : ℕ} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n}
    (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) : PinchedRelativeHomotopy s t :=
  ⟨c.homotopy, c.homotopy_boundary⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
