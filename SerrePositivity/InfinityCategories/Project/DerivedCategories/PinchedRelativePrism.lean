module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedNormalizedPrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedPointwiseAddition

/-! # 指定最上位比較から元の二単体の実相対ホモトピーへ

概要：差の境界上零の prism に第二単体を加え、境界を固定する実ホモトピーを作る。
方針：線形座標での加法、錐 prism の両端、境界上の消滅を接続する。
規約：正次元の二単体の比較を扱う。使われ方：Drinfeld 商の相対写像空間比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D}

/-- 第二単体を射影で引き戻し、正規化した差の prism を加える。 -/
def PinchedTopComparison.relativePrism {n : ℕ} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 1)}
    (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) :
    (Δ[n + 1] : SSet.{max u v}) ⊗ Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPointwiseAdd (fst _ _ ≫ SSet.yonedaEquiv.symm t.toPinched) c.normalizedPrism

/-- 相対 prism の零端は第二単体。 -/
lemma PinchedTopComparison.relativePrism_zero {n : ℕ} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 1)}
    (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) :
    SSet.ι₀ ≫ c.relativePrism = SSet.yonedaEquiv.symm t.toPinched := by
  rw [PinchedTopComparison.relativePrism, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPointwiseAdd_precomp,
    ← Category.assoc, SSet.ι₀_fst, Category.id_comp, c.normalizedPrism_zero,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedZeroSimplex_constant, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPointwiseAdd_zero]

/-- 相対 prism の一端は第一単体。 -/
lemma PinchedTopComparison.relativePrism_one {n : ℕ} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 1)}
    (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) :
    SSet.ι₁ ≫ c.relativePrism = SSet.yonedaEquiv.symm s.toPinched := by
  rw [PinchedTopComparison.relativePrism, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPointwiseAdd_precomp,
    ← Category.assoc, SSet.ι₁_fst, Category.id_comp, c.normalizedPrism_one,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPointwiseAdd_yoneda]
  have he : t + (s - t) = s := by abel
  rw [he]

/-- 相対 prism は元の全境界上で第二単体の定値ホモトピー。 -/
lemma PinchedTopComparison.relativePrism_boundary {n : ℕ}
    {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 1)} (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) :
    (∂Δ[n + 1]).ι ▷ Δ[1] ≫ c.relativePrism =
      fst _ _ ≫ (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm t.toPinched := by
  rw [PinchedTopComparison.relativePrism, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPointwiseAdd_precomp,
    c.normalizedPrism_boundary, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPointwiseAdd_zero]
  rfl

/-- 指定最上位比較から、元の二単体の間の実単体的ホモトピーを得る。 -/
def PinchedTopComparison.homotopy_positive {n : ℕ} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 1)}
    (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) :
    SSet.Homotopy (SSet.yonedaEquiv.symm t.toPinched) (SSet.yonedaEquiv.symm s.toPinched) where
  h := c.relativePrism
  h₀ := c.relativePrism_zero
  h₁ := c.relativePrism_one
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.2

/-- 構成した実ホモトピーは全境界上で厳密に定値。 -/
lemma PinchedTopComparison.homotopy_positive_boundary {n : ℕ}
    {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 1)} (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) :
    (∂Δ[n + 1]).ι ▷ Δ[1] ≫ c.homotopy_positive.h =
      fst _ _ ≫ (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm t.toPinched :=
  c.relativePrism_boundary

end SerrePositivity.InfinityCategories.Project.DerivedCategories
