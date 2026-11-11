module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedMappedBoundaryComparison

/-! # 境界を固定する pinched 線形単体の最上位比較

概要：全真部分集合の一致と、最上位の差の指定原始元を一つの構造にまとめる。
方針：差は全真部分集合で零であり、最上位は指定された微分である。
規約：実相対ホモトピーの存在とは区別する。使われ方：商の充填の比較の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D}

/-- 同じ境界を持つ二つの線形単体の、最上位の差の指定原始元。 -/
structure PinchedTopComparison {n : ℕ} (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n) where
  proper : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
    s.val.component J k hJ hk = t.val.component J k hJ hk
  primitive : GradedHom A x y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n - 1)
  differential_primitive : (_root_.SerrePositivity.DifferentialGraded.homObject A D x y).d
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n - 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n) primitive =
    s.val.component Finset.univ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n) Finset.univ_nonempty rfl -
      t.val.component Finset.univ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n) Finset.univ_nonempty rfl

/-- 最上位比較の差は全真部分集合で零。 -/
lemma PinchedTopComparison.difference_proper_zero {n : ℕ} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n}
    (c : PinchedTopComparison s t) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) (hne : J ≠ Finset.univ) :
    (s - t).val.component J k hJ hk = 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplex_sub_proper_zero s t c.proper J k hJ hk hne

/-- 最上位比較は差を取った線形単体の最上位成分を指定通りに微分する。 -/
lemma PinchedTopComparison.difference_full {n : ℕ} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n}
    (c : PinchedTopComparison s t) :
    (homObject A D x y).d (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n - 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n) c.primitive =
      (s - t).val.component Finset.univ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n) Finset.univ_nonempty rfl :=
  c.differential_primitive

end SerrePositivity.InfinityCategories.Project.DerivedCategories
