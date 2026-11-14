module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedNormalizedBoundaryRhs

/-! # 指定最上位原始元による正規化した差の充填

概要：最上位比較の差を零面に置いた境界を、指定原始元の符号倍で充填する。
方針：実境界の全真部分集合の方程式と、最上位右辺の一項計算を接続する。
規約：最上位の次数を明示して cast を局所化する。使われ方：正次元の実相対比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D}

/-- 同じ最上位次数を別の整数で指定して充填する。 -/
def pinchedCompleteTopAtDegree {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n)
    (he : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      _root_.SerrePositivity.DifferentialGraded.differential A (f.component J k hJ hk) = f.rhs J k hk)
    (k : ℤ) (hk : k = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n) (h : GradedHom A x y k)
    (hh : differential A h = f.rhs Finset.univ k hk) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n := by
  subst hk
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedCompleteTop f he h hh

/-- 指定次数による最上位置換も、全真部分集合を厳密に保つ。 -/
lemma pinchedCompleteTopAtDegree_proper {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (he)
    (k : ℤ) (hk : k = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n) (h : GradedHom A x y k) (hh)
    (J : Finset (Fin (n + 1))) (l : ℤ) (hJ : J.Nonempty) (hl : l = 1 - (J.card : ℤ))
    (hne : J ≠ Finset.univ) :
    (pinchedCompleteTopAtDegree f he k hk h hh).val.component J l hJ hl =
      f.component J l hJ hl := by
  subst hk
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedCompleteTopData_proper f h J l hJ hl hne

/-- 指定次数での最上位成分は、指定原始元そのもの。 -/
lemma pinchedCompleteTopAtDegree_full {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (he)
    (k : ℤ) (hk : k = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n) (h : GradedHom A x y k) (hh) :
    (pinchedCompleteTopAtDegree f he k hk h hh).val.component Finset.univ k
      Finset.univ_nonempty hk = h := by
  subst hk
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedCompleteTopData_full f h

/-- 指定終次数への微分式を、同じ成分の通常の cochain 微分へ戻す。 -/
lemma pinchedPrimitive_component_differential {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n)
    (p q : ℤ) (hpq : p + 1 = q)
    (hq : q = 1 - ((Finset.univ : Finset (Fin (n + 1))).card : ℤ))
    (e : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y p)
    (he : (_root_.SerrePositivity.DifferentialGraded.homObject A D x y).d p q e = f.component Finset.univ q Finset.univ_nonempty hq) :
    _root_.SerrePositivity.DifferentialGraded.differential A e = f.component Finset.univ (p + 1) Finset.univ_nonempty (hpq.trans hq) := by
  subst hpq
  exact he

/-- 正規化した差の境界の右辺を指定原始元の符号倍で解く。 -/
lemma PinchedTopComparison.normalized_primitive_equation {n : ℕ}
    {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 1)} (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) :
    differential A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign (Finset.univ : Finset (Fin (n + 3))) 0 • c.primitive) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryKnownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedNormalizedBoundary (s - t) c.difference_proper_zero)).rhs
        Finset.univ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree (n + 1) - 1) (by simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree]; omega) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedNormalizedBoundary_rhs]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_units_smul]
  apply congrArg (fun a => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign (Finset.univ : Finset (Fin (n + 3))) 0 • a)
  exact pinchedPrimitive_component_differential (s - t).val
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree (n + 1) - 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree (n + 1)) (by omega) rfl c.primitive
      c.difference_full

/-- 指定原始元を使い、零面が差で他の面が零となる一段高い線形単体を作る。 -/
def PinchedTopComparison.normalizedFiller {n : ℕ} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 1)}
    (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 2) :=
  pinchedCompleteTopAtDegree
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryKnownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedNormalizedBoundary (s - t) c.difference_proper_zero))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryKnownData_equation _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree (n + 1) - 1)
    (by simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree]; omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign (Finset.univ : Finset (Fin (n + 3))) 0 • c.primitive)
    c.normalized_primitive_equation

end SerrePositivity.InfinityCategories.Project.DerivedCategories
