module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedRelativeSimplexLifting

/-! # Pinched 境界の指定原始元による最上位充填

概要：全真部分集合の成分を保ち、最上位の指定原始元だけで実際の線形単体を構成する。
方針：最上位置換の右辺の独立性と、境界の削除方程式を使う。
規約：零次元を含めて一様。使われ方：商の相対分母による線形境界の充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded

/-- n 次元 pinched 線形単体の最上位成分の整数次数。 -/
abbrev pinchedTopDegree (n : ℕ) : ℤ :=
  1 - ((Finset.univ : Finset (Fin (n + 1))).card : ℤ)

variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D}

/-- 最上位だけを指定原始元で置き換えた境界データ。 -/
def pinchedCompleteTopData {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n)
    (h : GradedHom A x y (pinchedTopDegree n)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedReplaceTopData f (fun k hk => by subst k; exact h)

/-- 全真部分集合の成分は厳密にそのまま。 -/
lemma pinchedCompleteTopData_proper {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (h)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hne : J ≠ Finset.univ) :
    (pinchedCompleteTopData f h).component J k hJ hk = f.component J k hJ hk :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedReplaceTopData_proper f _ J k hJ hk hne

/-- 最上位成分は指定された原始元。 -/
lemma pinchedCompleteTopData_full {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (h) :
    (pinchedCompleteTopData f h).component Finset.univ (pinchedTopDegree n)
      Finset.univ_nonempty rfl = h := by
  rw [pinchedCompleteTopData, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedReplaceTopData_full]

/-- 最上位の置換は削除右辺を全て保つ。 -/
lemma pinchedCompleteTopData_rhs {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (h)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    (pinchedCompleteTopData f h).rhs J k hk = f.rhs J k hk :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinched_rhs_eq_of_proper_components _ _ (pinchedCompleteTopData_proper f h) J k hk

/-- 最上位の原始元と全真部分集合の方程式から、実際の線形単体を得る。 -/
def pinchedCompleteTop {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n)
    (he : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      _root_.SerrePositivity.DifferentialGraded.differential A (f.component J k hJ hk) = f.rhs J k hk)
    (h : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y (pinchedTopDegree n))
    (hh : _root_.SerrePositivity.DifferentialGraded.differential A h = f.rhs Finset.univ (pinchedTopDegree n) rfl) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n :=
  ⟨pinchedCompleteTopData f h, by
    intro J k hJ hk
    rw [pinchedCompleteTopData_rhs]
    by_cases hfull : J = Finset.univ
    · subst J
      subst k
      rw [pinchedCompleteTopData_full]
      exact hh
    · rw [pinchedCompleteTopData_proper f h J k hJ hk hfull]
      exact he J k hJ hk hfull⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
