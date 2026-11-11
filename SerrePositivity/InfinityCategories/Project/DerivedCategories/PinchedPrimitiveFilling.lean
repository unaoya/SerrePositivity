module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedProperEquations

/-! # 原始元作用素による pinched 線形境界の充填

概要：真部分集合の全成分を保ち、最上位を削除和の原始元に置き換えて解を作る。
方針：削除右辺は真部分集合だけに依存し、閉性は境界の方程式から従う。
規約：原始元作用素の正しさを明示して適用する。使われ方：β3 の収縮 Hom の境界充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D}

/-- 最上位成分を右辺の原始元へ置き換える線形データ。 -/
def pinchedPrimitiveFillerData {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n)
    (p : ∀ k : ℤ, _root_.SerrePositivity.DifferentialGraded.GradedHom A x y (k + 1) → _root_.SerrePositivity.DifferentialGraded.GradedHom A x y k) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n := fun t =>
  if t.val.1 = Finset.univ then p t.val.2 (f.rhs t.val.1 t.val.2 t.property.2) else f t

/-- 真部分集合の成分は原始元による置換で変わらない。 -/
lemma pinchedPrimitiveFillerData_proper {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (p)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hne : J ≠ Finset.univ) :
    (pinchedPrimitiveFillerData f p).component J k hJ hk = f.component J k hJ hk := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, pinchedPrimitiveFillerData, ite_eq_right hne]

/-- 最上位の成分は右辺の指定原始元。 -/
lemma pinchedPrimitiveFillerData_full {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (p)
    (k : ℤ) (hJ : (Finset.univ : Finset (Fin (n + 1))).Nonempty)
    (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 1))).card : ℤ)) :
    (pinchedPrimitiveFillerData f p).component Finset.univ k hJ hk =
      p k (f.rhs Finset.univ k hk) := by
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, pinchedPrimitiveFillerData]

/-- 最上位の置換は全ての削除右辺を変えない。 -/
lemma pinchedPrimitiveFillerData_rhs {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (p)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    (pinchedPrimitiveFillerData f p).rhs J k hk = f.rhs J k hk :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinched_rhs_eq_of_proper_components _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrimitiveFillerData_proper f p) J k hk

/-- 正しい原始元作用素があれば、全境界の方程式を満たすデータは全体に延長する。 -/
lemma pinchedPrimitiveFillerData_mem {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n)
    (he : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      _root_.SerrePositivity.DifferentialGraded.differential A (f.component J k hJ hk) = f.rhs J k hk)
    (p : ∀ k : ℤ, _root_.SerrePositivity.DifferentialGraded.GradedHom A x y (k + 1) → _root_.SerrePositivity.DifferentialGraded.GradedHom A x y k)
    (hp : ∀ k a, _root_.SerrePositivity.DifferentialGraded.differential A a = 0 → _root_.SerrePositivity.DifferentialGraded.differential A (p k a) = a) :
    pinchedPrimitiveFillerData f p ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearSubmodule A x y n := by
  intro J k hJ hk
  rw [pinchedPrimitiveFillerData_rhs]
  by_cases hfull : J = Finset.univ
  · subst J
    rw [pinchedPrimitiveFillerData_full]
    exact hp _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinched_rhs_closed_of_proper_equations f he _ _ hk)
  · rw [pinchedPrimitiveFillerData_proper f p J k hJ hk hfull]
    exact he J k hJ hk hfull

/-- 境界を保った原始元による実際の線形単体。 -/
def pinchedPrimitiveFiller {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n)
    (he : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      _root_.SerrePositivity.DifferentialGraded.differential A (f.component J k hJ hk) = f.rhs J k hk)
    (p : ∀ k : ℤ, _root_.SerrePositivity.DifferentialGraded.GradedHom A x y (k + 1) → _root_.SerrePositivity.DifferentialGraded.GradedHom A x y k)
    (hp : ∀ k a, _root_.SerrePositivity.DifferentialGraded.differential A a = 0 → _root_.SerrePositivity.DifferentialGraded.differential A (p k a) = a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n :=
  ⟨pinchedPrimitiveFillerData f p, pinchedPrimitiveFillerData_mem f he p hp⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
