module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedRelativeTopLifting

/-! # 指定された目標を持つ pinched 線形単体の充填

概要：既知境界を保ち、全射準同型な鎖写像で目標単体へ写る単体を作る。
方針：最上位成分だけを同時持ち上げの原始元へ置き換える。
規約：零次元も同じ構成。使われ方：β3 の写像空間の相対境界充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
variable [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] {x y : D} {x' y' : E}

/-- 全体集合の成分だけを指定した次数付きの族へ置き換える。 -/
def pinchedReplaceTopData {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n)
    (q : ∀ k : ℤ, k = 1 - ((Finset.univ : Finset (Fin (n + 1))).card : ℤ) →
      GradedHom A x y k) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n := fun t =>
  if h : t.val.1 = Finset.univ then q t.val.2 (by simpa only [h] using t.property.2) else f t

/-- 最上位の置換は真部分集合の成分を変えない。 -/
lemma pinchedReplaceTopData_proper {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (q)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hne : J ≠ Finset.univ) :
    (pinchedReplaceTopData f q).component J k hJ hk = f.component J k hJ hk := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, pinchedReplaceTopData, dite_eq_right hne]

/-- 最上位の置換は指定した成分を与える。 -/
lemma pinchedReplaceTopData_full {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (q)
    (k : ℤ) (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 1))).card : ℤ)) :
    (pinchedReplaceTopData f q).component Finset.univ k Finset.univ_nonempty hk = q k hk := by
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, pinchedReplaceTopData]

/-- 真部分集合を保ち、指定された目標単体へ写る線形単体が存在する。 -/
lemma pinchedLinear_relative_simplex_lift (φ : _root_.SerrePositivity.DifferentialGraded.homObject A D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject A E x' y')
    (hs : ∀ i : ℤ, Function.Surjective (φ.f i)) (hq : QuasiIso φ)
    {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n)
    (he : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      _root_.SerrePositivity.DifferentialGraded.differential A (f.component J k hJ hk) = f.rhs J k hk)
    (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x' y' n)
    (hm : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      φ.f k (f.component J k hJ hk) = g.val.component J k hJ hk) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n,
      (∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
        s.val.component J k hJ hk = f.component J k hJ hk) ∧
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap φ s = g := by
  let q := fun k hk => Classical.choose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinear_relative_top_lift φ hs hq f he g hm k hk)
  have hq' := fun k hk => Classical.choose_spec
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinear_relative_top_lift φ hs hq f he g hm k hk)
  let s := pinchedReplaceTopData f q
  have hproper := pinchedReplaceTopData_proper f q
  have hrhs : ∀ J k hk, s.rhs J k hk = f.rhs J k hk :=
    fun J k hk => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinched_rhs_eq_of_proper_components s f hproper J k hk
  have hmem : s ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearSubmodule A x y n := by
    intro J k hJ hk
    rw [hrhs]
    by_cases h : J = Finset.univ
    · subst J
      change _root_.SerrePositivity.DifferentialGraded.differential A ((pinchedReplaceTopData f q).component _ _ _ _) = _
      rw [pinchedReplaceTopData_full]
      exact (hq' k hk).1
    · rw [hproper J k hJ hk h]
      exact he J k hJ hk h
  refine ⟨⟨s, hmem⟩, hproper, ?_⟩
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change φ.f k (s.component J k hJ hk) = g.val.component J k hJ hk
  by_cases h : J = Finset.univ
  · subst J
    change φ.f k ((pinchedReplaceTopData f q).component _ _ _ _) = _
    rw [pinchedReplaceTopData_full]
    exact (hq' k hk).2
  · rw [hproper J k hJ hk h]
    exact hm J k hJ hk h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
