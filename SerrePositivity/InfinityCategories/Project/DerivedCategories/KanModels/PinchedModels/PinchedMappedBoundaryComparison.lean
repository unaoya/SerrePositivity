module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientPinchedBoundaryFillers

/-! # 共通分母による充填の商像と指定単体の比較

概要：全真部分集合での一致を商の線形単体の一致へ移し、差を最上位に集中させる。
方針：前合成の dg 関手自然性を各成分に適用する。
規約：元の指定単体を固定する。使われ方：最上位原始元からの実相対ホモトピー。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D E : Type v}
variable [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [Small.{u} E]

/-- 前合成した境界を保つ元の充填と指定目標の前合成は、像の全真部分集合で一致。 -/
lemma pinchedMappedBoundaryComparison_proper (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) {q x y : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A (F.obj x) (F.obj y) n)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A q y n)
    (ht : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      t.val.component J k hJ hk = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k (f.component J k hJ hk) s)
    (hm : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      (F.map x y).f k (f.component J k hJ hk) = g.val.component J k hJ hk) :
    ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (F.map q y) t).val.component J k hJ hk =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A E (F.onClosed.map s)) g).val.component
          J k hJ hk := by
  intro J k hJ hk hne
  change (F.map q y).f k (t.val.component J k hJ hk) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A E (F.onClosed.map s)).f k (g.val.component J k hJ hk)
  rw [ht J k hJ hk hne, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_f, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorGradedPrecompose_map,
    hm J k hJ hk hne]

/-- 全真部分集合で一致する二つの線形単体の差は、その成分が全て零。 -/
lemma pinchedLinearSimplex_sub_proper_zero {x y : D} {n : ℕ}
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n)
    (hp : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      s.val.component J k hJ hk = t.val.component J k hJ hk) :
    ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      (s - t).val.component J k hJ hk = 0 := by
  intro J k hJ hk hne
  change s.val.component J k hJ hk - t.val.component J k hJ hk = 0
  exact sub_eq_zero.mpr (hp J k hJ hk hne)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
