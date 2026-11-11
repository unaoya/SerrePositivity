module
public import SerrePositivity.KST.NonConnective.DGKappaPerfectInput
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Subcategory
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful

/-!
概要：固定 dg cone と、元の導来 ∞ 圏の κ-compact 全部分圏との比較同値。
方針：同じ導来比較を compact 部分へ因子化し、全 Hom の充満忠実性と covers を使う。
規約：対象別の比較であり、入力 dg 圏を動かす関手性は主張しない。
使われ方：新 sphere-closure 入力の B1、および後続の ω-Ind 比較への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 固定 cone の導来比較を、同じ実導来圏の κ-compact 部分へ因子化する。 -/
def dgKappaConeCompactComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGKappaCone R D I) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, max (u + 1) v} κ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (dgKappaConeDerivedComparison R D I) (by
    intro x
    obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective x
    exact I.kappaCompact M.val M.property)

/-- 全部分包含後は、元の導来比較を全単体で厳密に回収する。 -/
lemma dgKappaConeCompactComparison_inclusion :
    dgKappaConeCompactComparison R D I ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, max (u + 1) v} κ
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) = dgKappaConeDerivedComparison R D I :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

lemma dgKappaConeCompactComparison_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (dgKappaConeCompactComparison R D I) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion_isFullyFaithful.{u, max (u + 1) v} κ
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)).cancel_right
  rw [dgKappaConeCompactComparison_inclusion]
  exact I.derivedFullyFaithful

/-- 元の全 compact 頂点の covers を、同じ全部分圏内の可逆比較へ戻す。 -/
lemma dgKappaConeCompactComparison_isEssentiallySurjective :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (dgKappaConeCompactComparison R D I) := by
  intro y
  obtain ⟨M, hM, ⟨e⟩⟩ := I.covers y.val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex y)
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨M, hM⟩ : DGKappaCone R D I), ⟨?_⟩⟩
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion_isFullyFaithful.{u, max (u + 1) v} κ
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)).preimageVertexIso
  exact e

/-- compact 性・全写像空間の比較・covers から得る対象別の比較同値。 -/
lemma dgKappaConeCompactComparison_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (dgKappaConeCompactComparison R D I) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (dgKappaConeCompactComparison_isFullyFaithful R D I)
    (dgKappaConeCompactComparison_isEssentiallySurjective R D I)

/-- 順方向を固定した、cone と元の導来圏の κ-compact 部分との実同値。 -/
def dgKappaConeCompactEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGKappaCone R D I))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, max (u + 1) v} κ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)) :=
  (dgKappaConeCompactComparison_isQCatEquivalence R D I).choose

lemma dgKappaConeCompactEquivalence_hom :
    (dgKappaConeCompactEquivalence R D I).hom = dgKappaConeCompactComparison R D I := rfl

/-- 選んだ逆比較を元の導来比較で評価すると、同じ compact 包含を回収する。 -/
def dgKappaConeCompactEquivalence_inverse_inclusion :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((dgKappaConeCompactEquivalence R D I).inv ≫
      dgKappaConeDerivedComparison R D I)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, max (u + 1) v} κ
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)) := by
  have h := (dgKappaConeCompactEquivalence R D I).invHomIso.postcomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, max (u + 1) v} κ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D))
  simpa only [Category.assoc, dgKappaConeCompactEquivalence_hom,
    dgKappaConeCompactComparison_inclusion, Category.id_comp] using h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
