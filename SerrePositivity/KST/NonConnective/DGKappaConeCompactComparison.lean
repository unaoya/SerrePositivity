module
public import SerrePositivity.KST.NonConnective.DGKappaPerfectInput
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Subcategory
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence

/-!
概要：同じ実 dg cone を、実導来加群 ∞ 圏の非可算 κ-compact 全部分圏へ同値に送る。
方針：I の全写像空間比較・κ-compact 性・全頂点回収を、そのまま全部分圏へ因子化する。
規約：通常 compact／Indω 比較で代用せず、元の実導来包含を厳密に保持する。
使われ方：K-7 d4 の非可算 κ 側の模型照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 元の実導来比較を、同じ実導来 ∞ 圏の κ-compact 部分へ因子化する。 -/
def dgKappaConeCompactComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGKappaCone R D I) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, max (u + 1) v} κ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, max (u + 1) v} κ)
    (dgKappaConeDerivedComparison R D I) (by
      intro x
      obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective x
      exact I.kappaCompact M.val M.property)

/-- 全部分圏の包含後は元の同じ実導来比較に厳密に戻る。 -/
theorem dgKappaConeCompactComparison_inclusion :
    dgKappaConeCompactComparison R D I ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, max (u + 1) v} κ
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) = dgKappaConeDerivedComparison R D I := rfl

/-- κ-compact 部分への実比較も全写像空間で充満忠実。 -/
theorem dgKappaConeCompactComparison_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (dgKappaConeCompactComparison R D I) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_comp_iff _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion_isFullyFaithful.{u, max (u + 1) v} κ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D))).mp
  rw [dgKappaConeCompactComparison_inclusion]
  exact I.derivedFullyFaithful

/-- 同じ I の全 κ-compact 頂点回収を、全部分圏内の指定頂点同型へ戻す。 -/
theorem dgKappaConeCompactComparison_isEssentiallySurjective :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (dgKappaConeCompactComparison R D I) := by
  intro y
  obtain ⟨M, hM, ⟨e⟩⟩ := I.covers y.val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex y)
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ⟨M, hM⟩, ⟨?_⟩⟩
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion_isFullyFaithful.{u, max (u + 1) v} κ
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)).preimageVertexIso e

/-- 同じ実 dg cone と実導来圏の非可算 κ-compact 部分との同値。 -/
def dgKappaConeCompactEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGKappaCone R D I))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, max (u + 1) v} κ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (dgKappaConeCompactComparison_isFullyFaithful R D I)
    (dgKappaConeCompactComparison_isEssentiallySurjective R D I)).choose

/-- 同値も元の実導来包含を順射として厳密に保持する。 -/
theorem dgKappaConeCompactEquivalence_inclusion :
    (dgKappaConeCompactEquivalence R D I).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, max (u + 1) v} κ
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) = dgKappaConeDerivedComparison R D I := rfl

end SerrePositivity.KST.NonConnective
