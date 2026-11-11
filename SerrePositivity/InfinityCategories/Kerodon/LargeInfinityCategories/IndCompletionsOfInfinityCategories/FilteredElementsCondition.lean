module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FilteredElementsMembership
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningFunctorIso
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafRestrictionEquivalence

/-!
概要：元の前層の元の圏が κ-filtered であるという頂点条件を定め、前層内の同型閉性を示す。
方針：既存の前層対象の全単射と、小さい unstraightening の関手同型不変性を使う。
規約：κ-filtered 性は F2N-1 の定義を使い、同値性を追加仮定にしない。
使われ方：HTT 5.3.5.4 の最小閉包から右 fibration 条件への方向。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 同じ前層頂点の元の right unstraightening の元の圏が κ-filtered であること。 -/
def HasKappaFilteredElements (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).symm v))

/-- 元の関手で指定した前層では、同じ元の圏に対する元の κ-filtered 条件そのもの。 -/
lemma hasKappaFilteredElements_functorVertex (κ : Cardinal.{u}) {C : SSet.{u}}
    [Quasicategory C] (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    HasKappaFilteredElements κ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening F) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C) F))) ↔ _
  rw [Equiv.symm_apply_apply]

/-- 同じ元の圏の κ-filtered 性は、同じ最小 κ-filtered 閉包への所属を与える。 -/
lemma isIndVertex_of_hasKappaFilteredElements (κ : Cardinal.{u}) {C : SSet.{u}}
    [Quasicategory C] {v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌} (hv : HasKappaFilteredElements κ v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C v := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_of_kappaFiltered_elements κ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).symm v) hv
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).symm v)) at h
  simpa only [Equiv.apply_symm_apply] using h

/-- 同じ元の圏の κ-filtered 性は、元の前層 ∞ 圏内の任意の同型で閉じている。 -/
lemma hasKappaFilteredElements_isoClosed (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIsoClosed (HasKappaFilteredElements κ (C := C)) := by
  intro v w e hv
  let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).symm v
  let G := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).symm w
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = v := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).apply_symm_apply v
  have hG : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G = w := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).apply_symm_apply w
  have η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G := eqToIso (congrArg HomotopyCategory.mk hF) ≪≫ e ≪≫
    eqToIso (congrArg HomotopyCategory.mk hG.symm)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_iff_of_equivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.oppositeQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningEquivalenceOfFunctorIso η))).mp hv

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
