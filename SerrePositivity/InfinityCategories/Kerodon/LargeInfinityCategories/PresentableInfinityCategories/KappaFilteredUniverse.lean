module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallShapeSimplices
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FilteredUniverse
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.KappaSmallRange

/-!
概要：正則 κ に対する κ-small 性と κ-filtered 性の任意の宇宙持ち上げ。
方針：非退化単体の全単射と各次数の小ささで試験形状を縮小し、元の全余錐を持ち上げる。
規約：κ 自身を同じ Cardinal.lift で持ち上げる。任意の coherent な試験図式を扱う。
使われ方：大きい標的の Hom 錐族へ、同じ μ-filtered 添字を渡す。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 全非退化単体の小ささは、同じ濃度を持ち上げたときに保存・反映される。 -/
lemma isKappaSmall_ulift_iff (κ : Cardinal.{u}) (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall (Cardinal.lift.{v} κ) ((SSet.uliftFunctor.{v, u}).obj K) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ K := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall
  rw [← hasCardinalLT_iff_cardinal_mk_lt, hasCardinalLT_lift_iff,
    hasCardinalLT_iff_of_equiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.uliftNondegenerateEquiv.{u, v} K) κ,
    hasCardinalLT_iff_cardinal_mk_lt]

/-- 持ち上げた上限未満の形状の各次数は、元の小さい宇宙に収まる。 -/
lemma small_simplices_of_isKappaSmall_lift {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {K : SSet.{max u v}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall (Cardinal.lift.{v} κ) K)
    (n : SimplexCategoryᵒᵖ) : Small.{u} (K.obj n) := by
  have : Fact (Cardinal.lift.{v} κ).IsRegular := ⟨(Fact.out : κ.IsRegular).lift⟩
  exact ((hasCardinalLT_lift_iff _ κ).mp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_simplices_of_isKappaSmall hK n.unop.len)).small

/-- 縮小した同じ形状は、元の上限に関して κ-small。 -/
lemma smallSimplicialSet_isKappaSmall {κ : Cardinal.{u}}
    (K : SSet.{max u v}) [∀ n, Small.{u} (K.obj n)]
    (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall (Cardinal.lift.{v} κ) K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSet.{u, v} K) := by
  apply (isKappaSmall_ulift_iff.{u, v} κ _).mp
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isKappaSmall_iff_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso.{u, v} K)).mpr hK

/-- 元の κ-filtered ∞ 圏の持ち上げは、持ち上げた正則濃度に対して同じ全試験余錐を持つ。 -/
lemma isKappaFiltered_ulift {κ : Cardinal.{u}} [Fact κ.IsRegular]
    (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered (Cardinal.lift.{v} κ) ((SSet.uliftFunctor.{v, u}).obj C) := by
  constructor
  intro K hK f
  have (n : SimplexCategoryᵒᵖ) : Small.{u} (K.obj n) :=
    small_simplices_of_isKappaSmall_lift hK n
  let A := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSet.{u, v} K
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso.{u, v} K
  have hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ A := smallSimplicialSet_isKappaSmall K hK
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown (e.hom ≫ f)
  obtain ⟨c⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered.cocone_nonempty hA g
  have hg : (SSet.uliftFunctor.{v, u}).map g = e.hom ≫ f := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown_lift _
  have h : e.inv ≫ (SSet.uliftFunctor.{v, u}).map g = f := by
    rw [hg, Iso.inv_hom_id_assoc]
  exact ⟨h ▸ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u, v} c).restrict e.inv⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
