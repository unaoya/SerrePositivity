module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFamilySaturation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.Accessible
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanDiagramColimitTransport

/-!
概要：同じ小さい族の同型飽和に値を持つ全表示を、小さい全部分模型へ移す。
方針：飽和との全同値の逆を全図式へ合成し、余極限を関手同型で輸送する。
規約：元の指定頂点は厳密に保持。図式は任意の小さい coherent な filtered 添字。
使われ方：濃度変更における小さい μ-compact 生成圏の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {X : SSet.{u + 1}} [Quasicategory X] (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps X)
  {T : Type u} (v : T → X _⦋0⦌)

/-- 同型飽和に値を持つ元の全表示を、同じ指定頂点の小さい全部分模型による表示へ移す。 -/
lemma generatorPresentation_of_familySaturation {κ : Cardinal.{u}} {K : SSet.{u}}
    [Quasicategory K] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ K]
    (G : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ X)
    (hG : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FamilySaturation v (G.app _ (ULift.up k)))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.HasKappaFilteredGeneratorPresentation κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelInclusion hX v) c.vertex := by
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FamilySaturation v) G (by rintro ⟨k⟩; exact hG k)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFamilySaturationEquivalence v hX
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown (H ≫ e.inv)
  have ha : (SSet.uliftFunctor.{u + 1, u}).map a = H ≫ e.inv := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown_lift _
  have hi : e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.familySaturationInclusion v = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelInclusion hX v :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFamilySaturationComparison_inclusion v hX
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map a ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelInclusion hX v) G := by
    rw [ha, ← hi, Category.assoc]
    simpa only [Category.assoc, Category.id_comp, H,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.familySaturationInclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι] using
      (e.invHomIso.precomp H).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.familySaturationInclusion v)
  obtain ⟨d, hd, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.exists_colimitCocone_functorIso_sameVertex he.symm c hc
  exact ⟨K, inferInstance, inferInstance, a, d, hv, hd⟩

/-- 元の小さい compact 族の表示があれば、小さい全部分模型が同じ濃度で compact 生成する。 -/
lemma smallFullModelInclusion_isKappaCompactGenerating {κ : Cardinal.{u}}
    (hv : ∀ t, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (v t))
    (hp : ∀ x : X _⦋0⦌, ∃ (K : SSet.{u}) (hK : Quasicategory K),
      letI := hK
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ K ∧ ∃ G : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ X,
        (∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FamilySaturation v (G.app _ (ULift.up k))) ∧
        ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ∧ c.vertex = x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelInclusion hX v) where
  fullyFaithful := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelInclusion_isFullyFaithful hX v
  compact a := by
    obtain ⟨t, ht⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelIso hX v).hom.app _ (ULift.up a))
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact κ
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelIso hX v).hom.app _ (ULift.up a)).val)
    rw [← ht]
    exact hv t
  presentation x := by
    obtain ⟨K, hK, hκK, G, hG, c, hc, hx⟩ := hp x
    have := hK
    have := hκK
    exact hx ▸ generatorPresentation_of_familySaturation hX v G hG c hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
