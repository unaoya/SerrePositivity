module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PartialColimitProperty
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CofinalPartialColimitFamilies

/-!
概要：指定した実部分余錐を持つ全族の値から、所属条件と保存関手像の compact 性を回収する。
方針：元の余極限の一意性と、小 poset 余極限の compact 閉性を使用する。
規約：族の各値を選び直さない。使われ方：二辺を揃えた三角形族の段階判定。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PartialFamilyValues

local instance : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩

/-- 実部分余極限の条件は、同じ実余錐を持つ全族の全頂点に移る。 -/
lemma partialFamily_values_property
    {μ : Cardinal.{u}} {J : Type u} [PartialOrder J]
    {C : SSet.{u + 1}} [Quasicategory C]
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ C}
    (W : C _⦋0⦌ → Prop) (hiso : ∀ {x y}, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y → (W x ↔ W y))
    {B : Type u} [Preorder B] (p : B → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve B) ⟶ C)
    (hF : ∀ b, ∃ a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredPartialDiagram D (p b)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone a ∧ a.vertex = F.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex b)))
    (hW : ∀ b, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HasPropertyPartialColimit W D (p b)) :
    ∀ k, W (F.app (Opposite.op ⦋0⦌) k) := by
  rintro ⟨k⟩
  obtain ⟨b, rfl⟩ := nerveEquiv.symm.surjective k
  obtain ⟨a, ha, hWa⟩ := hW b
  obtain ⟨c, hc, hv⟩ := hF b
  have hm := (hiso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso a c ha hc)).mp hWa
  rwa [hv] at hm

/-- 保存関手の像で compact な元の段は、全小部分余極限族の各値の像でも compact。 -/
lemma partialFamily_mapped_values_compact
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {J : Type u} [PartialOrder J]
    {T C : SSet.{u + 1}} [Quasicategory T] [Quasicategory C]
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ T}
    (H : T ⟶ C) (hH : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits H)
    (hD : ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((D ≫ H).app _ k))
    {B : Type u} [Preorder B] (p : B → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve B) ⟶ T)
    (hF : ∀ b, ∃ a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredPartialDiagram D (p b)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone a ∧ a.vertex = F.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex b))) :
    ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((F ≫ H).app (Opposite.op ⦋0⦌) k) := by
  rintro ⟨k⟩
  obtain ⟨b, rfl⟩ := nerveEquiv.symm.surjective k
  obtain ⟨a, ha, hv⟩ := hF b
  have hm := hH (nerve (p b).val) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredPartialDiagram D (p b)) a ha
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_smallPosetColimit_universe hμ (p b).val (p b).property.2
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone H a) hm (fun k ↦ hD
      (((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion (p b).val))).app _ k))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex, hv] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PartialFamilyValues
