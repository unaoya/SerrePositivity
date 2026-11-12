module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.NativeCosliceCoconeRetract

/-!
概要：κ-compact な元の指定余極限頂点は、元の小さい κ-filtered 図式の一つの項の retract。
方針：元の全 Hom の余極限保存を同じ coslice 表現へ移し、恒等点の実因子化を適用する。
規約：元の余錐頂点と元の項を保持。通常の図式や Hom 集合の余極限で代用しない。
使われ方：Indκ 内の compact 対象を元の Yoneda 像の retract として回収する。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の compact な余極限頂点は、同じ元の κ-filtered 図式の一つの元の項の retract。 -/
lemma IsKappaCompact.retract_of_colimit {κ : Cardinal.{u}}
    {C : SSet.{max u v}} [Quasicategory C] {I : SSet.{u}}
    [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ I]
    (D : (SSet.uliftFunctor.{v, u}).obj I ⟶ C) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} κ c.vertex) :
    ∃ i : I _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf c.vertex (D.app (Opposite.op ⦋0⦌) (ULift.up i)) := by
  have hR := h.nativeCoslice_preserves I D c hc
  obtain ⟨i, hi⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.nativeCosliceCocone_retract D c hR
  exact ⟨i.down, hi⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsKappaCompact (retract_of_colimit)


end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
