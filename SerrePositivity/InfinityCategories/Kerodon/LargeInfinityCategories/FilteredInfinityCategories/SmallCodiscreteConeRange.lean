module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.KappaSmallRange
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CodiscreteFreshCoconeMono
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallJoin

/-!
概要：ラベル付き積の小さい部分複体を、同じ積内の小さい錐の像へ拡大する。
方針：新しい頂点を持つ単射な錐の像を取り、錐の小ささを同型で移す。
規約：元の部分複体の包含と錐の写像をそのまま用いる。
使われ方：終頂点付き部分複体の族による cofinal poset の構成。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 元の部分複体を含む、同じ新頂点付き単射な錐の小さい像が存在する。 -/
lemma exists_small_codiscreteConeRange {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ C]
    {T : Type u} (hT : κ ≤ Cardinal.mk T)
    (A : (C ⊗ nerve (Codiscrete T)).Subcomplex) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ A.toSSet) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone A.ι, Mono d.val ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ (Subcomplex.range d.val).toSSet ∧
      A ≤ Subcomplex.range d.val ∧
      ∀ x : A.toSSet _⦋0⦌, A.ι.app _ x ≠ d.vertex := by
  obtain ⟨d, hd, hfresh⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_mono_fresh_codiscreteProductCocone hA hT A.ι
  let := hd
  have hcone : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A.toSSet Δ[0]) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_join hκ hA (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_of_finite hκ.aleph0_le _)
  refine ⟨d, hd, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isKappaSmall_range_of_mono d.val hcone, ?_, hfresh⟩
  have h := Subfunctor.range_comp_le (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A.toSSet Δ[0]) d.val
  rw [d.property, Subfunctor.range_ι] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
