module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.SmallSubcomplexCovers

/-!
概要：正則 κ に関して κ 個未満の κ-small な部分複体の和は κ-small。
方針：同じ和の非退化単体を、各部分複体の非退化単体の直和から覆う。
規約：各次数の全単体数で代用せず、元の非退化単体の個数を使う。
使われ方：cofinal な κ-filtered poset を作るための小さい部分複体の上界。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- κ 個未満の κ-small な部分複体の同じ和は κ-small。 -/
lemma isKappaSmall_iSup_subcomplex {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {X : SSet.{u}} {ι : Type u} (hι : Cardinal.mk ι < κ) (A : ι → X.Subcomplex)
    (hA : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ (A i).toSSet) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ (⨆ i, A i).toSSet := by
  let U : X.Subcomplex := ⨆ i, A i
  let f : (Σ i, (A i).toSSet.N) → U.toSSet.N := fun ⟨i, s⟩ =>
    N.mk ((Subcomplex.homOfLE (le_iSup A i)).app _ s.simplex)
      ((nonDegenerate_iff_of_mono (Subcomplex.homOfLE (le_iSup A i)) s.simplex).mpr
        s.nonDegenerate)
  have hf : Function.Surjective f := by
    intro s
    obtain ⟨d, ⟨s, hs⟩, rfl⟩ := s.mk_surjective
    have hu : s.val ∈ (⨆ i, A i).obj (Opposite.op ⦋d⦌) := s.property
    simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hu
    obtain ⟨i, hi⟩ := hu
    have hsX : s.val ∈ X.nonDegenerate d := (Subcomplex.mem_nonDegenerate_iff U s).mp hs
    refine ⟨⟨i, N.mk ⟨s.val, hi⟩ ?_⟩, rfl⟩
    exact (Subcomplex.mem_nonDegenerate_iff (A i) ⟨s.val, hi⟩).mpr hsX
  have hm : Cardinal.mk U.toSSet.N ≤ Cardinal.sum (fun i => Cardinal.mk (A i).toSSet.N) := by
    simpa only [Cardinal.mk_sigma] using Cardinal.mk_le_of_surjective hf
  exact lt_of_le_of_lt hm (Cardinal.sum_lt_of_isRegular hκ hι hA)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
