module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallSimplicialShapes

/-!
概要：正則 κ について κ 個未満の κ-small な部分複体で被覆される単体集合は κ-small。
方針：非退化単体をいずれかの部分複体から持ち上げ、正則濃度の和を評価する。
規約：各次数の単体数ではなく非退化単体全体を数える。
使われ方：κ-small join と κ-filtered な coslice の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：被覆された単体集合の非退化単体は、部品の非退化単体の直和から覆われる。
方針：単体の上限への所属と、包含による非退化性の反映を使う。
規約：添字と単体集合の宇宙は同じ。使われ方：上限の濃度評価。 -/
lemma nondegenerate_cover_cardinal_le {X : SSet.{u}} {ι : Type u}
    (A : ι → X.Subcomplex) (hA : ⨆ i, A i = ⊤) :
    Cardinal.mk X.N ≤ Cardinal.sum (fun i ↦ Cardinal.mk (A i).toSSet.N) := by
  let f : (Σ i, (A i).toSSet.N) → X.N := fun ⟨i, s⟩ ↦
    N.mk ((A i).ι.app _ s.simplex)
      (by simpa only [nonDegenerate_iff_of_mono] using s.nonDegenerate)
  have hf : Function.Surjective f := by
    intro s
    obtain ⟨d, ⟨s, h₂⟩, rfl⟩ := s.mk_surjective
    have h₁ : s ∈ (⨆ i, A i).obj (Opposite.op ⦋d⦌) := by rw [hA]; trivial
    simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at h₁
    obtain ⟨i, hi⟩ := h₁
    exact ⟨⟨i, N.mk ⟨s, hi⟩ (by rwa [Subcomplex.mem_nonDegenerate_iff])⟩, rfl⟩
  simpa only [Cardinal.mk_sigma] using Cardinal.mk_le_of_surjective hf

/-- 概要：正則 κ に関して κ 個未満の κ-small な部分複体で覆われる対象は κ-small。
方針：非退化単体の直和による上界に正則濃度の和の評価を適用する。
規約：κ の正則性を明示する。使われ方：形状の被覆からの小ささの判定。 -/
lemma isKappaSmall_of_cover {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {X : SSet.{u}} {ι : Type u} (hι : Cardinal.mk ι < κ) (A : ι → X.Subcomplex)
    (hA : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ (A i)) (hcover : ⨆ i, A i = ⊤) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ X :=
  lt_of_le_of_lt (nondegenerate_cover_cardinal_le A hcover)
    (Cardinal.sum_lt_of_isRegular hκ hι hA)

end SerrePositivity.InfinityCategories.Project.FilteredExchange
