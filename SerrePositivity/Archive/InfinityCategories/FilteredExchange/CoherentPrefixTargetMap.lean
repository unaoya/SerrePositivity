module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentPrefixPathEnriched

/-!
概要：区間を全て写す単調写像による prefix 変形の標的変更。
方針：追加区間の各点を元の区間へ戻し、元の path の像を対応させる。
規約：実 path と指定精密化を保持する。
使われ方：固定始点の円柱の tail を元の正頂点側へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 区間を全て写す標的変更は prefix 変形と可換。 -/
lemma coherentPrefixPathDeformation_target_map {I J K : Type u}
    [LinearOrder I] [LinearOrder J] [LinearOrder K]
    (A : I →o J) (B : J →o K) (t : I →o Fin 2)
    (hB : ∀ x y z, B x ≤ z → z ≤ B y → ∃ w, x ≤ w ∧ w ≤ y ∧ B w = z)
    {i j : I} (P : Path i j) :
    coherentPrefixPathDeformation (B.comp A) t P =
      (SimplicialThickening.functorMap B ⟨A i⟩ ⟨A j⟩).obj
        (coherentPrefixPathDeformation A t P) := by
  apply SimplicialThickening.Path.ext
  ext z
  change (z ∈ (B.comp A) '' P.I ∨
    ∃ k ∈ P.I, t k = 0 ∧ B (A i) ≤ z ∧ z ≤ B (A k)) ↔
    z ∈ B '' (A '' P.I ∪ {w | ∃ k ∈ P.I, t k = 0 ∧ A i ≤ w ∧ w ≤ A k})
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, ht, hiz, hzk⟩)
    · exact ⟨A k, Or.inl ⟨k, hk, rfl⟩, rfl⟩
    · obtain ⟨w, hiw, hwk, hw⟩ := hB (A i) (A k) z hiz hzk
      exact ⟨w, Or.inr ⟨k, hk, ht, hiw, hwk⟩, hw⟩
  · rintro ⟨w, (⟨k, hk, rfl⟩ | ⟨k, hk, ht, hiw, hwk⟩), rfl⟩
    · exact Or.inl ⟨k, hk, rfl⟩
    · exact Or.inr ⟨k, hk, ht, B.monotone hiw, B.monotone hwk⟩

/-- 全区間を写す標的変更との可換性は全豊穣 Hom に持ち上がる。 -/
lemma coherentPrefixPathDeformationEnriched_target_map {I J K : Type u}
    [LinearOrder I] [LinearOrder J] [LinearOrder K]
    (A : I →o J) (B : J →o K) (t : I →o Fin 2)
    (hB : ∀ x y z, B x ≤ z → z ≤ B y → ∃ w, x ≤ w ∧ w ≤ y ∧ B w = z) :
    coherentPrefixPathDeformationEnriched (B.comp A) t =
      (coherentPrefixPathDeformationEnriched A t).comp SSet (SimplicialThickening.functor B) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext
    (fun z ↦ coherentPrefixPathDeformation_target_map A B t hB (P.obj z))

end SerrePositivity.InfinityCategories.F2
