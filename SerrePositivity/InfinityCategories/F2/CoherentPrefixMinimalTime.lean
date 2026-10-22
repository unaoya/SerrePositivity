module

public import SerrePositivity.InfinityCategories.F2.CoherentPrefixPathEnriched

/-!
概要：時刻零が最小点に限られる場合、prefix 変形は元の path の像を保持する。
方針：追加区間の始点も最小点なので、その区間は一点になる。
規約：全ての path と全次数の精密化を保持する。
使われ方：固定始点の coslice 円柱の時刻一の端点。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 零時刻が最小点だけなら追加区間は元の path の像に含まれる。 -/
lemma coherentPrefixPathDeformation_eq_image_of_zero_minimal
    {J K : Type u} [LinearOrder J] [OrderBot J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) (ht : ∀ k, t k = 0 → k = ⊥)
    {i j : J} (P : Path i j) :
    coherentPrefixPathDeformation A t P =
      (SimplicialThickening.functorMap A ⟨i⟩ ⟨j⟩).obj P := by
  apply SimplicialThickening.Path.ext
  ext z
  change (z ∈ A '' P.I ∨ ∃ k ∈ P.I, t k = 0 ∧ A i ≤ z ∧ z ≤ A k) ↔ z ∈ A '' P.I
  constructor
  · rintro (hz | ⟨k, hk, hk0, hiz, hzk⟩)
    · exact hz
    · have hik : i = k := le_antisymm (P.left_le k hk) (by rw [ht k hk0]; exact bot_le)
      have hz : z = A k := le_antisymm hzk (by simpa only [hik] using hiz)
      exact ⟨k, hk, hz.symm⟩
  · exact Or.inl

/-- 最小点だけの零時刻では全豊穣 Hom の作用も元の対象写像の作用。 -/
lemma coherentPrefixPathDeformationEnriched_eq_of_zero_minimal
    {J K : Type u} [LinearOrder J] [OrderBot J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) (ht : ∀ k, t k = 0 → k = ⊥) :
    coherentPrefixPathDeformationEnriched A t = SimplicialThickening.functor A := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext
    (fun z ↦ coherentPrefixPathDeformation_eq_image_of_zero_minimal A t ht (P.obj z))

end SerrePositivity.InfinityCategories.F2
