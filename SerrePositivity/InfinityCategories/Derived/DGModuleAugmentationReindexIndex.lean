module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationPrismSimplex
/-!
概要：augmentation の実切断と添字変更の比較に使う有限順序の像を照合する。
方針：同じ有限集合上の単射性と、元の単体の実引き戻しの成分式を使う。
規約：全添字作用の自然性は別工程。使われ方：実 prism の引き戻し。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
/-- 相一の切断点集合の像を同じ相の切断点集合と同定する。 -/
lemma dgModuleAugmentationCutPoints_image {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (ha : a ∈ I) (hb : b ∈ I)
    (hi : Set.InjOn α (I : Set (Fin (m + 1)))) :
    (dgModuleAugmentationCutPoints (β.comp α) I a b).image α =
      dgModuleAugmentationCutPoints β (I.image α) (α a) (α b) := by
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
    have hm := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j, hm.1, rfl⟩,
      (Index.image_lt_iff α.monotone hi ha hm.1).mpr hm.2.1,
      (Index.image_lt_iff α.monotone hi hm.1 hb).mpr hm.2.2.1, hm.2.2.2⟩
  · intro hy
    have hm := Finset.mem_filter.mp hy
    rcases Finset.mem_image.mp hm.1 with ⟨j, hj, rfl⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj,
      (Index.image_lt_iff α.monotone hi ha hj).mp hm.2.1,
      (Index.image_lt_iff α.monotone hi hj hb).mp hm.2.2.1, hm.2.2.2⟩, rfl⟩
/-- 左切断の像の濃度は元の同じ左切断の濃度。 -/
lemma dgModuleAugmentationLeftCut_image_card {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    (hi : Set.InjOn α (I : Set (Fin (m + 1)))) (j : Fin (m + 1)) (hj : j ∈ I) :
    ((I.image α).filter (· ≤ α j)).card = (I.filter (· ≤ j)).card := by
  rw [← Index.image_left α.monotone hi hj]
  exact Finset.card_image_of_injOn (hi.mono (Finset.filter_subset _ _))
/-- 右切断の像の濃度は元の同じ右切断の濃度。 -/
lemma dgModuleAugmentationRightCut_image_card {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    (hi : Set.InjOn α (I : Set (Fin (m + 1)))) (j : Fin (m + 1)) (hj : j ∈ I) :
    ((I.image α).filter (α j ≤ ·)).card = (I.filter (j ≤ ·)).card := by
  rw [← Index.image_right α.monotone hi hj]
  exact Finset.card_image_of_injOn (hi.mono (Finset.filter_subset _ _))
/-- 共有切断点を持つ左右で単射なら、元の添字集合全体で単射。 -/
lemma dgModuleAugmentationCut_injective_glue {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    (j : Fin (m + 1)) (hj : j ∈ I)
    (hL : Set.InjOn α ((I.filter (· ≤ j)) : Set (Fin (m + 1))))
    (hR : Set.InjOn α ((I.filter (j ≤ ·)) : Set (Fin (m + 1)))) :
    Set.InjOn α (I : Set (Fin (m + 1))) := by
  have hcross : ∀ x ∈ I, ∀ y ∈ I, x ≤ j → j ≤ y → α x = α y → x = y := by
    intro x hx y hy hxj hjy he
    have hxj' : α x = α j := le_antisymm (α.monotone hxj)
      (by rw [he]; exact α.monotone hjy)
    have hxj'' : x = j := hL (Finset.mem_filter.mpr ⟨hx, hxj⟩)
      (Finset.mem_filter.mpr ⟨hj, le_refl j⟩) hxj'
    have hjy' : α j = α y := by rw [← hxj'']; exact he
    have hjy'' : j = y := hR (Finset.mem_filter.mpr ⟨hj, le_refl j⟩)
      (Finset.mem_filter.mpr ⟨hy, hjy⟩) hjy'
    exact hxj''.trans hjy''
  intro x hx y hy he
  by_cases hxj : x ≤ j
  · by_cases hyj : y ≤ j
    · exact hL (Finset.mem_filter.mpr ⟨hx, hxj⟩) (Finset.mem_filter.mpr ⟨hy, hyj⟩) he
    · exact hcross x hx y hy hxj (le_of_lt (lt_of_not_ge hyj)) he
  · by_cases hyj : y ≤ j
    · exact (hcross y hy x hx hyj (le_of_lt (lt_of_not_ge hxj)) he.symm).symm
    · exact hR (Finset.mem_filter.mpr ⟨hx, le_of_lt (lt_of_not_ge hxj)⟩)
        (Finset.mem_filter.mpr ⟨hy, le_of_lt (lt_of_not_ge hyj)⟩) he
end SerrePositivity.InfinityCategories
