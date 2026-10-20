module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationReindexIndex
/-!
概要：augmentation の実切断と添字変更の比較に使う同じ全域係数を照合する。
方針：同じ有限集合上の単射性と、元の単体の実引き戻しの成分式を使う。
規約：全添字作用の自然性は別工程。使われ方：実 prism の引き戻し。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
/-- 正しい全域係数の単射引き戻しは、同じ像の全域係数。 -/
lemma dgSimplexHomOrZero_pullback_of_inj {R : Type u} [CommRing R]
    {D : Type v} [DGCategory R D] {m n : ℕ} (s : SimplexData R D n)
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hi : Set.InjOn α (I : Set (Fin (m + 1)))) :
    (s.pullback α).homOrZero I a b k = s.homOrZero (I.image α) (α a) (α b) k := by
  rw [SimplexData.homOrZero_eq (s.pullback α) I a b k hI ha hb hk,
    SimplexData.pullback_hom_of_inj s α I a b k hI ha hb hk hi]
  symm
  exact SimplexData.homOrZero_eq s (I.image α) (α a) (α b) k (Index.image_two hi hI)
    (Index.image_min α.monotone (by rw [ha]; exact I.isLeast_min' _) _)
    (Index.image_max α.monotone (by rw [hb]; exact I.isGreatest_max' _) _)
    (by rw [Finset.card_image_of_injOn hi]; exact hk)
end SerrePositivity.InfinityCategories
