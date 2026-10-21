module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugCorrectionReindex
/-!
概要：実 augmentation 候補の全相係数と、実単体の単射引き戻しを照合する。
方針：明示的な相選択を評価し、元の dg 関手の像または同じ混合係数の引き戻しを使う。
規約：非単射な添字変更は別工程。使われ方：全実 prism の単体作用の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  {m n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) n)
/-- 明示した二相の同じ係数は、I 上単射な添字変更で引き戻せる。 -/
lemma dgCommaAugmentationPrismPhaseHom_pullback_of_inj
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hi : Set.InjOn α (I : Set (Fin (m + 1))))
    (p q : Fin 2) (hpq : p ≤ q) :
    dgCommaAugmentationPrismPhaseHom R C E F (s.pullback α) (β.comp α) I a b k
        hI ha hb hk p q hpq =
      dgCommaAugmentationPrismPhaseHom R C E F s β (I.image α) (α a) (α b) k
        (Index.image_two hi hI)
        (Index.image_min α.monotone (by rw [ha]; exact I.isLeast_min' _) _)
        (Index.image_max α.monotone (by rw [hb]; exact I.isGreatest_max' _) _)
        (by rw [Finset.card_image_of_injOn hi]; exact hk) p q hpq := by
  fin_cases p <;> fin_cases q
  · change ((dgCommaAugmentationSource R C E F).map (s.obj (α a)) (s.obj (α b))).f k _ =
      ((dgCommaAugmentationSource R C E F).map (s.obj (α a)) (s.obj (α b))).f k _
    rw [SimplexData.pullback_hom_of_inj s α I a b k hI ha hb hk hi]
  · exact dgCommaAugmentationPrismMixedHom_pullback_of_inj R C E F s α β I a b k
      hI ha hb hk hi
  · change (1 : ℕ) ≤ 0 at hpq
    omega
  · change ((dgCommaAugmentationTarget R C E F).map (s.obj (α a)) (s.obj (α b))).f k _ =
      ((dgCommaAugmentationTarget R C E F).map (s.obj (α a)) (s.obj (α b))).f k _
    rw [SimplexData.pullback_hom_of_inj s α I a b k hI ha hb hk hi]
/-- 実候補の同じ正しい係数は、I 上単射な任意の添字変更と可換。 -/
lemma dgCommaAugmentationPrismData_hom_pullback_of_inj
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hi : Set.InjOn α (I : Set (Fin (m + 1)))) :
    (dgCommaAugmentationPrismData R C E F (s.pullback α) (β.comp α)).hom
        I a b k hI ha hb hk =
      ((dgCommaAugmentationPrismData R C E F s β).pullback α).hom I a b k hI ha hb hk := by
  rw [SimplexData.pullback_hom_of_inj (dgCommaAugmentationPrismData R C E F s β)
    α I a b k hI ha hb hk hi]
  have hab : a ≤ b := by rw [ha, hb]; exact (I.isLeast_min' _).2 (I.max'_mem _)
  exact dgCommaAugmentationPrismPhaseHom_pullback_of_inj R C E F s α β I a b k
    hI ha hb hk hi (β (α a)) (β (α b)) (β.monotone (α.monotone hab))
/-- 実 augmentation 単体の族は、単射な全添字変更と厳密に可換。 -/
lemma dgCommaAugmentationPrismSimplex_pullback_of_injective
    (s : Simplex R (DGFunctorCommaObject R C E F) n)
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (n + 1) →o Fin 2)
    (hi : Function.Injective α) :
    dgCommaAugmentationPrismSimplex R C E F (s.pullback α) (β.comp α) =
      (dgCommaAugmentationPrismSimplex R C E F s β).pullback α := by
  apply Simplex.ext
  apply SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    exact dgCommaAugmentationPrismData_hom_pullback_of_inj R C E F s.toSimplexData α β I a b k
      hI ha hb hk hi.injOn
end SerrePositivity.InfinityCategories
