module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationDegenerateCut
/-!
概要：実候補の非単射な高次引き戻し係数を零として照合する。
方針：同じ全切断補正の零を総和し、二相の元の射と同じ混合係数を評価する。
規約：潰れた二点係数は別工程。使われ方：全実 prism の添字作用の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  {m n : ℕ} (s : SimplexData R (DGModuleFunctorResolutionObject R C E F) n)
/-- 始相零の非単射な実引き戻しでは、同じ全切断補正和は零。 -/
lemma dgModuleAugmentationPrismCorrection_pullback_zero_of_not_inj
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hi : ¬ Set.InjOn α (I : Set (Fin (m + 1))))
    (hpa : β (α a) = 0) :
    dgModuleAugmentationPrismCorrection R C E F (s.pullback α) (β.comp α) I a b k = 0 := by
  unfold dgModuleAugmentationPrismCorrection
  apply Finset.sum_eq_zero
  intro j hj
  have hm := Finset.mem_filter.mp hj
  rw [dgModuleAugmentationHomotopyCut_pullback_zero_of_not_inj R C E F s α β I a b k
    hI ha hb hk hi j hm.1 hm.2.1 hm.2.2.1 hpa hm.2.2.2, smul_zero]
/-- 非単射な高次の実混合引き戻し係数は、同じ基底と補正和から零。 -/
lemma dgModuleAugmentationPrismMixedHom_pullback_zero_of_not_inj
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hi : ¬ Set.InjOn α (I : Set (Fin (m + 1))))
    (hc : I.card ≠ 2) (hpa : β (α a) = 0) :
    dgModuleAugmentationPrismMixedHom R C E F (s.pullback α) (β.comp α) I a b k
      hI ha hb hk = 0 := by
  rw [dgModuleAugmentationPrismMixedHom_eq_base_add_correction,
    dgModuleAugmentationPrismCorrection_pullback_zero_of_not_inj R C E F s α β I a b k
      hI ha hb hk hi hpa,
    SimplexData.pullback_hom_of_not_inj s α I a b k hI ha hb hk hi hc,
    map_zero, compose_zero, zero_add]
/-- 明示した相の高次係数は、実端点相に沿う非単射な引き戻しで零。 -/
lemma dgModuleAugmentationPrismPhaseHom_pullback_zero_of_not_inj
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hi : ¬ Set.InjOn α (I : Set (Fin (m + 1))))
    (hc : I.card ≠ 2) (p q : Fin 2) (hpq : p ≤ q)
    (hpa : β (α a) = p) (hpb : β (α b) = q) :
    dgModuleAugmentationPrismPhaseHom R C E F (s.pullback α) (β.comp α) I a b k
      hI ha hb hk p q hpq = 0 := by
  fin_cases p <;> fin_cases q
  · change ((dgModuleAugmentationSource R C E F).map (s.obj (α a)) (s.obj (α b))).f k _ = 0
    rw [SimplexData.pullback_hom_of_not_inj s α I a b k hI ha hb hk hi hc, map_zero]
  · exact dgModuleAugmentationPrismMixedHom_pullback_zero_of_not_inj R C E F s α β I a b k
      hI ha hb hk hi hc hpa
  · change (1 : ℕ) ≤ 0 at hpq
    omega
  · change ((dgModuleAugmentationTarget R C E F).map (s.obj (α a)) (s.obj (α b))).f k _ = 0
    rw [SimplexData.pullback_hom_of_not_inj s α I a b k hI ha hb hk hi hc, map_zero]
/-- 実候補の高次係数は、非単射な添字変更の両側で同じ零となる。 -/
lemma dgModuleAugmentationPrismData_hom_pullback_of_not_inj
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hi : ¬ Set.InjOn α (I : Set (Fin (m + 1))))
    (hc : I.card ≠ 2) :
    (dgModuleAugmentationPrismData R C E F (s.pullback α) (β.comp α)).hom
        I a b k hI ha hb hk =
      ((dgModuleAugmentationPrismData R C E F s β).pullback α).hom I a b k hI ha hb hk := by
  rw [SimplexData.pullback_hom_of_not_inj (dgModuleAugmentationPrismData R C E F s β)
    α I a b k hI ha hb hk hi hc]
  have hab : a ≤ b := by rw [ha, hb]; exact (I.isLeast_min' _).2 (I.max'_mem _)
  exact dgModuleAugmentationPrismPhaseHom_pullback_zero_of_not_inj R C E F s α β I a b k
    hI ha hb hk hi hc (β (α a)) (β (α b)) (β.monotone (α.monotone hab)) rfl rfl
end SerrePositivity.InfinityCategories
