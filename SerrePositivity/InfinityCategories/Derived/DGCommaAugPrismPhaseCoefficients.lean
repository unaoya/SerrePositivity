module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugPrismBoundary
/-!
概要：全候補の実係数から、二つの端点相で選ばれる同じ斉次係数を回収する。
方針：明示的な相選択の定義を評価し、対象の相違は異種等号で保持する。
規約：全 HA 方程式を仮定しない。使われ方：候補の線形・二次境界との直接比較。
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
  {n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) n)
/-- 両端相零の実候補係数は、同じ比較対象像の斉次係数。 -/
lemma dgCommaAugmentationPrismData_hom_zero
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 0) :
    HEq ((dgCommaAugmentationPrismData R C E F s β).hom I a b k hI ha hb hk)
      (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk)) := by
  have he : ∀ (p q : Fin 2) (h : p ≤ q), p = 0 → q = 0 →
      HEq (dgCommaAugmentationPrismPhaseHom R C E F s β I a b k hI ha hb hk p q h)
        (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj b)).f k
          (s.hom I a b k hI ha hb hk)) := by
    intro p q h hp hq
    subst p
    subst q
    rfl
  exact he (β a) (β b) _ hpa hpb
/-- 両端相一の実候補係数は、同じ元の入力像の斉次係数。 -/
lemma dgCommaAugmentationPrismData_hom_one
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 1) (hpb : β b = 1) :
    HEq ((dgCommaAugmentationPrismData R C E F s β).hom I a b k hI ha hb hk)
      (((dgCommaAugmentationTarget R C E F).map (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk)) := by
  have he : ∀ (p q : Fin 2) (h : p ≤ q), p = 1 → q = 1 →
      HEq (dgCommaAugmentationPrismPhaseHom R C E F s β I a b k hI ha hb hk p q h)
        (((dgCommaAugmentationTarget R C E F).map (s.obj a) (s.obj b)).f k
          (s.hom I a b k hI ha hb hk)) := by
    intro p q h hp hq
    subst p
    subst q
    rfl
  exact he (β a) (β b) _ hpa hpb
/-- 混合端点相の実候補係数は、元の同じ augmentation 切断補正和。 -/
lemma dgCommaAugmentationPrismData_hom_mixed
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1) :
    HEq ((dgCommaAugmentationPrismData R C E F s β).hom I a b k hI ha hb hk)
      (dgCommaAugmentationPrismMixedHom R C E F s β I a b k hI ha hb hk) := by
  have he : ∀ (p q : Fin 2) (h : p ≤ q), p = 0 → q = 1 →
      HEq (dgCommaAugmentationPrismPhaseHom R C E F s β I a b k hI ha hb hk p q h)
        (dgCommaAugmentationPrismMixedHom R C E F s β I a b k hI ha hb hk) := by
    intro p q h hp hq
    subst p
    subst q
    rfl
  exact he (β a) (β b) _ hpa hpb
/-- 相零の実候補対象は、同じ比較対象対象。 -/
lemma dgCommaAugmentationPrismData_obj_zero
    (β : Fin (n + 1) →o Fin 2) (a : Fin (n + 1)) (ha : β a = 0) :
    (dgCommaAugmentationPrismData R C E F s β).obj a = (s.obj a).replacement := by
  simp only [dgCommaAugmentationPrismData, ha, StrictNatTrans.phaseObj]
  rfl
/-- 相一の実候補対象は、元の同じ入力像。 -/
lemma dgCommaAugmentationPrismData_obj_one
    (β : Fin (n + 1) →o Fin 2) (a : Fin (n + 1)) (ha : β a = 1) :
    (dgCommaAugmentationPrismData R C E F s β).obj a = F.obj (s.obj a).source := by
  simp only [dgCommaAugmentationPrismData, ha, StrictNatTrans.phaseObj]
  rfl
/-- 正しい全域係数の両端相零の場合は、同じ比較対象像を回収する。 -/
lemma dgCommaAugmentationPrismData_homOrZero_zero
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 0) :
    HEq ((dgCommaAugmentationPrismData R C E F s β).homOrZero I a b k)
      (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk)) := by
  rw [SimplexData.homOrZero_eq (dgCommaAugmentationPrismData R C E F s β) I a b k
    hI ha hb hk]
  exact dgCommaAugmentationPrismData_hom_zero R C E F s β I a b k hI ha hb hk hpa hpb
/-- 正しい全域係数の両端相一の場合は、同じ入力像を回収する。 -/
lemma dgCommaAugmentationPrismData_homOrZero_one
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 1) (hpb : β b = 1) :
    HEq ((dgCommaAugmentationPrismData R C E F s β).homOrZero I a b k)
      (((dgCommaAugmentationTarget R C E F).map (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk)) := by
  rw [SimplexData.homOrZero_eq (dgCommaAugmentationPrismData R C E F s β) I a b k
    hI ha hb hk]
  exact dgCommaAugmentationPrismData_hom_one R C E F s β I a b k hI ha hb hk hpa hpb
/-- 正しい全域係数の混合端点相の場合は、同じ実混合係数を回収する。 -/
lemma dgCommaAugmentationPrismData_homOrZero_mixed
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1) :
    HEq ((dgCommaAugmentationPrismData R C E F s β).homOrZero I a b k)
      (dgCommaAugmentationPrismMixedHom R C E F s β I a b k hI ha hb hk) := by
  rw [SimplexData.homOrZero_eq (dgCommaAugmentationPrismData R C E F s β) I a b k
    hI ha hb hk]
  exact dgCommaAugmentationPrismData_hom_mixed R C E F s β I a b k hI ha hb hk hpa hpb
end SerrePositivity.InfinityCategories
