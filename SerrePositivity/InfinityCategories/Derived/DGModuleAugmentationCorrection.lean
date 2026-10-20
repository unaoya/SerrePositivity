module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationExtendedCut
/-!
概要：全実混合係数を、augmentation の実後合成と同じ全域切断補正和に分解する。
方針：相一の内部点を有限集合にまとめ、元の従属した和を同じ各項へ移す。
規約：元の係数を変更しない。使われ方：一般 HA 方程式の微分・削除・切断和の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
/-- 相一の実内部切断点の有限集合。 -/
def dgModuleAugmentationCutPoints {n : ℕ} (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  I.filter (fun j ↦ a < j ∧ j < b ∧ β j = 1)
/-- 実相切断点の形成は、元の有限集合の点の削除と可換。 -/
lemma dgModuleAugmentationCutPoints_erase {n : ℕ} (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b j : Fin (n + 1)) :
    dgModuleAugmentationCutPoints β (I.erase j) a b =
      (dgModuleAugmentationCutPoints β I a b).erase j :=
  Finset.filter_erase _ _ _
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  {n : ℕ} (s : SimplexData R (DGModuleFunctorResolutionObject R C E F) n)
/-- 同じ実補正を、全域化した切断係数の有限和で表す。 -/
def dgModuleAugmentationPrismCorrection (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) :
    GradedHom R (s.obj a).replacement.val (F.obj (s.obj b).source) k :=
  ∑ j ∈ dgModuleAugmentationCutPoints β I a b,
    Index.sign I j • dgModuleAugmentationHomotopyCut R C E F s I a b k j
/-- 全実混合係数は、元の同じ augmentation 合成と全域切断補正和の和。 -/
lemma dgModuleAugmentationPrismMixedHom_eq_base_add_correction
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    dgModuleAugmentationPrismMixedHom R C E F s β I a b k hI ha hb hk =
      compose R (x := (s.obj a).replacement.val) (y := (s.obj b).replacement.val)
        (z := F.obj (s.obj b).source) (dgModuleAugmentationComponent R C E F (s.obj b)).val
        (((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj b)).f k
          (s.hom I a b k hI ha hb hk)) (add_zero k) +
      dgModuleAugmentationPrismCorrection R C E F s β I a b k := by
  unfold dgModuleAugmentationPrismMixedHom dgModuleAugmentationPrismCorrection
    dgModuleAugmentationCutPoints
  congr 1
  rw [Finset.sum_filter, ← Finset.sum_coe_sort I]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : a < j.val ∧ j.val < b ∧ β j.val = 1
  · simp only [dite_eq_left h, ite_eq_left h]
    exact dgModuleAugmentationPrismCut_eq_homotopyCut R C E F s I a b k hI ha hb hk
      j.val j.property h.1 h.2.1
  · simp only [dite_eq_right h, ite_eq_right h]
/-- 同じ実混合係数の微分も、後合成部分と同じ各実補正の微分和へ分解する。 -/
lemma dgModuleAugmentationPrismMixedHom_differential_decomposition
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d k (k + 1)
      (dgModuleAugmentationPrismMixedHom R C E F s β I a b k hI ha hb hk) =
    (moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d k (k + 1)
      (compose R (x := (s.obj a).replacement.val) (y := (s.obj b).replacement.val)
        (z := F.obj (s.obj b).source) (dgModuleAugmentationComponent R C E F (s.obj b)).val
        (((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj b)).f k
          (s.hom I a b k hI ha hb hk)) (add_zero k)) +
    ∑ j ∈ dgModuleAugmentationCutPoints β I a b,
      Index.sign I j • (moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d
        k (k + 1) (dgModuleAugmentationHomotopyCut R C E F s I a b k j) := by
  rw [dgModuleAugmentationPrismMixedHom_eq_base_add_correction]
  simp only [dgModuleAugmentationPrismCorrection, Units.smul_def, map_add, map_sum, map_zsmul]
end SerrePositivity.InfinityCategories
