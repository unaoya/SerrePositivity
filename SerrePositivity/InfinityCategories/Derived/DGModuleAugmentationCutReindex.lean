module

public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationPrismSimplex
public import SerrePositivity.InfinityCategories.DGNerve.AugmentationCombinatorics
/-!
概要：実 augmentation の全域切断補正を、単射な添字変更の同じ像へ照合する。
方針：左右の集合・次数を先にそろえ、正しい全域係数の引き戻しを使う。
規約：依存した真の hom の証明引数を書き換えない。使われ方：全実混合係数の自然性。
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
/-- 正しい実内部切断の全域補正は、I 上単射な添字変更の同じ像と一致する。 -/
lemma dgModuleAugmentationHomotopyCut_pullback_of_inj
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hi : Set.InjOn α (I : Set (Fin (m + 1))))
    (j : Fin (m + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    dgModuleAugmentationHomotopyCut R C E F (s.pullback α) I a b k j =
      dgModuleAugmentationHomotopyCut R C E F s (I.image α) (α a) (α b) k (α j) := by
  have hamin : IsLeast (I : Set (Fin (m + 1))) a := by
    rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (m + 1))) b := by
    rw [hb]; exact I.isGreatest_max' _
  have hIL := Index.left_two hamin.1 hj haj
  have hIR := Index.right_two hj hbmax.1 hjb
  have hiL : Set.InjOn α ((I.filter (· ≤ j)) : Set (Fin (m + 1))) :=
    hi.mono (Finset.filter_subset _ _)
  have hiR : Set.InjOn α ((I.filter (j ≤ ·)) : Set (Fin (m + 1))) :=
    hi.mono (Finset.filter_subset _ _)
  have hLeft := Index.image_left α.monotone hi hj
  have hRight := Index.image_right α.monotone hi hj
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ) - 1) = k := by
    have := Index.split_card hj
    omega
  rw [dgModuleAugmentationHomotopyCut, dgModuleAugmentationHomotopyCut,
    ← hLeft, ← hRight, Finset.card_image_of_injOn hiL, Finset.card_image_of_injOn hiR]
  simp only [dite_eq_left hsum]
  rw [dgSimplexHomOrZero_pullback_of_inj s α (I.filter (j ≤ ·)) j b _ hIR
    (Index.right_min hj _) (Index.right_max hbmax hjb.le _) rfl hiR,
    dgSimplexHomOrZero_pullback_of_inj s α (I.filter (· ≤ j)) a j _ hIL
    (Index.left_min hamin haj.le _) (Index.left_max hj _) rfl hiL]
  rfl
end SerrePositivity.InfinityCategories
