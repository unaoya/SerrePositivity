module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPinchedPrismCorrectionSum

/-! 元の混合係数を主項と唯一の補正へ分離する。単なる別模型ではなく同じ prism の係数式。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E) {n : ℕ}

def dgGluingCommaPrismMainCoefficient (s : SimplexData R (DGFunctorCommaObject R C E F) n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :=
  compose R (x := (s.obj a).replacement) (y := (s.obj b).replacement)
    (z := F.obj (s.obj b).source) (dgCommaAugmentationComponent R C E F (s.obj b)).val
    (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj b)).f k
      (s.hom I a b k hI ha hb hk)) (add_zero k)

lemma dgGluingCommaPrismMixedCoefficient_eq (s : SimplexData R (DGFunctorCommaObject R C E F) n)
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' (Index.nonempty hI))
    (hb : b = I.max' (Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)) :
    dgCommaAugmentationPrismMixedHom R C E F s β I a b k hI ha hb hk =
      dgGluingCommaPrismMainCoefficient R C E F s I a b k hI ha hb hk +
        dgGluingCommaPrismCorrectionSum R C E F s β I a b k hI ha hb hk := rfl

variable {X Y : DGFunctorCommaObject R C E F}
  (s : (DGNerve.pinchedHom R (DGFunctorCommaObject R C E F) X Y) _⦋n⦌)

lemma dgGluingCommaPinchedPrismMixedCoefficient_correction
    (β : Fin (n + 2) →o Fin 2) (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card)
    (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    dgCommaAugmentationPrismMixedHom R C E F s.val.toSimplexData β (withLast J)
        (J.min' (Index.nonempty hJ)).castSucc (Fin.last (n + 1)) k
        (two_withLast (Index.nonempty hJ)) (min_withLast (Index.nonempty hJ) _)
        (max_withLast J _) (by rw [card_withLast]; omega) -
      dgGluingCommaPrismMainCoefficient R C E F s.val.toSimplexData (withLast J)
        (J.min' (Index.nonempty hJ)).castSucc (Fin.last (n + 1)) k
        (two_withLast (Index.nonempty hJ)) (min_withLast (Index.nonempty hJ) _)
        (max_withLast J _) (by rw [card_withLast]; omega) =
    if β (second J hJ).castSucc = 1 then
      dgCommaAugmentationPrismCut R C E F s.val.toSimplexData (withLast J)
        (J.min' (Index.nonempty hJ)).castSucc (Fin.last (n + 1)) k
        (two_withLast (Index.nonempty hJ)) (min_withLast (Index.nonempty hJ) _)
        (max_withLast J _) (by rw [card_withLast]; omega)
        (second J hJ).castSucc (Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨_, (Finset.mem_erase.mp (second_mem_erase J hJ)).2, rfl⟩))
        (Fin.castSucc_lt_castSucc_iff.mpr (first_lt_second J hJ)) (Fin.castSucc_lt_last _)
      else 0 := by
  rw [dgGluingCommaPrismMixedCoefficient_eq, add_sub_cancel_left]
  exact dgGluingCommaPinchedPrismCorrectionSum_second R C E F s β J hJ k hk

end SerrePositivity.InfinityCategories
