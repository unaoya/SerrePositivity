module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugPrismPhaseCoefficients
public import SerrePositivity.InfinityCategories.DGNerve.PinchedTerms

/-! 元の comma augmentation prism は pinched 入力で線形化し、二番目以外の切断は消える。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  {X Y : DGFunctorCommaObject R C E F} {n : ℕ}
  (s : (DGNerve.pinchedHom R (DGFunctorCommaObject R C E F) X Y) _⦋n⦌)

lemma dgGluingCommaPinchedPrismCut_zero_of_ne_second
    (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - (J.card : ℤ))
    (j : Fin (n + 1)) (hj : j ∈ J) (haj : J.min' (Index.nonempty hJ) < j)
    (hne : j ≠ second J hJ) :
    dgCommaAugmentationPrismCut R C E F s.val.toSimplexData (withLast J)
      (J.min' (Index.nonempty hJ)).castSucc (Fin.last (n + 1)) k
      (two_withLast (Index.nonempty hJ)) (min_withLast (Index.nonempty hJ) _)
      (max_withLast J _) (by rw [card_withLast]; omega)
      j.castSucc (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
      (Fin.castSucc_lt_castSucc_iff.mpr haj) (Fin.castSucc_lt_last j) = 0 := by
  have hL := Index.left_two (J.min'_mem (Index.nonempty hJ)) hj haj
  have haL := Index.left_min (J.isLeast_min' (Index.nonempty hJ)) haj.le (Index.nonempty hL)
  have hjL := Index.left_max hj (Index.nonempty hL)
  have hc : (J.filter (· ≤ j)).card ≠ 2 := mt (left_card_two_iff J hJ j hj haj).mp hne
  have hz : ∀ (hI : 2 ≤ ((withLast J).filter (· ≤ j.castSucc)).card)
      (ha : (J.min' (Index.nonempty hJ)).castSucc =
        ((withLast J).filter (· ≤ j.castSucc)).min' (Index.nonempty hI))
      (hb : j.castSucc = ((withLast J).filter (· ≤ j.castSucc)).max' (Index.nonempty hI)),
      s.val.hom ((withLast J).filter (· ≤ j.castSucc))
        (J.min' (Index.nonempty hJ)).castSucc j.castSucc
        (2 - (((withLast J).filter (· ≤ j.castSucc)).card : ℤ)) hI ha hb rfl = 0 := by
    intro hI ha hb
    exact front_hom_zero_of_image s _ _ _ _ _ hI ha hb rfl hL haL hjL (left_withLast J j) hc
  dsimp only [dgCommaAugmentationPrismCut]
  rw [hz, map_zero, compose_zero, smul_zero]

end SerrePositivity.InfinityCategories
