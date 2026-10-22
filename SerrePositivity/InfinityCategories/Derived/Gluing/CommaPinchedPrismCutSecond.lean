module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPinchedPrismCutZero
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPrismUnitCut

/-! pinched 入力の唯一の補正切断を、同じ右比較成分へ全次数で同定する。 -/
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

lemma dgGluingCommaPinchedPrismCut_second
    (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    HEq (dgCommaAugmentationPrismCut R C E F s.val.toSimplexData (withLast J)
      (J.min' (Index.nonempty hJ)).castSucc (Fin.last (n + 1)) k
      (two_withLast (Index.nonempty hJ)) (min_withLast (Index.nonempty hJ) _)
      (max_withLast J _) (by rw [card_withLast]; omega)
      (second J hJ).castSucc (Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨_, (Finset.mem_erase.mp (second_mem_erase J hJ)).2, rfl⟩))
      (Fin.castSucc_lt_castSucc_iff.mpr (first_lt_second J hJ)) (Fin.castSucc_lt_last _))
      (dgGluingCommaPrismRightCorrection R C E F s.val.toSimplexData (withLast J)
        (Fin.last (n + 1)) (two_withLast (Index.nonempty hJ)) (max_withLast J _)
        (second J hJ).castSucc (Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨_, (Finset.mem_erase.mp (second_mem_erase J hJ)).2, rfl⟩))
        (Fin.castSucc_lt_last _)) := by
  have hj := (Finset.mem_erase.mp (second_mem_erase J hJ)).2
  have haj := first_lt_second J hJ
  have hL := Index.left_two (J.min'_mem (Index.nonempty hJ)) hj haj
  have haL := Index.left_min (J.isLeast_min' (Index.nonempty hJ)) haj.le (Index.nonempty hL)
  have hjL := Index.left_max hj (Index.nonempty hL)
  have hc : (J.filter (· ≤ second J hJ)).card = 2 :=
    (left_card_two_iff J hJ _ hj haj).mpr rfl
  apply dgGluingCommaPrismCut_of_left_unit
  · exact (source_obj s _).trans (source_obj s _).symm
  · rw [left_withLast, Finset.card_image_of_injective _ (Fin.castSucc_injective _), hc]
    norm_num
  · dsimp only [SimplexData.cutLeft]
    have hu : ∀ (hI : 2 ≤ ((withLast J).filter (· ≤ (second J hJ).castSucc)).card)
        (ha : (J.min' (Index.nonempty hJ)).castSucc =
          ((withLast J).filter (· ≤ (second J hJ).castSucc)).min' (Index.nonempty hI))
        (hb : (second J hJ).castSucc =
          ((withLast J).filter (· ≤ (second J hJ).castSucc)).max' (Index.nonempty hI)),
        HEq (s.val.hom ((withLast J).filter (· ≤ (second J hJ).castSucc))
          (J.min' (Index.nonempty hJ)).castSucc (second J hJ).castSucc
          (2 - (((withLast J).filter (· ≤ (second J hJ).castSucc)).card : ℤ)) hI ha hb rfl)
          (unitElement R X).val := by
      intro hI ha hb
      exact front_hom_unit_of_image s _ _ _ _ _ hI ha hb rfl hL haL hjL
        (left_withLast J _) hc
    refine (hu _ _ _).trans ?_
    rw [source_obj s (second J hJ)]

end SerrePositivity.InfinityCategories
