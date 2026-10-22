module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPinchedPrismCutSecond

/-! 唯一の切断の右係数は、最小点を消した元 Hom の線形成分への比較 cochain の作用である。 -/
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

lemma dgGluingCommaHomotopyComponent_smul_heq
    {X Y X' Y' : DGFunctorCommaObject R C E F} {p q : ℤ}
    (hx : X = X') (hy : Y = Y') (hp : p = q)
    (a : GradedHom R X Y p) (b : GradedHom R X' Y' q) (hab : HEq a b) (σ : ℤˣ) :
    HEq (σ • dgCommaAugmentationHomotopyComponent R C E F X Y p a)
      (σ • dgCommaAugmentationHomotopyComponent R C E F X' Y' q b) := by
  cases hx
  cases hy
  cases hp
  rw [eq_of_heq hab]

variable {X Y : DGFunctorCommaObject R C E F} {n : ℕ}
  (s : (DGNerve.pinchedHom R (DGFunctorCommaObject R C E F) X Y) _⦋n⦌)

lemma dgGluingCommaPinchedPrismRightCorrection_linear
    (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    HEq (dgGluingCommaPrismRightCorrection R C E F s.val.toSimplexData (withLast J)
        (Fin.last (n + 1)) (two_withLast (Index.nonempty hJ)) (max_withLast J _)
        (second J hJ).castSucc (Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨_, (Finset.mem_erase.mp (second_mem_erase J hJ)).2, rfl⟩)) (Fin.castSucc_lt_last _))
      ((((withLast J).filter ((second J hJ).castSucc < ·)).card : ℤ).negOnePow •
        dgCommaAugmentationHomotopyComponent R C E F X Y (k + 1)
          ((toLinearData s).component (J.erase (J.min' (Index.nonempty hJ))) (k + 1)
            (LinearData.erase_nonempty hJ _ (J.min'_mem _))
            (by have := Finset.card_erase_add_one (J.min'_mem (Index.nonempty hJ)); omega))) := by
  dsimp only [dgGluingCommaPrismRightCorrection]
  apply dgGluingCommaHomotopyComponent_smul_heq
  · exact source_obj s _
  · exact target_obj s
  · rw [right_withLast, right_second, card_withLast]
    have := Finset.card_erase_add_one (J.min'_mem (Index.nonempty hJ))
    omega
  · exact cutRight_second_heq_component s J hJ k hk

end SerrePositivity.InfinityCategories
