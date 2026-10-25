module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarSubsetLabels
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarShiftedInclusions
public import SerrePositivity.InfinityCategories.DGNerve.HomHEqAlgebra

/-!
概要：元の単体の非空部分集合ごとに、bar への実際の閉斉次包含を与える。
方針：同じ部分単体ラベルのシフト付き包含を、元の最小頂点へ移送する。
規約：対象と全次数を保持し、MC 方程式を追加仮定にしない。
使われ方：最後の対象を bar とする Bianchi データの係数。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgCoherentBarSubsetInclusion {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 1))) (r : ℕ) (hc : J.card = r + 1) (hJ : J.Nonempty) :
    GradedHom R ((coherentDiagramSimplex F σ).obj (J.min' hJ))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) (-(r : ℤ)) :=
  (gradedHomTransportWithHEq (A := R) (D := RightModule R D)
    (dgCoherentBarSubsetLabel_source R D F σ J r hc hJ) rfl rfl
    (dgCoherentBarShiftedInclusion R D F (dgCoherentBarSubsetLabel σ J r hc))).val

lemma dgCoherentBarSubsetInclusion_heq {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 1))) (r : ℕ) (hc : J.card = r + 1) (hJ : J.Nonempty) :
    HEq (dgCoherentBarSubsetInclusion R D F σ J r hc hJ)
      (dgCoherentBarShiftedInclusion R D F (dgCoherentBarSubsetLabel σ J r hc)) :=
  (gradedHomTransportWithHEq (A := R) (D := RightModule R D) _ _ _ _).property

lemma dgCoherentBarSubsetInclusion_d {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 1))) (r : ℕ) (hc : J.card = r + 1) (hJ : J.Nonempty) :
    differential R (dgCoherentBarSubsetInclusion R D F σ J r hc hJ) = 0 := by
  have hd := gradedHom_differential_heq (A := R) (D := RightModule R D)
    (dgCoherentBarSubsetLabel_source R D F σ J r hc hJ).symm rfl rfl
    (dgCoherentBarSubsetInclusion R D F σ J r hc hJ)
    (dgCoherentBarShiftedInclusion R D F (dgCoherentBarSubsetLabel σ J r hc))
    (dgCoherentBarSubsetInclusion_heq R D F σ J r hc hJ)
  have hz := dgCoherentBarShiftedInclusion_d R D F (dgCoherentBarSubsetLabel σ J r hc)
  change differential R (D := RightModule R D)
    (x := dgCoherentBarSource R D F (dgCoherentBarSubsetLabel σ J r hc))
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (dgCoherentBarShiftedInclusion R D F
    (dgCoherentBarSubsetLabel σ J r hc)) = 0 at hz
  exact eq_of_heq (hd.trans ((heq_of_eq hz).trans
    (gradedHom_zero_heq (A := R) (D := RightModule R D)
      (dgCoherentBarSubsetLabel_source R D F σ J r hc hJ) rfl rfl)))

end SerrePositivity.InfinityCategories
