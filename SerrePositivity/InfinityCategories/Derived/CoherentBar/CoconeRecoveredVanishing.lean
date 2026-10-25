module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredMixedNaturality
/-!
概要：右部分集合の添字変更が退化すると、回収した一点下の混合成分は零になる。
方針：回収 Hom の退化消滅を混合成分の実計算則に移す。
規約：零成分の端点を明示し、右面の定値性を要求しない。
使われ方：回収データの全面・全退化の自然性の非単射分岐。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarCoconeRecoveredRawData_mixed_zero_of_not_injOn {m n : ℕ}
    (c : (sliceUnder F) _⦋n⦌) (α : Fin (m + 1) →o Fin (n + 1))
    (K : Finset (Fin 1)) (L : Finset (Fin (m + 1))) (hK : K.Nonempty) (hL : L.Nonempty)
    (hi : ¬Set.InjOn α (L : Set (Fin (m + 1))))
    (a b : Fin (0 + m + 1 + 1)) (k : ℤ)
    (hJ : 2 ≤ (dgCoherentBarJoinSubset K L).card)
    (ha : a = (dgCoherentBarJoinSubset K L).min' (Index.nonempty hJ))
    (hb : b = (dgCoherentBarJoinSubset K L).max' (Index.nonempty hJ))
    (hk : k = 2 - ((dgCoherentBarJoinSubset K L).card : ℤ)) :
    (dgCoherentBarCoconeRecoveredRawData R D F hMC
      ((sliceUnder F).map (SimplexCategory.mkHom α).op c)).hom
      (dgCoherentBarJoinSubset K L) a b k hJ ha hb hk = 0 := by
  have hK0 := dgCoherentBarFinOneSubset_eq_univ K hK
  subst K
  let c' := (sliceUnder F).map (SimplexCategory.mkHom α).op c
  let Q := dgCoherentBarCoconeRecoveredRawData R D F hMC c'
  have hkL : k = 1 - (L.card : ℤ) := by
    rw [dgCoherentBarJoinSubset_card] at hk
    simp only [Finset.card_univ, Fintype.card_fin] at hk
    omega
  have hRaw := dgCoherentBarCoconeRecoveredRawData_mixed_hom_heq R D F hMC c' L hL
    a b k hJ ha hb hk
  rw [dgCoherentBarCoconeLiftSubsetHom_map_of_not_injOn R D F hMC c α L k hL hkL hi] at hRaw
  have hx : Q.obj a = dgCoherentBarNormalizedModule R D F hMC := by
    rw [ha, dgCoherentBarJoinSubset_min Finset.univ L hK (Index.nonempty hJ)]
    exact congrArg (fun t : SimplexData R (RightModule R D) 0 => t.obj (Finset.univ.min' hK))
      (dgCoherentBarCoconeRecoveredRawData_left R D F hMC c')
  have hz : Q.obj b = ((sliceUnderProjection F).app (Opposite.op ⦋m⦌) c').obj
      (L.max' hL) := by
    rw [hb, dgCoherentBarJoinSubset_max Finset.univ L hL (Index.nonempty hJ)]
    exact congrArg (fun t : SimplexData R (RightModule R D) m => t.obj (L.max' hL))
      (dgCoherentBarCoconeRecoveredRawData_right R D F hMC c')
  exact eq_of_heq (hRaw.trans
    (gradedHom_zero_heq (A := R) (D := RightModule R D) hx hz rfl).symm)

end SerrePositivity.InfinityCategories
