module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftHomComparison
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinRawCoordinates
/-!
概要：持ち上げ余錐の任意の右部分単体から、正規化 bar を始域とする成分を回収する。
方針：右部分集合を昇順列挙し、回収 Hom の終域を右面の最大頂点へ移す。
規約：右面の全 HA 成分を保持し、定値性を仮定しない。
使われ方：標準族の持ち上げを、bar から出る高次の比較へ移す。
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

lemma dgCoherentBarCoconeLiftTarget_subset {n r : ℕ}
    (c : (sliceUnder F) _⦋n⦌) (J : Finset (Fin (n + 1)))
    (hc : J.card = r + 1) (hJ : J.Nonempty) :
    dgCoherentBarCoconeLiftTarget R D F
      ((sliceUnder F).map (SimplexCategory.mkHom (J.orderEmbOfFin hc).toOrderHom).op c) =
        ((sliceUnderProjection F).app (Opposite.op ⦋n⦌) c).obj (J.max' hJ) := by
  let α := SimplexCategory.mkHom (J.orderEmbOfFin hc).toOrderHom
  have hNat := ConcreteCategory.congr_hom ((sliceUnderProjection F).naturality α.op) c
  change ((sliceUnderProjection F).app (Opposite.op ⦋r⦌)
    ((sliceUnder F).map α.op c)) =
      (dgNerve R (RightModule R D)).map α.op
        ((sliceUnderProjection F).app (Opposite.op ⦋n⦌) c) at hNat
  unfold dgCoherentBarCoconeLiftTarget
  rw [hNat]
  change ((sliceUnderProjection F).app (Opposite.op ⦋n⦌) c).obj
    ((J.orderEmbOfFin hc) (Fin.last r)) = _
  have hLast : (J.orderEmbOfFin hc) (Fin.last r) = J.max' hJ := by
    have h := Finset.orderEmbOfFin_last hc (by omega)
    have hi : (⟨(r + 1) - 1, Nat.sub_lt (show 0 < r + 1 by omega) (Nat.succ_pos 0)⟩ :
        Fin (r + 1)) = Fin.last r := Fin.ext (by change (r + 1) - 1 = r; omega)
    rw [hi] at h
    exact h
  rw [hLast]

def dgCoherentBarCoconeLiftSubsetHom {n : ℕ}
    (c : (sliceUnder F) _⦋n⦌) (J : Finset (Fin (n + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    GradedHom R (dgCoherentBarNormalizedModule R D F hMC)
      (((sliceUnderProjection F).app (Opposite.op ⦋n⦌) c).obj (J.max' hJ)) k :=
  gradedHomTransport rfl
    (dgCoherentBarCoconeLiftTarget_subset R D F c J
      (show J.card = (J.card - 1) + 1 by have := Finset.card_pos.mpr hJ; omega) hJ)
    (show -((J.card - 1 : ℕ) : ℤ) = k by have := Finset.card_pos.mpr hJ; omega)
    (dgCoherentBarCoconeLiftHom R D F hMC
      ((sliceUnder F).map (SimplexCategory.mkHom
        (J.orderEmbOfFin (show J.card = (J.card - 1) + 1 by
          have := Finset.card_pos.mpr hJ; omega)).toOrderHom).op c))

lemma dgCoherentBarCoconeLiftSubsetHom_heq {n r : ℕ}
    (c : (sliceUnder F) _⦋n⦌) (J : Finset (Fin (n + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) (hc : J.card = r + 1) :
    HEq (dgCoherentBarCoconeLiftSubsetHom R D F hMC c J k hJ hk)
      (dgCoherentBarCoconeLiftHom R D F hMC
        ((sliceUnder F).map (SimplexCategory.mkHom (J.orderEmbOfFin hc).toOrderHom).op c)) := by
  have hr : J.card - 1 = r := by omega
  cases hr
  unfold dgCoherentBarCoconeLiftSubsetHom
  exact gradedHomTransport_heq _ _ _ _

def dgCoherentBarCoconeRecoveredMixedData {n : ℕ} (c : (sliceUnder F) _⦋n⦌) :
    DGCoherentBarJoinMixedData
      (Simplex.vertex (A := R) (dgCoherentBarNormalizedModule R D F hMC)).toSimplexData
      ((sliceUnderProjection F).app (Opposite.op ⦋n⦌) c).toSimplexData := by
  intro K J hK hJ k hk
  have hKc : K.card = 1 := by
    have hSub : K ⊆ (Finset.univ : Finset (Fin 1)) := Finset.subset_univ _
    have hLe := Finset.card_le_card hSub
    have hPos := Finset.card_pos.mpr hK
    simp only [Finset.card_univ, Fintype.card_fin] at hLe
    omega
  exact dgCoherentBarCoconeLiftSubsetHom R D F hMC c J k hJ (by rw [hKc] at hk; omega)

def dgCoherentBarCoconeRecoveredRawData {n : ℕ} (c : (sliceUnder F) _⦋n⦌) :
    SimplexData R (RightModule R D) (0 + n + 1) :=
  dgCoherentBarJoinRawData
    (Simplex.vertex (A := R) (dgCoherentBarNormalizedModule R D F hMC)).toSimplexData
    ((sliceUnderProjection F).app (Opposite.op ⦋n⦌) c).toSimplexData
    (dgCoherentBarCoconeRecoveredMixedData R D F hMC c)

end SerrePositivity.InfinityCategories
