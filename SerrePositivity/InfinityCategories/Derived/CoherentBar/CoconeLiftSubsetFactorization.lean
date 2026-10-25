module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredCoordinates
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftFactorization
/-!
概要：持ち上げ余錐の全混合成分を、回収した右部分集合の Hom と native 列に分解する。
方針：混合部分単体の成分回収と native Hom の一意性を合成する。
規約：動く終域の輸送を明示し、全非空部分集合を扱う。
使われ方：パラメーター削除項と切断項を一点下の回収データへ移す。
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

lemma dgCoherentBarCoconeLiftSimplex_subset_factorization {m n r l : ℕ}
    (c : (sliceUnder F) _⦋m⦌) (s : I _⦋n⦌)
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1)))
    (hcK : K.card = r + 1) (hcL : L.card = l + 1) (hL : L.Nonempty)
    (a b : Fin (n + m + 1 + 1)) (k : ℤ)
    (hJ : 2 ≤ (dgCoherentBarJoinSubset K L).card)
    (ha : a = (dgCoherentBarJoinSubset K L).min' (Index.nonempty hJ))
    (hb : b = (dgCoherentBarJoinSubset K L).max' (Index.nonempty hJ))
    (hk : k = 2 - ((dgCoherentBarJoinSubset K L).card : ℤ)) :
    HEq ((dgCoherentBarCoconeLiftSimplex R D F c s).hom
      (dgCoherentBarJoinSubset K L) a b k hJ ha hb hk)
      (compose R
        (x := dgCoherentBarSource R D F (dgCoherentBarSubsetLabel s K r hcK))
        (y := dgCoherentBarNormalizedModule R D F hMC)
        (z := ((sliceUnderProjection F).app (Opposite.op ⦋m⦌) c).obj (L.max' hL))
        (dgCoherentBarCoconeLiftSubsetHom R D F hMC c L (-(l : ℤ)) hL
          (by rw [hcL]; push_cast; omega))
        (dgCoherentBarNativeColumn R D F hMC (dgCoherentBarSubsetLabel s K r hcK))
        (show -(r : ℤ) + -(l : ℤ) = -(l : ℤ) - (r : ℤ) by omega)) := by
  let c' := (sliceUnder F).map (SimplexCategory.mkHom
    (L.orderEmbOfFin hcL).toOrderHom).op c
  let τ := dgCoherentBarSubsetLabel s K r hcK
  have hColumns := dgCoherentBarCoconeLiftHom_columns R D F hMC c' τ
  have hPhi := dgCoherentBarCoconeLiftSubsetHom_heq R D F hMC c L (-(l : ℤ)) hL
    (by rw [hcL]; push_cast; omega) hcL
  have hTarget := dgCoherentBarCoconeLiftTarget_subset R D F c L hcL hL
  have hCompose := gradedHom_compose_heq (A := R) (D := RightModule R D)
    rfl rfl hTarget.symm rfl rfl rfl
    (p := -(r : ℤ)) (q := -(l : ℤ)) (k := -(l : ℤ) - (r : ℤ))
    (p' := -(r : ℤ)) (q' := -(l : ℤ)) (k' := -(l : ℤ) - (r : ℤ))
    (dgCoherentBarCoconeLiftSubsetHom R D F hMC c L (-(l : ℤ)) hL
      (by rw [hcL]; push_cast; omega))
    (dgCoherentBarNativeColumn R D F hMC τ)
    (dgCoherentBarCoconeLiftHom R D F hMC c')
    (dgCoherentBarNativeColumn R D F hMC τ) hPhi HEq.rfl (by omega) (by omega)
  exact (dgCoherentBarCoconeLiftSimplex_mixed_hom_heq R D F c s K L hcK hcL
    a b k hJ ha hb hk).trans ((heq_of_eq hColumns).symm.trans hCompose.symm)

end SerrePositivity.InfinityCategories
