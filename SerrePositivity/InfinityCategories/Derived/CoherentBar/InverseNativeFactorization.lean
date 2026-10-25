module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawFactorization
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeSubsetHom
/-!
概要：逆構成の混合成分は、任意のパラメーター係数と native 単体の成分の合成に一致する。
方針：実端点を移送し、部分単体の native 列の既存比較を使う。
規約：任意の線形成分族に適用し、HA 方程式を仮定しない。
使われ方：逆構成の HA 右辺の元の単体側の因数分解。
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
  (N : RightModule R D)

lemma dgCoherentBarInverseRawData_mixed_factorization {m n r l : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌)
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1)))
    (hcK : K.card = r + 1) (hcL : L.card = l + 1) (hK : K.Nonempty)
    (a b : Fin (n + m + 1 + 1)) (k : ℤ)
    (hJ : 2 ≤ (dgCoherentBarJoinSubset K L).card)
    (ha : a = (dgCoherentBarJoinSubset K L).min' (Index.nonempty hJ))
    (hb : b = (dgCoherentBarJoinSubset K L).max' (Index.nonempty hJ))
    (hk : k = 2 - ((dgCoherentBarJoinSubset K L).card : ℤ)) :
    HEq ((dgCoherentBarInverseRawData R D F hMC N f s).hom
      (dgCoherentBarJoinSubset K L) a b k hJ ha hb hk)
      (compose R
        (dgCoherentBarInverseParameterHomAt R D F hMC N f L (-(l : ℤ))
          (Finset.card_pos.mp (by omega)) (by rw [hcL]; push_cast; omega) s)
        ((dgCoherentBarNativeSimplex R D F hMC s).hom (PinchedHom.withLast K)
          (K.min' hK).castSucc (Fin.last (n + 1)) (-(r : ℤ)) (PinchedHom.two_withLast hK)
          (PinchedHom.min_withLast hK _) (PinchedHom.max_withLast K _)
          (by rw [PinchedHom.card_withLast, hcK]; push_cast; omega))
        (show -(r : ℤ) + -(l : ℤ) = -(l : ℤ) - (r : ℤ) by omega)) := by
  have hL : L.Nonempty := Finset.card_pos.mp (by omega)
  have hq : -(l : ℤ) = 1 - (L.card : ℤ) := by rw [hcL]; push_cast; omega
  have hc := gradedHom_compose_heq (A := R) (D := RightModule R D)
    (dgCoherentBarNativeSimplex_subset_source R D F hMC s K r hcK hK)
    (dgCoherentBarNativeSimplex_last R D F hMC s) rfl rfl rfl rfl
    (p := -(r : ℤ)) (q := -(l : ℤ)) (k := -(l : ℤ) - (r : ℤ))
    (p' := -(r : ℤ)) (q' := -(l : ℤ)) (k' := -(l : ℤ) - (r : ℤ))
    (dgCoherentBarInverseParameterHomAt R D F hMC N f L (-(l : ℤ)) hL hq s)
    ((dgCoherentBarNativeSimplex R D F hMC s).hom (PinchedHom.withLast K)
      (K.min' hK).castSucc (Fin.last (n + 1)) (-(r : ℤ)) (PinchedHom.two_withLast hK)
      (PinchedHom.min_withLast hK _) (PinchedHom.max_withLast K _)
      (by rw [PinchedHom.card_withLast, hcK]; push_cast; omega))
    (dgCoherentBarInverseParameterCoefficient f L (-(l : ℤ)) hL hq)
    (dgCoherentBarNativeColumn R D F hMC (dgCoherentBarSubsetLabel s K r hcK))
    (dgCoherentBarInverseParameterHomAt_heq R D F hMC N f L (-(l : ℤ)) hL hq s)
    (dgCoherentBarNativeSimplex_subset_hom_heq R D F hMC s K r hcK hK)
    (by omega) (by omega)
  exact (dgCoherentBarInverseRawData_mixed_hom_heq R D F hMC N f s K L hK hL
    r hcK (-(l : ℤ)) hq a b k hJ ha hb hk).trans hc.symm

end SerrePositivity.InfinityCategories
