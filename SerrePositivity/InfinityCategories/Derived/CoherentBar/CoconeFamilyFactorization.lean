module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyMixedHom
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeSubsetHom
/-!
概要：余錐族の全混合成分を、回収した高次 Hom と正規化 native 成分の合成に同定する。
方針：混合部分単体の係数回収と native 部分単体の係数回収を同じラベルで比較する。
規約：Hom の始域の輸送を明示し、全次数と全高次成分を保つ。
使われ方：HA の削除・切断項を Hom の微分方程式へ因数分解する。
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
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

def dgCoherentBarCoconeFamilyHomAt {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌) (s : I _⦋n⦌) :
    GradedHom R ((dgCoherentBarNativeSimplex R D F hMC s).obj (Fin.last (n + 1)))
      (dgNerve.vertexEquiv R (RightModule R D) y) (-(m : ℤ)) :=
  gradedHomTransport (dgCoherentBarNativeSimplex_last R D F hMC s).symm rfl rfl
    (dgCoherentBarCoconeFamilyHom R D F hMC y c)

lemma dgCoherentBarCoconeFamilyHomAt_heq {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌) (s : I _⦋n⦌) :
    HEq (dgCoherentBarCoconeFamilyHomAt R D F hMC y c s)
      (dgCoherentBarCoconeFamilyHom R D F hMC y c) := gradedHomTransport_heq _ _ _ _

lemma dgCoherentBarCoconeFamilySimplex_mixed_factorization {m n r l : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌) (s : I _⦋n⦌)
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1)))
    (hcK : K.card = r + 1) (hcL : L.card = l + 1) (hK : K.Nonempty)
    (a b : Fin (n + m + 1 + 1)) (k : ℤ)
    (hJ : 2 ≤ (dgCoherentBarJoinSubset K L).card)
    (ha : a = (dgCoherentBarJoinSubset K L).min' (Index.nonempty hJ))
    (hb : b = (dgCoherentBarJoinSubset K L).max' (Index.nonempty hJ))
    (hk : k = 2 - ((dgCoherentBarJoinSubset K L).card : ℤ)) :
    HEq ((dgCoherentBarCoconeFamilySimplex R D F y c s).hom
      (dgCoherentBarJoinSubset K L) a b k hJ ha hb hk)
      (compose R
        (dgCoherentBarCoconeFamilyHomAt R D F hMC y
          ((coconeMappingSpace F y).map (SimplexCategory.mkHom
            (L.orderEmbOfFin hcL).toOrderHom).op c) s)
        ((dgCoherentBarNativeSimplex R D F hMC s).hom (PinchedHom.withLast K)
          (K.min' hK).castSucc (Fin.last (n + 1)) (-(r : ℤ)) (PinchedHom.two_withLast hK)
          (PinchedHom.min_withLast hK _) (PinchedHom.max_withLast K _)
          (by rw [PinchedHom.card_withLast, hcK]; push_cast; omega))
        (show -(r : ℤ) + -(l : ℤ) = -(l : ℤ) - (r : ℤ) by omega)) := by
  let c' := (coconeMappingSpace F y).map
    (SimplexCategory.mkHom (L.orderEmbOfFin hcL).toOrderHom).op c
  have hc := gradedHom_compose_heq (A := R) (D := RightModule R D)
    (dgCoherentBarNativeSimplex_subset_source R D F hMC s K r hcK hK)
    (dgCoherentBarNativeSimplex_last R D F hMC s) rfl rfl rfl rfl
    (p := -(r : ℤ)) (q := -(l : ℤ)) (k := -(l : ℤ) - (r : ℤ))
    (p' := -(r : ℤ)) (q' := -(l : ℤ)) (k' := -(l : ℤ) - (r : ℤ))
    (dgCoherentBarCoconeFamilyHomAt R D F hMC y c' s)
    ((dgCoherentBarNativeSimplex R D F hMC s).hom (PinchedHom.withLast K)
      (K.min' hK).castSucc (Fin.last (n + 1)) (-(r : ℤ)) (PinchedHom.two_withLast hK)
      (PinchedHom.min_withLast hK _) (PinchedHom.max_withLast K _)
      (by rw [PinchedHom.card_withLast, hcK]; push_cast; omega))
    (dgCoherentBarCoconeFamilyHom R D F hMC y c')
    (dgCoherentBarNativeColumn R D F hMC (dgCoherentBarSubsetLabel s K r hcK))
    (dgCoherentBarCoconeFamilyHomAt_heq R D F hMC y c' s)
    (dgCoherentBarNativeSimplex_subset_hom_heq R D F hMC s K r hcK hK)
    (by omega) (by omega)
  rw [dgCoherentBarCoconeFamilyHom_columns] at hc
  exact (dgCoherentBarCoconeFamilySimplex_mixed_hom_heq R D F y c s K L hcK hcL
    a b k hJ ha hb hk).trans hc.symm

end SerrePositivity.InfinityCategories
