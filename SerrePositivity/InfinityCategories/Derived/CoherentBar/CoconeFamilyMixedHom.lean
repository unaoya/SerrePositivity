module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinMixedIndex
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyDifferential
/-!
概要：高次余錐族の混合部分集合の成分を、左右の部分単体の最上成分として回収する。
方針：二つの昇順列挙を join し、単射引き戻しの HA 成分を比較する。
規約：始域・終域・次数を異種等号で保ち、全ての混合部分集合を対象にする。
使われ方：Hom 逆構成による余錐族の全 HA 成分の復元。
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
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarCoconeFamilySimplex_mixed_hom_heq {m n r l : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌) (s : I _⦋n⦌)
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1)))
    (hK : K.card = r + 1) (hL : L.card = l + 1)
    (a b : Fin (n + m + 1 + 1)) (k : ℤ)
    (hJ : 2 ≤ (dgCoherentBarJoinSubset K L).card)
    (ha : a = (dgCoherentBarJoinSubset K L).min' (Index.nonempty hJ))
    (hb : b = (dgCoherentBarJoinSubset K L).max' (Index.nonempty hJ))
    (hk : k = 2 - ((dgCoherentBarJoinSubset K L).card : ℤ)) :
    HEq ((dgCoherentBarCoconeFamilySimplex R D F y c s).hom
      (dgCoherentBarJoinSubset K L) a b k hJ ha hb hk)
      (dgCoherentBarCoconeFamilyColumn R D F y
        ((coconeMappingSpace F y).map (SimplexCategory.mkHom
          (L.orderEmbOfFin hL).toOrderHom).op c)
        ⟨r, I.map (SimplexCategory.mkHom (K.orderEmbOfFin hK).toOrderHom).op s⟩) := by
  let α := (K.orderEmbOfFin hK).toOrderHom
  let β := (L.orderEmbOfFin hL).toOrderHom
  let γ := dgCoherentBarJoinOrderMap α β
  let τ := I.map (SimplexCategory.mkHom α).op s
  let c' := (coconeMappingSpace F y).map (SimplexCategory.mkHom β).op c
  have hγ : Function.Injective γ := dgCoherentBarJoinOrderMap_injective α β
    (K.orderEmbOfFin hK).injective (L.orderEmbOfFin hL).injective
  have him : (Finset.univ : Finset (Fin (r + l + 1 + 1))).image γ =
      dgCoherentBarJoinSubset K L := by
    rw [← dgCoherentBarJoinSubset_univ r l, dgCoherentBarJoinSubset_map]
    change dgCoherentBarJoinSubset
      (Finset.univ.image (K.orderEmbOfFin hK))
      (Finset.univ.image (L.orderEmbOfFin hL)) = _
    rw [K.image_orderEmbOfFin_univ hK, L.image_orderEmbOfFin_univ hL]
  have hA : γ 0 = a := by
    rw [ha]
    have h0 : IsLeast
        ((Finset.univ : Finset (Fin (r + l + 1 + 1))) : Set (Fin (r + l + 1 + 1))) 0 :=
      ⟨Finset.mem_univ _, fun i _ => Fin.zero_le i⟩
    simpa only [him] using Index.image_min γ.monotone h0
      (Finset.Nonempty.image Finset.univ_nonempty γ)
  have hB : γ (Fin.last (r + l + 1)) = b := by
    rw [hb]
    have hlast : IsGreatest
        ((Finset.univ : Finset (Fin (r + l + 1 + 1))) : Set (Fin (r + l + 1 + 1)))
        (Fin.last (r + l + 1)) := ⟨Finset.mem_univ _, fun i _ => Fin.le_last i⟩
    simpa only [him] using Index.image_max γ.monotone hlast
      (Finset.Nonempty.image Finset.univ_nonempty γ)
  have hkr : k = -(l : ℤ) - (r : ℤ) := by
    rw [dgCoherentBarJoinSubset_card, hK, hL] at hk
    push_cast at hk
    omega
  have hNat := congrArg DGNerve.Simplex.toSimplexData
    (dgCoherentBarCoconeFamilySimplex_map R D F y c s
      (SimplexCategory.mkHom α) (SimplexCategory.mkHom β))
  change (dgCoherentBarCoconeFamilySimplex R D F y c' τ).toSimplexData =
    (dgCoherentBarCoconeFamilySimplex R D F y c s).toSimplexData.pullback γ at hNat
  have hHom := SimplexData.hom_heq_of_eq hNat Finset.univ 0 (Fin.last (r + l + 1))
    (-(l : ℤ) - (r : ℤ)) (coherentDiagramTop_card (r + l))
    (coherentDiagramTop_min (r + l)) (coherentDiagramTop_max (r + l)) (by simp; omega)
  rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hγ.injOn] at hHom
  have hAny : HEq ((dgCoherentBarCoconeFamilySimplex R D F y c s).hom
      (dgCoherentBarJoinSubset K L) a b k hJ ha hb hk)
      ((dgCoherentBarCoconeFamilySimplex R D F y c' τ).hom
        Finset.univ 0 (Fin.last (r + l + 1)) (-(l : ℤ) - (r : ℤ))
        (coherentDiagramTop_card (r + l)) (coherentDiagramTop_min (r + l))
        (coherentDiagramTop_max (r + l)) (by simp; omega)) := by
    refine HEq.trans ?_ hHom.symm
    exact SimplexData.hom_heq_of_indices_degree _ him.symm hA.symm hB.symm hkr
  refine hAny.trans ?_
  exact (gradedHomTransport_heq (A := R) (D := RightModule R D)
    (dgCoherentBarCoconeFamilySimplex_source R D F y c' τ)
    (dgCoherentBarCoconeFamilySimplex_target R D F y c' τ) rfl _).symm

end SerrePositivity.InfinityCategories
