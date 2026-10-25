module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeDegenerateColumns
/-!
概要：任意の native 余錐の全部分集合成分を、同じ部分単体の最上係数へ戻す。
方針：先頭集合の昇順列挙と末端を加えた単射自然性を使う。
規約：全端点と次数を異種等号で保持する。
使われ方：Hom の逆像が余錐の全 HA 成分を厳密に回収することの検証。
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

lemma dgCoherentBarCoconeSimplex_last_hom_heq (c : JoinCocone F) {n : ℕ} (s : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)) :
    HEq ((dgCoherentBarCoconeSimplex R D F c s).hom
      J a (Fin.last (n + 1)) k hJ ha hb hk)
      (dgCoherentBarCoconeColumn R D F c (dgCoherentBarBianchiLabel s J hJ hb)) := by
  have hl : Fin.last (n + 1) ∈ J := hb ▸ J.max'_mem _
  let K := PinchedHom.withoutLast J
  have hK : K.Nonempty := PinchedHom.withoutLast_nonempty hJ hl
  let r := K.card - 1
  have hc : K.card = r + 1 := by have := Finset.card_pos.mpr hK; dsimp [r]; omega
  let α := (K.orderEmbOfFin hc).toOrderHom
  let β := PinchedHom.extendOrderHom α
  let τ := I.map (SimplexCategory.mkHom α).op s
  have hβ : Function.Injective β := dgCoherentBarExtend_injective α (K.orderEmbOfFin hc).injective
  have him : (Finset.univ : Finset (Fin (r + 2))).image β = J := by
    rw [← dgCoherentBar_withLast_univ r, PinchedHom.image_withLast_extend]
    change PinchedHom.withLast ((Finset.univ : Finset (Fin (r + 1))).image
      (K.orderEmbOfFin hc)) = J
    rw [K.image_orderEmbOfFin_univ hc]
    exact PinchedHom.withLast_withoutLast J hl
  have hA : β 0 = a := by
    rw [ha]
    have h0 : IsLeast ((Finset.univ : Finset (Fin (r + 2))) : Set (Fin (r + 2))) 0 :=
      ⟨Finset.mem_univ _, fun i _ => Fin.zero_le i⟩
    simpa only [him] using Index.image_min β.monotone h0
      (Finset.Nonempty.image Finset.univ_nonempty β)
  have hkr : k = -(r : ℤ) := by
    have hh := PinchedHom.card_withoutLast J hl
    change J.card = K.card + 1 at hh
    omega
  have hNat := congrArg DGNerve.Simplex.toSimplexData
    (dgCoherentBarCoconeSimplex_map R D F c s α)
  change (dgCoherentBarCoconeSimplex R D F c τ).toSimplexData =
    (dgCoherentBarCoconeSimplex R D F c s).toSimplexData.pullback β at hNat
  have hHom := SimplexData.hom_heq_of_eq hNat Finset.univ 0 (Fin.last (r + 1))
    (-(r : ℤ)) (coherentDiagramTop_card r) (coherentDiagramTop_min r)
    (coherentDiagramTop_max r) (by simp; omega)
  rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hβ.injOn] at hHom
  have hAny : HEq ((dgCoherentBarCoconeSimplex R D F c s).hom
      J a (Fin.last (n + 1)) k hJ ha hb hk)
      ((dgCoherentBarCoconeSimplex R D F c τ).hom
        Finset.univ 0 (Fin.last (r + 1)) (-(r : ℤ)) (coherentDiagramTop_card r)
        (coherentDiagramTop_min r) (coherentDiagramTop_max r) (by simp; omega)) := by
    refine HEq.trans ?_ hHom.symm
    exact SimplexData.hom_heq_of_indices_degree _ him.symm hA.symm
      (PinchedHom.extendOrderHom_last α).symm hkr
  refine hAny.trans ?_
  exact (gradedHomTransport_heq (A := R) (D := RightModule R D)
    (dgCoherentBarCoconeSimplex_source R D F c τ)
    (dgCoherentBarCoconeSimplex_last R D F c τ) rfl _).symm

end SerrePositivity.InfinityCategories
