module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredFaceNaturality
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinPartialInjectivity
/-!
概要：回収した一点下のデータの混合成分は、右部分集合上で単射な全添字変更に自然である。
方針：矩形の像と回収 Hom の部分集合自然性を比較する。
規約：大域的単射性は要求せず、実端点を異種等号で保持する。
使われ方：全部分集合の HA 方程式の移送と、全自然性の単射分岐。
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

lemma dgCoherentBarCoconeRecoveredRawData_map_mixed_of_injOn {m n : ℕ}
    (c : (sliceUnder F) _⦋n⦌) (α : Fin (m + 1) →o Fin (n + 1))
    (K : Finset (Fin 1)) (L : Finset (Fin (m + 1))) (hK : K.Nonempty) (hL : L.Nonempty)
    (hiL : Set.InjOn α (L : Set (Fin (m + 1))))
    (a b : Fin (0 + m + 1 + 1)) (k : ℤ)
    (hJ : 2 ≤ (dgCoherentBarJoinSubset K L).card)
    (ha : a = (dgCoherentBarJoinSubset K L).min' (Index.nonempty hJ))
    (hb : b = (dgCoherentBarJoinSubset K L).max' (Index.nonempty hJ))
    (hk : k = 2 - ((dgCoherentBarJoinSubset K L).card : ℤ)) :
    HEq ((dgCoherentBarCoconeRecoveredRawData R D F hMC
      ((sliceUnder F).map (SimplexCategory.mkHom α).op c)).hom
      (dgCoherentBarJoinSubset K L) a b k hJ ha hb hk)
      (((dgCoherentBarCoconeRecoveredRawData R D F hMC c).pullback
        (dgCoherentBarJoinOrderMap (OrderHom.id : Fin 1 →o Fin 1) α)).hom
        (dgCoherentBarJoinSubset K L) a b k hJ ha hb hk) := by
  have hK0 := dgCoherentBarFinOneSubset_eq_univ K hK
  subst K
  let γ := dgCoherentBarJoinOrderMap (OrderHom.id : Fin 1 →o Fin 1) α
  let Q := dgCoherentBarCoconeRecoveredRawData R D F hMC c
  have hiγ : Set.InjOn γ
      ((dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) L) : Set _) :=
    (dgCoherentBarJoinOrderMap_injOn_subset_iff (OrderHom.id : Fin 1 →o Fin 1)
      α Finset.univ L).mpr ⟨Function.injective_id.injOn, hiL⟩
  have hImg : (dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) L).image γ =
      dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) (L.image α) := by
    have hid : (Finset.univ : Finset (Fin 1)).image (OrderHom.id : Fin 1 →o Fin 1) =
        Finset.univ := by
      change (Finset.univ : Finset (Fin 1)).image id = Finset.univ
      exact Finset.image_id
    simpa only [hid] using
      dgCoherentBarJoinSubset_map (OrderHom.id : Fin 1 →o Fin 1) α Finset.univ L
  have hCard : (dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) (L.image α)).card =
      (dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) L).card := by
    rw [← hImg, Finset.card_image_of_injOn hiγ]
  have hJ' : 2 ≤ (dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) (L.image α)).card := by
    rw [hCard]
    exact hJ
  have ha' : γ a = (dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1))
      (L.image α)).min' (Index.nonempty hJ') := by
    have h := Index.image_min γ.monotone
      (show IsLeast ((dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) L) : Set _) a by
        rw [ha]; exact (dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) L).isLeast_min' _)
      ((Index.nonempty hJ).image γ)
    simpa only [hImg] using h
  have hb' : γ b = (dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1))
      (L.image α)).max' (Index.nonempty hJ') := by
    have h := Index.image_max γ.monotone
      (show IsGreatest ((dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) L) : Set _) b by
        rw [hb]; exact (dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) L).isGreatest_max' _)
      ((Index.nonempty hJ).image γ)
    simpa only [hImg] using h
  have hk' : k = 2 - ((dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1))
      (L.image α)).card : ℤ) := by rw [hCard]; exact hk
  have hkL : k = 1 - (L.card : ℤ) := by
    rw [dgCoherentBarJoinSubset_card] at hk
    simp only [Finset.card_univ, Fintype.card_fin] at hk
    omega
  have hNew := dgCoherentBarCoconeRecoveredRawData_mixed_hom_heq R D F hMC
    ((sliceUnder F).map (SimplexCategory.mkHom α).op c) L hL a b k hJ ha hb hk
  have hColumns := dgCoherentBarCoconeLiftSubsetHom_map_of_injOn R D F hMC c α L k hL hkL hiL
  have hOld := dgCoherentBarCoconeRecoveredRawData_mixed_hom_heq R D F hMC c
    (L.image α) (hL.image α) (γ a) (γ b) k hJ' ha' hb' hk'
  have hPull : HEq ((Q.pullback γ).hom (dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) L)
      a b k hJ ha hb hk)
      (Q.hom (dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) (L.image α))
        (γ a) (γ b) k hJ' ha' hb' hk') := by
    rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hiγ]
    exact SimplexData.hom_heq_of_indices_degree Q hImg rfl rfl rfl
  exact hNew.trans (hColumns.trans (hOld.symm.trans hPull.symm))

end SerrePositivity.InfinityCategories
