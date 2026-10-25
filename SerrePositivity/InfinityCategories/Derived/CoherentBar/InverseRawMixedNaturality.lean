module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawFaceNaturality
/-!
概要：単射な二変数の添字変更について、逆データの全混合成分を比較する。
方針：矩形の像と昇順部分単体のラベルを比較し、混合列の自然性を使う。
規約：実端点と全次数を異種等号で保持する。
使われ方：全部分集合の方程式を回収するための単射自然性。
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
  (hMC : dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

lemma dgCoherentBarInverseRawData_map_mixed_heq {a b n m : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (α : Fin (a + 1) →o Fin (n + 1))
    (β : Fin (b + 1) →o Fin (m + 1)) (hiα : Function.Injective α)
    (hiβ : Function.Injective β)
    (K : Finset (Fin (a + 1))) (L : Finset (Fin (b + 1)))
    (hK : K.Nonempty) (hL : L.Nonempty)
    (c d : Fin (a + b + 1 + 1)) (k : ℤ)
    (hJ : 2 ≤ (dgCoherentBarJoinSubset K L).card)
    (hc : c = (dgCoherentBarJoinSubset K L).min' (Index.nonempty hJ))
    (hd : d = (dgCoherentBarJoinSubset K L).max' (Index.nonempty hJ))
    (hk : k = 2 - ((dgCoherentBarJoinSubset K L).card : ℤ)) :
    HEq ((dgCoherentBarInverseRawData R D F hMC N
      (DGNerve.PinchedHom.LinearData.pullback β f)
      (I.map (SimplexCategory.mkHom α).op s)).hom
      (dgCoherentBarJoinSubset K L) c d k hJ hc hd hk)
      (((dgCoherentBarInverseRawData R D F hMC N f s).pullback
        (dgCoherentBarJoinOrderMap α β)).hom (dgCoherentBarJoinSubset K L) c d k hJ hc hd hk) := by
  let γ := dgCoherentBarJoinOrderMap α β
  let T := dgCoherentBarInverseRawData R D F hMC N f s
  have hiγ : Function.Injective γ := dgCoherentBarJoinOrderMap_injective α β hiα hiβ
  have hImg : (dgCoherentBarJoinSubset K L).image γ =
      dgCoherentBarJoinSubset (K.image α) (L.image β) := dgCoherentBarJoinSubset_map α β K L
  have hCard : (dgCoherentBarJoinSubset (K.image α) (L.image β)).card =
      (dgCoherentBarJoinSubset K L).card := by
    rw [← hImg, Finset.card_image_of_injective _ hiγ]
  have hJ' : 2 ≤ (dgCoherentBarJoinSubset (K.image α) (L.image β)).card := by
    rw [hCard]; exact hJ
  have hc' : γ c = (dgCoherentBarJoinSubset (K.image α) (L.image β)).min'
      (Index.nonempty hJ') := by
    have h := Index.image_min γ.monotone
      (show IsLeast ((dgCoherentBarJoinSubset K L) : Set _) c by
        rw [hc]; exact (dgCoherentBarJoinSubset K L).isLeast_min' _)
      ((Index.nonempty hJ).image γ)
    simpa only [hImg] using h
  have hd' : γ d = (dgCoherentBarJoinSubset (K.image α) (L.image β)).max'
      (Index.nonempty hJ') := by
    have h := Index.image_max γ.monotone
      (show IsGreatest ((dgCoherentBarJoinSubset K L) : Set _) d by
        rw [hd]; exact (dgCoherentBarJoinSubset K L).isGreatest_max' _)
      ((Index.nonempty hJ).image γ)
    simpa only [hImg] using h
  have hk' : k = 2 - ((dgCoherentBarJoinSubset (K.image α) (L.image β)).card : ℤ) := by
    rw [hCard]; exact hk
  let r := K.card - 1
  have hcK : K.card = r + 1 := by have := Finset.card_pos.mpr hK; dsimp [r]; omega
  have hcK' : (K.image α).card = r + 1 := by
    rw [Finset.card_image_of_injective _ hiα]; exact hcK
  let q : ℤ := 1 - (L.card : ℤ)
  have hq' : q = 1 - ((L.image β).card : ℤ) := by
    rw [Finset.card_image_of_injective _ hiβ]
  have hNew := dgCoherentBarInverseRawData_mixed_hom_heq R D F hMC N
    (DGNerve.PinchedHom.LinearData.pullback β f) (I.map (SimplexCategory.mkHom α).op s)
    K L hK hL r hcK q rfl c d k hJ hc hd hk
  have hColumns := dgCoherentBarInverseMixedColumn_reindex R D F hMC N f s α β
    K L hK hL hiα.injOn hiβ.injOn r hcK q rfl
  have hOld := dgCoherentBarInverseRawData_mixed_hom_heq R D F hMC N f s
    (K.image α) (L.image β) (hK.image α) (hL.image β) r hcK' q hq'
    (γ c) (γ d) k hJ' hc' hd' hk'
  have hPull : HEq ((T.pullback γ).hom (dgCoherentBarJoinSubset K L) c d k hJ hc hd hk)
      (T.hom (dgCoherentBarJoinSubset (K.image α) (L.image β))
        (γ c) (γ d) k hJ' hc' hd' hk') := by
    rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hiγ.injOn]
    exact SimplexData.hom_heq_of_indices_degree T hImg rfl rfl rfl
  exact hNew.trans (hColumns.trans (hOld.symm.trans hPull.symm))

lemma dgCoherentBarInverseRawData_map_of_injective {a b n m : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (α : Fin (a + 1) →o Fin (n + 1))
    (β : Fin (b + 1) →o Fin (m + 1)) (hiα : Function.Injective α)
    (hiβ : Function.Injective β) :
    dgCoherentBarInverseRawData R D F hMC N (DGNerve.PinchedHom.LinearData.pullback β f)
      (I.map (SimplexCategory.mkHom α).op s) =
    (dgCoherentBarInverseRawData R D F hMC N f s).pullback
      (dgCoherentBarJoinOrderMap α β) := by
  apply dgCoherentBarJoinSimplexData_ext
  · exact dgCoherentBarInverseRawData_map_left R D F hMC N f s α β
  · exact dgCoherentBarInverseRawData_map_right R D F hMC N f s α β
  · intro K L hK hL c d k hJ hc hd hk
    exact dgCoherentBarInverseRawData_map_mixed_heq R D F hMC N f s α β hiα hiβ
      K L hK hL c d k hJ hc hd hk

end SerrePositivity.InfinityCategories
