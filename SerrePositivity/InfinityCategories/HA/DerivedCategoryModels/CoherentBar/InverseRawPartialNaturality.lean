module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinPartialInjectivity
/-!
概要：部分集合上だけの単射性から、逆データの混合成分の自然性を証明する。
方針：矩形上の単射性を左右へ分解し、像の濃度と係数の移送を比較する。
規約：全体で単射でない写像も許す。
使われ方：全ての退化を含む二変数自然性の単射分岐。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

lemma dgCoherentBarInverseRawData_map_mixed_of_injOn {a b n m : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (α : Fin (a + 1) →o Fin (n + 1))
    (β : Fin (b + 1) →o Fin (m + 1))
    (K : Finset (Fin (a + 1))) (L : Finset (Fin (b + 1)))
    (hK : K.Nonempty) (hL : L.Nonempty)
    (hiK : Set.InjOn α (K : Set (Fin (a + 1))))
    (hiL : Set.InjOn β (L : Set (Fin (b + 1))))
    (c d : Fin (a + b + 1 + 1)) (k : ℤ)
    (hJ : 2 ≤ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).card)
    (hc : c = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hd : d = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback β f)
      (I.map (SimplexCategory.mkHom α).op s)).hom
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L) c d k hJ hc hd hk)
      (((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s).pullback
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap α β)).hom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L) c d k hJ hc hd hk) := by
  let γ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap α β
  let T := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s
  have hiγ : Set.InjOn γ ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L) : Set _) :=
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap_injOn_subset_iff α β K L).mpr ⟨hiK, hiL⟩
  have hImg : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).image γ =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (K.image α) (L.image β) := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_map α β K L
  have hCard : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (K.image α) (L.image β)).card =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).card := by
    rw [← hImg, Finset.card_image_of_injOn hiγ]
  have hJ' : 2 ≤ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (K.image α) (L.image β)).card := by
    rw [hCard]; exact hJ
  have hc' : γ c = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (K.image α) (L.image β)).min'
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ') := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min γ.monotone
      (show IsLeast ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L) : Set _) c by
        rw [hc]; exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).isLeast_min' _)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ).image γ)
    simpa only [hImg] using h
  have hd' : γ d = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (K.image α) (L.image β)).max'
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ') := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max γ.monotone
      (show IsGreatest ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L) : Set _) d by
        rw [hd]; exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).isGreatest_max' _)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ).image γ)
    simpa only [hImg] using h
  have hk' : k = 2 - ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (K.image α) (L.image β)).card : ℤ) := by
    rw [hCard]; exact hk
  let r := K.card - 1
  have hcK : K.card = r + 1 := by have := Finset.card_pos.mpr hK; dsimp [r]; omega
  have hcK' : (K.image α).card = r + 1 := by
    rw [Finset.card_image_of_injOn hiK]; exact hcK
  let q : ℤ := 1 - (L.card : ℤ)
  have hq' : q = 1 - ((L.image β).card : ℤ) := by
    rw [Finset.card_image_of_injOn hiL]
  have hNew := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_mixed_hom_heq R D F hMC N
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback β f) (I.map (SimplexCategory.mkHom α).op s)
    K L hK hL r hcK q rfl c d k hJ hc hd hk
  have hColumns := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseMixedColumn_reindex R D F hMC N f s α β
    K L hK hL hiK hiL r hcK q rfl
  have hOld := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_mixed_hom_heq R D F hMC N f s
    (K.image α) (L.image β) (hK.image α) (hL.image β) r hcK' q hq'
    (γ c) (γ d) k hJ' hc' hd' hk'
  have hPull : HEq ((T.pullback γ).hom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L) c d k hJ hc hd hk)
      (T.hom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (K.image α) (L.image β))
        (γ c) (γ d) k hJ' hc' hd' hk') := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hiγ]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree T hImg rfl rfl rfl
  exact hNew.trans (hColumns.trans (hOld.symm.trans hPull.symm))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
