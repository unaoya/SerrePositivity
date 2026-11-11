module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.BianchiLabelPartialNaturality
/-!
概要：正規化余錐の単体は先頭の全単調写像と可換である。
方針：先頭面は元の図式の自然性、末端成分は部分集合上の単射性と退化消滅で比較する。
規約：単射制限だけでなく、元の全ての退化作用を検証する。
使われ方：全 HA 単体を native 余錐へ貼り合わせる。
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
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarNativeSimplexData_last_hom_eq_zero {n : ℕ} (s : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ))
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiLabel s J hJ hb).2 ∈
      I.degenerate (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiLabel s J hJ hb).1) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplexData R D F hMC s).hom
      J a (Fin.last (n + 1)) k hJ ha hb hk = 0 := by
  have hx := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacementObj_of_ne (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F s)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) a (ha ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_ne_last J hJ)).trans
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarBianchiLabel_source R D F s J a hJ ha hb)
  have hy := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacementObj_last (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F s)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
  have hd := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarBianchiLabel_degree s J hJ hb k hk
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplexData_last_hom_heq R D F hMC s J a k hJ ha hb hk
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn_degenerate R D F hMC ⟨_, hs⟩] at h
  exact eq_of_heq (h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := R) (D := RightModule R D)
    hx.symm hy.symm hd.symm))

lemma dgCoherentBarNativeSimplexData_front_pullback {m n : ℕ} (s : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplexData R D F hMC s).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)).pullback Fin.castSuccOrderEmb.toOrderHom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F (I.map (SimplexCategory.mkHom α).op s)).toSimplexData := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_comp]
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α).comp Fin.castSuccOrderEmb.toOrderHom =
      Fin.castSuccOrderEmb.toOrderHom.comp α := by
    apply DFunLike.ext
    intro i
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc α i
  rw [he, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_comp, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplexData_front]
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex_map F α s)).symm

lemma dgCoherentBarNativeSimplexData_map {m n : ℕ} (σ : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplexData R D F hMC (I.map (SimplexCategory.mkHom α).op σ) =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplexData R D F hMC σ).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α) := by
  let τ := I.map (SimplexCategory.mkHom α).op σ
  let β := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α
  let s := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplexData R D F hMC τ
  let t := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplexData R D F hMC σ).pullback β
  have hfront : s.pullback Fin.castSuccOrderEmb.toOrderHom =
      t.pullback Fin.castSuccOrderEmb.toOrderHom :=
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplexData_front R D F hMC τ).trans
      (dgCoherentBarNativeSimplexData_front_pullback R D F hMC σ α).symm
  have hobj : s.obj = t.obj := by
    funext i
    induction i using Fin.lastCases with
    | last =>
      change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex R D F hMC τ).obj (Fin.last (m + 1)) =
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex R D F hMC σ).obj (β (Fin.last (m + 1)))
      rw [show β (Fin.last (m + 1)) = Fin.last (n + 1) from _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last α,
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex_last, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex_last]
    | cast i =>
      exact congrArg (fun u : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (RightModule R D) m => u.obj i) hfront
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext hobj
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise hobj
  intro J a b k hJ ha hb hk
  by_cases hbl : b = Fin.last (m + 1)
  · cases hbl
    by_cases hi : Set.InjOn β (J : Set (Fin (m + 2)))
    · have hK := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hi hJ
      have haK : β a = (J.image β).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hK) :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min β.monotone (by rw [ha]; exact J.isLeast_min' _) _
      have hbK : Fin.last (n + 1) = (J.image β).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hK) := by
        have h : β (Fin.last (m + 1)) = (J.image β).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hK) :=
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max β.monotone (by rw [hb]; exact J.isGreatest_max' _) _
        simpa only [β, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last] using h
      have hkK : k = 2 - ((J.image β).card : ℤ) := by
        rw [Finset.card_image_of_injOn hi]; exact hk
      have hl := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplexData_last_hom_heq R D F hMC τ J a k hJ ha hb hk
      have hr : HEq (t.hom J a (Fin.last (m + 1)) k hJ ha hb hk)
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiLabel σ (J.image β) hK hbK)) := by
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
        refine HEq.trans ?_ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplexData_last_hom_heq R D F hMC σ
          (J.image β) (β a) k hK haK hbK hkK)
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree _ rfl rfl
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last α) rfl
      have hlabel := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarBianchiLabel_map_of_injOn σ α J hJ hb hi hK hbK
      have he := (show ∀ (p q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I), p = q →
          HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC p) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC q) by
        intro p q hpq
        cases hpq
        rfl) _ _ hlabel
      exact hl.trans (he.trans hr.symm)
    · have hLast : Fin.last (m + 1) ∈ J := hb ▸ J.max'_mem _
      have hc : J.card ≠ 2 := by
        intro hc
        have hcard := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withoutLast J hLast
        have hsmall : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J).card ≤ 1 := by omega
        apply hi
        apply (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInjOn_extend_withoutLast_iff α J hLast).mpr
        intro x hx y hy _
        exact Finset.card_le_one.mp hsmall x hx y hy
      have hr : t.hom J a (Fin.last (m + 1)) k hJ ha hb hk = 0 :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc
      have hl := dgCoherentBarNativeSimplexData_last_hom_eq_zero R D F hMC τ J a k hJ ha hb hk
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarBianchiLabel_degenerate_of_not_injOn σ α J hJ hb hi)
      rw [hl, hr]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := R) (D := RightModule R D)
        (congrFun hobj a) (congrFun hobj (Fin.last (m + 1))) rfl
  · have hnot : Fin.last (m + 1) ∉ J := by
      intro hl
      have hle : Fin.last (m + 1) ≤ b := by rw [hb]; exact Finset.le_max' J _ hl
      exact hbl (le_antisymm (Fin.le_last _) hle)
    have hc : (Fin.last (m + 1)).succAboveOrderEmb.toOrderHom =
        Fin.castSuccOrderEmb.toOrderHom := by
      apply DFunLike.ext
      intro i
      exact congrFun Fin.succAbove_last i
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hom_heq_of_face_pullback_eq s t (Fin.last (m + 1))
      (by simpa only [hc] using hfront) J hnot a b k hJ ha hb hk

lemma dgCoherentBarNativeSimplex_map {m n : ℕ} (σ : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex R D F hMC (I.map (SimplexCategory.mkHom α).op σ) =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex R D F hMC σ).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact dgCoherentBarNativeSimplexData_map R D F hMC σ α

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
