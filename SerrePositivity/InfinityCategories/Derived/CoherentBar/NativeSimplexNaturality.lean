module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.BianchiLabelPartialNaturality
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarNativeSimplexData_last_hom_eq_zero {n : ℕ} (s : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ))
    (hs : (dgCoherentBarBianchiLabel s J hJ hb).2 ∈
      I.degenerate (dgCoherentBarBianchiLabel s J hJ hb).1) :
    (dgCoherentBarNativeSimplexData R D F hMC s).hom
      J a (Fin.last (n + 1)) k hJ ha hb hk = 0 := by
  have hx := (SimplexData.lastReplacementObj_of_ne (dgCoherentBarBianchiData R D F s)
    (dgCoherentBarNormalizedModule R D F hMC) a (ha ▸ PinchedHom.min_ne_last J hJ)).trans
    (dgCoherentBarBianchiLabel_source R D F s J a hJ ha hb)
  have hy := SimplexData.lastReplacementObj_last (dgCoherentBarBianchiData R D F s)
    (dgCoherentBarNormalizedModule R D F hMC)
  have hd := dgCoherentBarBianchiLabel_degree s J hJ hb k hk
  have h := dgCoherentBarNativeSimplexData_last_hom_heq R D F hMC s J a k hJ ha hb hk
  rw [dgCoherentBarNativeColumn_degenerate R D F hMC ⟨_, hs⟩] at h
  exact eq_of_heq (h.trans (gradedHom_zero_heq (A := R) (D := RightModule R D)
    hx.symm hy.symm hd.symm))

lemma dgCoherentBarNativeSimplexData_front_pullback {m n : ℕ} (s : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    ((dgCoherentBarNativeSimplexData R D F hMC s).pullback
      (PinchedHom.extendOrderHom α)).pullback Fin.castSuccOrderEmb.toOrderHom =
    (coherentDiagramSimplex F (I.map (SimplexCategory.mkHom α).op s)).toSimplexData := by
  rw [SimplexData.pullback_comp]
  have he : (PinchedHom.extendOrderHom α).comp Fin.castSuccOrderEmb.toOrderHom =
      Fin.castSuccOrderEmb.toOrderHom.comp α := by
    apply DFunLike.ext
    intro i
    exact PinchedHom.extendOrderHom_castSucc α i
  rw [he, ← SimplexData.pullback_comp, dgCoherentBarNativeSimplexData_front]
  exact (congrArg DGNerve.Simplex.toSimplexData (coherentDiagramSimplex_map F α s)).symm

lemma dgCoherentBarNativeSimplexData_map {m n : ℕ} (σ : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    dgCoherentBarNativeSimplexData R D F hMC (I.map (SimplexCategory.mkHom α).op σ) =
      (dgCoherentBarNativeSimplexData R D F hMC σ).pullback (PinchedHom.extendOrderHom α) := by
  let τ := I.map (SimplexCategory.mkHom α).op σ
  let β := PinchedHom.extendOrderHom α
  let s := dgCoherentBarNativeSimplexData R D F hMC τ
  let t := (dgCoherentBarNativeSimplexData R D F hMC σ).pullback β
  have hfront : s.pullback Fin.castSuccOrderEmb.toOrderHom =
      t.pullback Fin.castSuccOrderEmb.toOrderHom :=
    (dgCoherentBarNativeSimplexData_front R D F hMC τ).trans
      (dgCoherentBarNativeSimplexData_front_pullback R D F hMC σ α).symm
  have hobj : s.obj = t.obj := by
    funext i
    induction i using Fin.lastCases with
    | last =>
      change (dgCoherentBarNativeSimplex R D F hMC τ).obj (Fin.last (m + 1)) =
        (dgCoherentBarNativeSimplex R D F hMC σ).obj (β (Fin.last (m + 1)))
      rw [show β (Fin.last (m + 1)) = Fin.last (n + 1) from PinchedHom.extendOrderHom_last α,
        dgCoherentBarNativeSimplex_last, dgCoherentBarNativeSimplex_last]
    | cast i =>
      exact congrArg (fun u : SimplexData R (RightModule R D) m => u.obj i) hfront
  apply SimplexData.ext hobj
  apply HomFamily.heq_of_pointwise hobj
  intro J a b k hJ ha hb hk
  by_cases hbl : b = Fin.last (m + 1)
  · cases hbl
    by_cases hi : Set.InjOn β (J : Set (Fin (m + 2)))
    · have hK := Index.image_two hi hJ
      have haK : β a = (J.image β).min' (Index.nonempty hK) :=
        Index.image_min β.monotone (by rw [ha]; exact J.isLeast_min' _) _
      have hbK : Fin.last (n + 1) = (J.image β).max' (Index.nonempty hK) := by
        have h : β (Fin.last (m + 1)) = (J.image β).max' (Index.nonempty hK) :=
          Index.image_max β.monotone (by rw [hb]; exact J.isGreatest_max' _) _
        simpa only [β, PinchedHom.extendOrderHom_last] using h
      have hkK : k = 2 - ((J.image β).card : ℤ) := by
        rw [Finset.card_image_of_injOn hi]; exact hk
      have hl := dgCoherentBarNativeSimplexData_last_hom_heq R D F hMC τ J a k hJ ha hb hk
      have hr : HEq (t.hom J a (Fin.last (m + 1)) k hJ ha hb hk)
          (dgCoherentBarNativeColumn R D F hMC
            (dgCoherentBarBianchiLabel σ (J.image β) hK hbK)) := by
        rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
        refine HEq.trans ?_ (dgCoherentBarNativeSimplexData_last_hom_heq R D F hMC σ
          (J.image β) (β a) k hK haK hbK hkK)
        exact SimplexData.hom_heq_of_indices_degree _ rfl rfl
          (PinchedHom.extendOrderHom_last α) rfl
      have hlabel := dgCoherentBarBianchiLabel_map_of_injOn σ α J hJ hb hi hK hbK
      have he := (show ∀ (p q : dgCoherentBarIndex I), p = q →
          HEq (dgCoherentBarNativeColumn R D F hMC p) (dgCoherentBarNativeColumn R D F hMC q) by
        intro p q hpq
        cases hpq
        rfl) _ _ hlabel
      exact hl.trans (he.trans hr.symm)
    · have hLast : Fin.last (m + 1) ∈ J := hb ▸ J.max'_mem _
      have hc : J.card ≠ 2 := by
        intro hc
        have hcard := PinchedHom.card_withoutLast J hLast
        have hsmall : (PinchedHom.withoutLast J).card ≤ 1 := by omega
        apply hi
        apply (dgCoherentBarInjOn_extend_withoutLast_iff α J hLast).mpr
        intro x hx y hy _
        exact Finset.card_le_one.mp hsmall x hx y hy
      have hr : t.hom J a (Fin.last (m + 1)) k hJ ha hb hk = 0 :=
        SimplexData.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc
      have hl := dgCoherentBarNativeSimplexData_last_hom_eq_zero R D F hMC τ J a k hJ ha hb hk
        (dgCoherentBarBianchiLabel_degenerate_of_not_injOn σ α J hJ hb hi)
      rw [hl, hr]
      exact gradedHom_zero_heq (A := R) (D := RightModule R D)
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
    exact SimplexData.hom_heq_of_face_pullback_eq s t (Fin.last (m + 1))
      (by simpa only [hc] using hfront) J hnot a b k hJ ha hb hk

lemma dgCoherentBarNativeSimplex_map {m n : ℕ} (σ : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    dgCoherentBarNativeSimplex R D F hMC (I.map (SimplexCategory.mkHom α).op σ) =
      (dgCoherentBarNativeSimplex R D F hMC σ).pullback (PinchedHom.extendOrderHom α) := by
  apply DGNerve.Simplex.ext
  exact dgCoherentBarNativeSimplexData_map R D F hMC σ α

end SerrePositivity.InfinityCategories
