module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarBianchiLabelNaturality
public import SerrePositivity.InfinityCategories.DGNerve.FaceHomComparison
public import SerrePositivity.InfinityCategories.DGNerve.PinchedTerms

/-!
概要：実 bar を末端に加えた Bianchi データは、先頭頂点の単射制限と厳密に両立する。
方針：先頭面は元の図式の自然性、末端成分は元の部分単体ラベルの等号で比較する。
規約：MC を仮定せず、全 Hom 成分のデータの等号を得る。
使われ方：全体 HA 右辺の式を任意の末端部分集合へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarBianchiData_front_pullback {m n : ℕ} (σ : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    ((dgCoherentBarBianchiData R D F σ).pullback (PinchedHom.extendOrderHom α)).pullback
      Fin.castSuccOrderEmb.toOrderHom =
      (coherentDiagramSimplex F (I.map (SimplexCategory.mkHom α).op σ)).toSimplexData := by
  rw [SimplexData.pullback_comp]
  have he : (PinchedHom.extendOrderHom α).comp Fin.castSuccOrderEmb.toOrderHom =
      Fin.castSuccOrderEmb.toOrderHom.comp α := by
    apply DFunLike.ext
    intro i
    exact PinchedHom.extendOrderHom_castSucc α i
  rw [he, ← SimplexData.pullback_comp, dgCoherentBarBianchiData_front R D F σ]
  exact (congrArg DGNerve.Simplex.toSimplexData (coherentDiagramSimplex_map F α σ)).symm

lemma dgCoherentBarBianchiData_pullback_last_hom_heq {m n : ℕ} (σ : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α)
    (J : Finset (Fin (m + 2))) (a : Fin (m + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : Fin.last (m + 1) = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ))
    (hK : 2 ≤ (J.image (PinchedHom.extendOrderHom α)).card)
    (haK : PinchedHom.extendOrderHom α a =
      (J.image (PinchedHom.extendOrderHom α)).min' (Index.nonempty hK))
    (hbK : Fin.last (n + 1) = (J.image (PinchedHom.extendOrderHom α)).max' (Index.nonempty hK))
    (hkK : k = 2 - ((J.image (PinchedHom.extendOrderHom α)).card : ℤ)) :
    HEq (((dgCoherentBarBianchiData R D F σ).pullback (PinchedHom.extendOrderHom α)).hom
      J a (Fin.last (m + 1)) k hJ ha hb hk)
      (dgCoherentBarShiftedInclusion R D F
        (dgCoherentBarBianchiLabel σ (J.image (PinchedHom.extendOrderHom α)) hK hbK)) := by
  rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _
    (dgCoherentBarExtend_injective α hα).injOn]
  refine HEq.trans ?_ (dgCoherentBarBianchiData_last_hom_heq R D F σ
    (J.image (PinchedHom.extendOrderHom α)) (PinchedHom.extendOrderHom α a) k hK haK hbK hkK)
  exact SimplexData.hom_heq_of_indices_degree _ rfl rfl (PinchedHom.extendOrderHom_last α) rfl

lemma dgCoherentBarBianchiData_map {m n : ℕ} (σ : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α) :
    dgCoherentBarBianchiData R D F (I.map (SimplexCategory.mkHom α).op σ) =
      (dgCoherentBarBianchiData R D F σ).pullback (PinchedHom.extendOrderHom α) := by
  let τ := I.map (SimplexCategory.mkHom α).op σ
  let β := PinchedHom.extendOrderHom α
  let s := dgCoherentBarBianchiData R D F τ
  let t := (dgCoherentBarBianchiData R D F σ).pullback β
  have hfront : s.pullback Fin.castSuccOrderEmb.toOrderHom =
      t.pullback Fin.castSuccOrderEmb.toOrderHom :=
    (dgCoherentBarBianchiData_front R D F τ).trans
      (dgCoherentBarBianchiData_front_pullback R D F σ α).symm
  have hobj : s.obj = t.obj := by
    funext i
    induction i using Fin.lastCases with
    | last =>
      change (dgCoherentBarBianchiData R D F τ).obj (Fin.last (m + 1)) =
        (dgCoherentBarBianchiData R D F σ).obj (β (Fin.last (m + 1)))
      rw [show β (Fin.last (m + 1)) = Fin.last (n + 1) from PinchedHom.extendOrderHom_last α]
      exact (dgCoherentBarBianchiData_obj_last R D F τ).trans
        (dgCoherentBarBianchiData_obj_last R D F σ).symm
    | cast i =>
      exact congrArg (fun u : SimplexData R (RightModule R D) m => u.obj i) hfront
  apply SimplexData.ext hobj
  apply HomFamily.heq_of_pointwise hobj
  intro J a b k hJ ha hb hk
  by_cases hbLast : b = Fin.last (m + 1)
  · cases hbLast
    have hβ := dgCoherentBarExtend_injective α hα
    have hK := Index.image_two hβ.injOn hJ
    have haK : β a = (J.image β).min' (Index.nonempty hK) :=
      Index.image_min β.monotone (by rw [ha]; exact J.isLeast_min' _) (Index.nonempty hK)
    have hbK : Fin.last (n + 1) = (J.image β).max' (Index.nonempty hK) := by
      have hh : β (Fin.last (m + 1)) = (J.image β).max' (Index.nonempty hK) :=
        Index.image_max β.monotone (by rw [hb]; exact J.isGreatest_max' _) (Index.nonempty hK)
      simpa only [β, PinchedHom.extendOrderHom_last] using hh
    have hkK : k = 2 - ((J.image β).card : ℤ) := by
      rw [Finset.card_image_of_injective _ hβ]
      exact hk
    have hl := dgCoherentBarBianchiData_last_hom_heq R D F τ J a k hJ ha hb hk
    have hr := dgCoherentBarBianchiData_pullback_last_hom_heq R D F σ α hα
      J a k hJ ha hb hk hK haK hbK hkK
    have hlabel := dgCoherentBarBianchiLabel_map σ α hα J hJ hb hK hbK
    have hi := (show ∀ (p q : dgCoherentBarIndex I), p = q →
        HEq (dgCoherentBarShiftedInclusion R D F p) (dgCoherentBarShiftedInclusion R D F q) by
      intro p q hpq
      cases hpq
      rfl) _ _ hlabel
    exact hl.trans (hi.trans hr.symm)
  · have hnot : Fin.last (m + 1) ∉ J := by
      intro hLast
      have hle : Fin.last (m + 1) ≤ b := by rw [hb]; exact Finset.le_max' J _ hLast
      exact hbLast (le_antisymm (Fin.le_last _) hle)
    have hc : (Fin.last (m + 1)).succAboveOrderEmb.toOrderHom =
        Fin.castSuccOrderEmb.toOrderHom := by
      apply DFunLike.ext
      intro i
      exact congrFun Fin.succAbove_last i
    exact SimplexData.hom_heq_of_face_pullback_eq s t (Fin.last (m + 1))
      (by simpa only [hc] using hfront) J hnot a b k hJ ha hb hk

end SerrePositivity.InfinityCategories
