module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarBianchiLabelNaturality
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FaceHomComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedTerms

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarBianchiData_front_pullback {m n : ℕ} (σ : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)).pullback
      Fin.castSuccOrderEmb.toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F (I.map (SimplexCategory.mkHom α).op σ)).toSimplexData := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_comp]
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α).comp Fin.castSuccOrderEmb.toOrderHom =
      Fin.castSuccOrderEmb.toOrderHom.comp α := by
    apply DFunLike.ext
    intro i
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc α i
  rw [he, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_front R D F σ]
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex_map F α σ)).symm

lemma dgCoherentBarBianchiData_pullback_last_hom_heq {m n : ℕ} (σ : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α)
    (J : Finset (Fin (m + 2))) (a : Fin (m + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : Fin.last (m + 1) = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ))
    (hK : 2 ≤ (J.image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)).card)
    (haK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α a =
      (J.image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hK))
    (hbK : Fin.last (n + 1) = (J.image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hK))
    (hkK : k = 2 - ((J.image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)).card : ℤ)) :
    HEq (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)).hom
      J a (Fin.last (m + 1)) k hJ ha hb hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion R D F
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiLabel σ (J.image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)) hK hbK)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarExtend_injective α hα).injOn]
  refine HEq.trans ?_ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_last_hom_heq R D F σ
    (J.image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α a) k hK haK hbK hkK)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree _ rfl rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last α) rfl

lemma dgCoherentBarBianchiData_map {m n : ℕ} (σ : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F (I.map (SimplexCategory.mkHom α).op σ) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α) := by
  let τ := I.map (SimplexCategory.mkHom α).op σ
  let β := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α
  let s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F τ
  let t := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).pullback β
  have hfront : s.pullback Fin.castSuccOrderEmb.toOrderHom =
      t.pullback Fin.castSuccOrderEmb.toOrderHom :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_front R D F τ).trans
      (dgCoherentBarBianchiData_front_pullback R D F σ α).symm
  have hobj : s.obj = t.obj := by
    funext i
    induction i using Fin.lastCases with
    | last =>
      change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F τ).obj (Fin.last (m + 1)) =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).obj (β (Fin.last (m + 1)))
      rw [show β (Fin.last (m + 1)) = Fin.last (n + 1) from _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last α]
      exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_obj_last R D F τ).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_obj_last R D F σ).symm
    | cast i =>
      exact congrArg (fun u : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (RightModule R D) m => u.obj i) hfront
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext hobj
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise hobj
  intro J a b k hJ ha hb hk
  by_cases hbLast : b = Fin.last (m + 1)
  · cases hbLast
    have hβ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarExtend_injective α hα
    have hK := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hβ.injOn hJ
    have haK : β a = (J.image β).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hK) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min β.monotone (by rw [ha]; exact J.isLeast_min' _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hK)
    have hbK : Fin.last (n + 1) = (J.image β).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hK) := by
      have hh : β (Fin.last (m + 1)) = (J.image β).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hK) :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max β.monotone (by rw [hb]; exact J.isGreatest_max' _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hK)
      simpa only [β, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last] using hh
    have hkK : k = 2 - ((J.image β).card : ℤ) := by
      rw [Finset.card_image_of_injective _ hβ]
      exact hk
    have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_last_hom_heq R D F τ J a k hJ ha hb hk
    have hr := dgCoherentBarBianchiData_pullback_last_hom_heq R D F σ α hα
      J a k hJ ha hb hk hK haK hbK hkK
    have hlabel := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiLabel_map σ α hα J hJ hb hK hbK
    have hi := (show ∀ (p q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I), p = q →
        HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion R D F p) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion R D F q) by
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
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hom_heq_of_face_pullback_eq s t (Fin.last (m + 1))
      (by simpa only [hc] using hfront) J hnot a b k hJ ha hb hk

end SerrePositivity.InfinityCategories.Project.DerivedCategories
