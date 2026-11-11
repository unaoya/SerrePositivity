module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.PuncturedFaceAnodyne
public import Mathlib.Data.Finset.Max

/-!
概要：元の面の下方閉じた有限族を、実際の内角ホーン貼付けの有限合成として構成する。
方針：頂点数が最大の元の面を除いて帰納し、同じ元の pushout で最後の面を戻す。
規約：全ての段階の元の包含を保持し、同値な別の包含で置き換えない。
使われ方：HTT 4.4.5.8 の有限貼付けの合成。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 指定面と内点を含む下方閉じた有限族への元の段階包含は inner anodyne。 -/
lemma missingFaceStage_innerAnodyne {n : ℕ} (J : Finset (Fin (n + 1)))
    (j i k : Fin (n + 1)) (hj : j ∉ J) (hi : i ∈ J) (hk : k ∈ J)
    (hij : i < j) (hjk : j < k)
    (F : Finset (Finset (Fin (n + 1))))
    (hF : ∀ T ∈ F, J ⊆ T ∧ j ∈ T)
    (hdown : ∀ T ∈ F, ∀ U, J ⊆ U → j ∈ U → U ⊆ T → U ∈ F) :
    innerAnodyneExtensions (Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceComplex_le_stage.{u} J F)) := by
  classical
  revert hF hdown
  refine Finset.strongInductionOn F ?_
  intro F ih hF hdown
  by_cases hE : F = ∅
  · subst F
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceStage.{u} J ∅ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceComplex J := by
      simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceStage]
    exact innerAnodyneExtensions.of_isIso (Subcomplex.eqToIso he.symm).hom
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image F Finset.card
    (Finset.nonempty_iff_ne_empty.mpr hE)
  have hJS := (hF S hS).1
  have hjS := (hF S hS).2
  have hprevF : ∀ T ∈ F.erase S, J ⊆ T ∧ j ∈ T :=
    fun T hT ↦ hF T (Finset.mem_erase.mp hT).2
  have hnot : ∀ T ∈ F.erase S, ¬S ⊆ T := by
    intro T hT hST
    have he := Finset.eq_of_subset_of_card_le hST
      (hmax T (Finset.mem_erase.mp hT).2)
    exact (Finset.mem_erase.mp hT).1 he.symm
  have hprevDown : ∀ T ∈ F.erase S, ∀ U,
      J ⊆ U → j ∈ U → U ⊆ T → U ∈ F.erase S := by
    intro T hT U hJU hjU hUT
    apply Finset.mem_erase.mpr
    refine ⟨?_, hdown T (Finset.mem_erase.mp hT).2 U hJU hjU hUT⟩
    intro hUS
    exact hnot T hT (hUS ▸ hUT)
  have hprev := ih (F.erase S) (Finset.erase_ssubset hS) hprevF hprevDown
  have hfaces : ∀ a ∈ S, a ≠ j → a ∉ J → S.erase a ∈ F.erase S := by
    intro a ha haj haJ
    apply Finset.mem_erase.mpr
    refine ⟨?_, hdown S hS (S.erase a) ?_ ?_ (Finset.erase_subset _ _)⟩
    · intro hEq
      have hc := Finset.card_erase_lt_of_mem ha
      rw [hEq] at hc
      exact (lt_irrefl _) hc
    · intro b hb
      exact Finset.mem_erase.mpr ⟨(fun h ↦ haJ (h ▸ hb)), hJS hb⟩
    · exact Finset.mem_erase.mpr ⟨haj.symm, hjS⟩
  have hc : S.card = (S.card - 1) + 1 := by
    have hp := Finset.card_pos.mpr (show S.Nonempty from ⟨j, hjS⟩)
    omega
  let e := S.orderIsoOfFin hc
  let p := e.symm ⟨j, hjS⟩
  have hp : (e p).val = j := congrArg Subtype.val (e.apply_symm_apply ⟨j, hjS⟩)
  have hinner := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.faceCoordinates_index_inner S e p i k (hJS hi) (hJS hk)
    (by rw [hp]; exact hij) (by rw [hp]; exact hjk)
  have hattach := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceStage_attach_innerAnodyne J S e p (F.erase S)
    hinner.1 hinner.2 (by rw [hp]; exact hj) hJS
    (by intro T hT; rw [hp]; exact (hprevF T hT).2) hnot
    (by simpa only [hp] using hfaces)
  have hEq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceStage.{u} J (F.erase S) ⊔ stdSimplex.face S =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceStage J F :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceStage_insert J S (F.erase S)).symm.trans
      (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceStage J) (Finset.insert_erase hS))
  have hpost := innerAnodyneExtensions.of_isIso (Subcomplex.eqToIso hEq).hom
  have hcomp := innerAnodyneExtensions.comp_mem _ _
    (innerAnodyneExtensions.comp_mem _ _ hprev hattach) hpost
  exact hcomp

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
