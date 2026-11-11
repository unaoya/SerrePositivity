module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.MissingFaces

/-!
概要：指定面を避ける複体へ次の面を貼るときの、元の交わりを計算する。
方針：既存の各面と新しい面の共通頂点を調べ、指定頂点以外の欠けた頂点を回収する。
規約：元の有限族と元の面を保持。ホーンの座標への移送は後続で行う。
使われ方：HTT 4.4.5.8 の各段階の実際の pushout。

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

/-- 新しい面と既存段階の交わりは、同じ面の指定頂点以外の全ての面。 -/
lemma missingFaceStage_inf_face {n : ℕ} (J S : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (F : Finset (Finset (Fin (n + 1))))
    (hj : j ∉ J) (hJS : J ⊆ S)
    (hpoint : ∀ T ∈ F, j ∈ T) (hnot : ∀ T ∈ F, ¬S ⊆ T)
    (hfaces : ∀ i ∈ S, i ≠ j → i ∉ J → S.erase i ∈ F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceStage.{u} J F ⊓ stdSimplex.face S = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.puncturedFace S j := by
  apply le_antisymm
  · rintro ⟨⟨k⟩⟩ a ⟨ha, hS⟩
    rcases ha with hJ | hF
    · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceComplex, Subfunctor.iSup_obj, Set.mem_iUnion] at hJ
      obtain ⟨i, hi, hai⟩ := hJ
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.puncturedFace, Subfunctor.iSup_obj, Set.mem_iUnion]
      refine ⟨i, hJS hi, (fun h ↦ hj (h ▸ hi)), ?_⟩
      rw [stdSimplex.mem_face_iff] at hai hS ⊢
      intro v
      have hvi : a v ≠ i := by simpa using hai v
      exact Finset.mem_erase.mpr ⟨hvi, hS v⟩
    · simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hF
      obtain ⟨T, hT, haT⟩ := hF
      obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp (hnot T hT)
      have hij : i ≠ j := fun h ↦ hiT (h.symm ▸ hpoint T hT)
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.puncturedFace, Subfunctor.iSup_obj, Set.mem_iUnion]
      refine ⟨i, hiS, hij, ?_⟩
      rw [stdSimplex.mem_face_iff] at haT hS ⊢
      intro v
      have hvi : a v ≠ i := fun h ↦ hiT (h ▸ haT v)
      exact Finset.mem_erase.mpr ⟨hvi, hS v⟩
  · apply le_inf
    · apply iSup_le
      intro i
      apply iSup_le
      intro hi
      apply iSup_le
      intro hij
      by_cases hiJ : i ∈ J
      · apply le_sup_of_le_left
        exact le_iSup_of_le i (le_iSup_of_le hiJ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.face_erase_le_complement S i))
      · apply le_sup_of_le_right
        exact le_iSup_of_le (S.erase i) (le_iSup_of_le (hfaces i hi hij hiJ) le_rfl)
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.puncturedFace_le_face S j

/-- 元の交わりを使った段階への貼付けは、同じ部分複体の実際の pushout。 -/
lemma missingFaceStage_pushout {n : ℕ} (J S : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (F : Finset (Finset (Fin (n + 1))))
    (hj : j ∉ J) (hJS : J ⊆ S)
    (hpoint : ∀ T ∈ F, j ∈ T) (hnot : ∀ T ∈ F, ¬S ⊆ T)
    (hfaces : ∀ i ∈ S, i ≠ j → i ∉ J → S.erase i ∈ F) :
    Subcomplex.BicartSq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.puncturedFace.{u} S j) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceStage J F)
      (stdSimplex.face S) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceStage J F ⊔ stdSimplex.face S) where
  sup_eq := rfl
  inf_eq := missingFaceStage_inf_face J S j F hj hJS hpoint hnot hfaces

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
