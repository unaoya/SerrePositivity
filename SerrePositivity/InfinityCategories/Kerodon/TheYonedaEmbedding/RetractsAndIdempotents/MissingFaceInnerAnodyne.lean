module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.MissingFaceFiniteAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.MissingFaceCardStage
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：指定面を含まない面の合併の包含は、内点が指定面の両端の間にあれば inner anodyne。
方針：元の指定面と内点を含む全ての面を有限順に貼り、元の全単体を回収する。
規約：元の包含そのものの性質を証明する。使われ方：HTT 4.4.5.8。

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

/-- 元の指定面を含まない面の合併の包含は、指定面の二頂点の間に内点があれば内角 anodyne。 -/
@[kerodon 03ZB]
lemma missingFaceComplex_innerAnodyne {n : ℕ} (J : Finset (Fin (n + 1)))
    (j i k : Fin (n + 1)) (hj : j ∉ J) (hi : i ∈ J) (hk : k ∈ J)
    (hij : i < j) (hjk : j < k) :
    innerAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceComplex.{u} J).ι := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceCardFamily J j (n + 2)
  have hF : ∀ T ∈ F, J ⊆ T ∧ j ∈ T := by
    intro T hT
    have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.mem_missingFaceCardFamily J T j (n + 2)).mp hT
    exact ⟨h.1, h.2.1⟩
  have hdown : ∀ T ∈ F, ∀ U, J ⊆ U → j ∈ U → U ⊆ T → U ∈ F := by
    intro T hT U hJU hjU hUT
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.mem_missingFaceCardFamily J U j (n + 2)).mpr
    have hT' := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.mem_missingFaceCardFamily J T j (n + 2)).mp hT).2.2
    exact ⟨hJU, hjU, lt_of_le_of_lt (Finset.card_le_card hUT) hT'⟩
  have ht : (Finset.univ : Finset (Fin (n + 1))) ∈ F := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.mem_missingFaceCardFamily J _ j (n + 2)).mpr
    exact ⟨Finset.subset_univ _, Finset.mem_univ _, by simp⟩
  have htop : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceStage.{u} J F = ⊤ := by
    apply top_unique
    rw [← stdSimplex.face_univ n]
    exact le_sup_of_le_right (le_iSup_of_le Finset.univ (le_iSup_of_le ht le_rfl))
  have hstage := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceStage_innerAnodyne J j i k hj hi hk hij hjk F hF hdown
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceStage.{u} J F).ι := (Subfunctor.eq_top_iff_isIso _).mp htop
  exact innerAnodyneExtensions.comp_mem _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceStage.{u} J F).ι hstage
    (innerAnodyneExtensions.of_isIso _)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
