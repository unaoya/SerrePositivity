module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.MissingFaceAttachment
public import Mathlib.Data.Finset.Powerset

/-!
概要：元の面を頂点数の順に貼るための、具体的な有限段階と交わり。
方針：指定面と指定頂点を含む、頂点数が小さい元の面を全て集める。
規約：次に貼る元の面と既存段階の共通部分を、同じ面の欠けた境界に同定する。
使われ方：HTT 4.4.5.8 の有限貼付けの次数順。

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

/-- 指定面と指定頂点を含み、頂点数が指定された数より小さい元の面の有限族。 -/
def missingFaceCardFamily {n : ℕ} (J : Finset (Fin (n + 1))) (j : Fin (n + 1)) (k : ℕ) :
    Finset (Finset (Fin (n + 1))) :=
  Finset.univ.powerset.filter (fun T ↦ J ⊆ T ∧ j ∈ T ∧ T.card < k)

/-- 元の次数順の有限族への所属は、元の三つの条件そのもの。 -/
lemma mem_missingFaceCardFamily {n : ℕ} (J T : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (k : ℕ) :
    T ∈ missingFaceCardFamily J j k ↔ J ⊆ T ∧ j ∈ T ∧ T.card < k := by
  simp [missingFaceCardFamily]

/-- 次に貼る元の面と次数順の元の既存段階の交わりを、同じ欠けた境界へ同定する。 -/
lemma missingFaceCardStage_inf_face {n : ℕ} (J S : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (hj : j ∉ J) (hJS : J ⊆ S) (hjS : j ∈ S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceStage.{u} J (missingFaceCardFamily J j S.card) ⊓ stdSimplex.face S =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.puncturedFace S j := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceStage_inf_face J S j _ hj hJS
  · intro T hT
    exact ((mem_missingFaceCardFamily J T j S.card).mp hT).2.1
  · intro T hT hST
    have hT' := ((mem_missingFaceCardFamily J T j S.card).mp hT).2.2
    have hle := Finset.card_le_card hST
    omega
  · intro i hi hij hiJ
    apply (mem_missingFaceCardFamily J (S.erase i) j S.card).mpr
    refine ⟨?_, Finset.mem_erase.mpr ⟨hij.symm, hjS⟩, Finset.card_erase_lt_of_mem hi⟩
    intro a ha
    exact Finset.mem_erase.mpr ⟨(fun h ↦ hiJ (h ▸ ha)), hJS ha⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
