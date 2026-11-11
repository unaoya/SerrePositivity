module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.PuncturedCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.RelativeFacePreimage
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.MissingFaceAttachment
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic

/-!
概要：元の面の指定された欠けた境界の包含と、その貼付けは inner anodyne。
方針：元の標準ホーンとの矢印同型と、元の部分複体の pushout を使う。
規約：元の面・指定頂点・既存の有限族を保持。全段階の合成は後で行う。
使われ方：HTT 4.4.5.8 の元の内角ホーンによる各セルの貼付け。

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

/-- 元の指定頂点が面の内部にあると、元の欠けた境界の包含は inner anodyne。 -/
lemma puncturedFace_innerAnodyne {n d : ℕ} (S : Finset (Fin (n + 1)))
    (e : Fin (d + 1) ≃o S) (p : Fin (d + 1)) (h0 : 0 < p) (hn : p < Fin.last d) :
    innerAnodyneExtensions (Subcomplex.homOfLE
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.puncturedFace_le_face.{u} S (e p).val)) := by
  have h : innerAnodyneExtensions
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.puncturedFace S (e p).val).preimage
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.faceCoordinates S e).hom ≫ (stdSimplex.face S).ι)).ι := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.puncturedFace_coordinate_preimage]
    exact innerAnodyneExtensions.horn_ι h0 hn
  exact (innerAnodyneExtensions.arrow_mk_iso_iff
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.relativeFacePreimageArrowIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.puncturedFace_le_face S (e p).val)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.faceCoordinates S e))).mp h

/-- 元の指定頂点の両側に元の面の頂点があれば、標準座標でも指定頂点は内部。 -/
lemma faceCoordinates_index_inner {n d : ℕ} (S : Finset (Fin (n + 1)))
    (e : Fin (d + 1) ≃o S) (p : Fin (d + 1))
    (i k : Fin (n + 1)) (hi : i ∈ S) (hk : k ∈ S)
    (hij : i < (e p).val) (hjk : (e p).val < k) : 0 < p ∧ p < Fin.last d := by
  have hleft : e.symm ⟨i, hi⟩ < p := by
    apply e.lt_iff_lt.mp
    rw [e.apply_symm_apply]
    exact hij
  have hright : p < e.symm ⟨k, hk⟩ := by
    apply e.lt_iff_lt.mp
    rw [e.apply_symm_apply]
    exact hjk
  exact ⟨lt_of_le_of_lt (Fin.zero_le _) hleft,
    lt_of_lt_of_le hright (Fin.le_last _)⟩

/-- 元の交わりの包含の pushout として、同じ元の面を貼る射は inner anodyne。 -/
lemma missingFaceStage_attach_innerAnodyne {n d : ℕ} (J S : Finset (Fin (n + 1)))
    (e : Fin (d + 1) ≃o S) (p : Fin (d + 1))
    (F : Finset (Finset (Fin (n + 1))))
    (h0 : 0 < p) (hn : p < Fin.last d) (hj : (e p).val ∉ J) (hJS : J ⊆ S)
    (hpoint : ∀ T ∈ F, (e p).val ∈ T) (hnot : ∀ T ∈ F, ¬S ⊆ T)
    (hfaces : ∀ i ∈ S, i ≠ (e p).val → i ∉ J → S.erase i ∈ F) :
    innerAnodyneExtensions (Subcomplex.homOfLE (show _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceStage.{u} J F ≤
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceStage J F ⊔ stdSimplex.face S from le_sup_left)) := by
  let sq := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceStage_pushout J S (e p).val F hj hJS hpoint hnot hfaces
  exact innerAnodyneExtensions.of_isPushout sq.isPushout
    (puncturedFace_innerAnodyne S e p h0 hn)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
