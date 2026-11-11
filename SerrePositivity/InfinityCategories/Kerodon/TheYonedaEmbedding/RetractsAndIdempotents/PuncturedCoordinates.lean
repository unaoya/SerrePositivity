module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.MissingFaces

/-!
概要：元の面の頂点を順に列挙して、元の欠けた境界を同じ標準ホーンへ照合する。
方針：元の面の表現可能性による同型を使い、全単体の頂点作用を計算する。
規約：元の面・欠けた頂点・元の包含を保持する。
使われ方：HTT 4.4.5.8 の貼付けを実際の内角ホーンへ移す座標。

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

/-- 元の欠けた面の境界への所属は、指定頂点以外の元の欠けた頂点で検出できる。 -/
lemma mem_puncturedFace {n m : ℕ} (S : Finset (Fin (n + 1))) (j : Fin (n + 1))
    (a : (Δ[n] : SSet.{u}) _⦋m⦌) :
    a ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.puncturedFace S j).obj (Opposite.op ⦋m⦌) ↔
      ∃ i ∈ S, i ≠ j ∧ ∀ v, a v ∈ S.erase i := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.puncturedFace, Subfunctor.iSup_obj, Set.mem_iUnion, stdSimplex.mem_face_iff,
    exists_prop]

/-- 元のホーンへの所属は、指定頂点以外の元の欠けた頂点で検出できる。 -/
lemma mem_horn_missing_vertex {n m : ℕ} (j : Fin (n + 1))
    (a : (Δ[n] : SSet.{u}) _⦋m⦌) :
    a ∈ (horn n j).obj (Opposite.op ⦋m⦌) ↔ ∃ i, i ≠ j ∧ ∀ v, a v ≠ i := by
  rw [horn_eq_iSup]
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion, stdSimplex.mem_face_iff,
    Finset.mem_compl, Finset.mem_singleton, Subtype.exists, Set.mem_compl_iff,
    Set.mem_singleton_iff, exists_prop]

/-- 元の非空な面を同じ順序の頂点で表示する標準同型。 -/
def faceCoordinates {n d : ℕ} (S : Finset (Fin (n + 1))) (e : Fin (d + 1) ≃o S) :
    (Δ[d] : SSet.{u}) ≅ stdSimplex.face S :=
  stdSimplex.isoOfRepresentableBy (stdSimplex.faceRepresentableBy S d e)

/-- 元の面の標準座標の全単体での頂点作用は、元の順序付き頂点の包含。 -/
lemma faceCoordinates_vertex {n d m : ℕ} (S : Finset (Fin (n + 1)))
    (e : Fin (d + 1) ≃o S) (a : (Δ[d] : SSet.{u}) _⦋m⦌) (v : Fin (m + 1)) :
    (((faceCoordinates S e).hom ≫ (stdSimplex.face S).ι).app (Opposite.op ⦋m⦌) a) v =
      (e (a v)).val := rfl

/-- 元の面の欠けた境界を標準座標へ戻すと、同じ指定頂点の標準ホーン。 -/
lemma puncturedFace_coordinate_preimage {n d : ℕ} (S : Finset (Fin (n + 1)))
    (e : Fin (d + 1) ≃o S) (p : Fin (d + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.puncturedFace S (e p).val).preimage
      ((faceCoordinates.{u} S e).hom ≫ (stdSimplex.face S).ι) = horn d p := by
  ext ⟨⟨m⟩⟩ a
  change _ ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.puncturedFace S (e p).val).obj (Opposite.op ⦋m⦌) ↔ _
  rw [mem_puncturedFace, mem_horn_missing_vertex]
  constructor
  · rintro ⟨i, hi, hip, ha⟩
    let q := e.symm ⟨i, hi⟩
    have hq : (e q).val = i := congrArg Subtype.val (e.apply_symm_apply ⟨i, hi⟩)
    refine ⟨q, (fun h ↦ hip (hq.symm.trans (congrArg (fun r ↦ (e r).val) h))), ?_⟩
    intro v hv
    have hvi := (Finset.mem_erase.mp (ha v)).1
    rw [faceCoordinates_vertex, hv, hq] at hvi
    exact hvi rfl
  · rintro ⟨q, hqp, ha⟩
    refine ⟨(e q).val, (e q).property, ?_, ?_⟩
    · intro h
      exact hqp (e.injective (Subtype.ext h))
    · intro v
      rw [faceCoordinates_vertex]
      apply Finset.mem_erase.mpr
      refine ⟨?_, (e (a v)).property⟩
      intro h
      exact ha v (e.injective (Subtype.ext h))

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
