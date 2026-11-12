module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Walking
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakShape

/-!
概要：元の分裂二単体の像が等しいとき、標準二単体の元の単体を分類する。
方針：元の分裂対象と非分裂対象を区別し、中央頂点の逆像と単調性を使う。
規約：全次数の元の単体を扱い、非退化単体だけへの制限は行わない。
使われ方：Ret の商から元の分裂添字への標準比較の単射性。

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

/-- 元の分裂対象と非分裂対象は、同じ添字圏の異なる二対象。 -/
lemma walkingSource_ne_image : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource.{u} ≠ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage := by
  intro h
  have hp := congrArg (fun P : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u} ↦ (P.p : WithOne PUnit.{u + 1})) h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingIdempotent_ne_id hp.symm

/-- 元の分裂二単体の全次数での頂点作用は、中央頂点だけを元の非分裂対象へ送る。 -/
lemma walkingRetractionTriangle_obj {n : ℕ} (a : (Δ[2] : SSet.{u}) _⦋n⦌)
    (i : Fin (n + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingRetractionTriangle.app (Opposite.op ⦋n⦌) a).obj i) =
      if a i = 1 then _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource else _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage := by
  change (ComposableArrows.mk₂ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSection _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingRetraction).obj (a i) = _
  generalize a i = j
  fin_cases j <;> rfl

/-- 同じ像を持つ元の二単体の単体は、中央頂点の元の逆像を共有する。 -/
lemma walkingRetractionTriangle_one_iff {n : ℕ} {a b : (Δ[2] : SSet.{u}) _⦋n⦌}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingRetractionTriangle.app (Opposite.op ⦋n⦌) a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingRetractionTriangle.app (Opposite.op ⦋n⦌) b) (i : Fin (n + 1)) :
    a i = 1 ↔ b i = 1 := by
  have hi := congrArg (fun t ↦ t.obj i) h
  rw [walkingRetractionTriangle_obj, walkingRetractionTriangle_obj] at hi
  by_cases ha : a i = 1 <;> by_cases hb : b i = 1 <;>
    simp [ha, hb, walkingSource_ne_image, Ne.symm walkingSource_ne_image] at hi ⊢

/-- 中央頂点を通る標準二単体の単体は、その中央頂点の逆像で一意に決まる。 -/
lemma triangleSimplex_eq_of_one_fibers {n : ℕ} {a b : (Δ[2] : SSet.{u}) _⦋n⦌}
    (h : ∀ i, a i = 1 ↔ b i = 1) (j : Fin (n + 1)) (hj : a j = 1) : a = b := by
  have hbj : b j = 1 := (h j).mp hj
  apply SSet.stdSimplex.ext
  intro i
  by_cases hi : a i = 1
  · exact hi.trans ((h i).mp hi).symm
  have hbi : b i ≠ 1 := fun hb ↦ hi ((h i).mpr hb)
  rcases le_total i j with hij | hji
  · have ha := (stdSimplex.monotone_apply a) hij
    have hb := (stdSimplex.monotone_apply b) hij
    change a i ≤ a j at ha
    change b i ≤ b j at hb
    have haj : (a j).val = 1 := congrArg Fin.val hj
    have hbjv : (b j).val = 1 := congrArg Fin.val hbj
    apply Fin.ext
    have ha' := (a i).isLt
    have hb' := (b i).isLt
    omega
  · have ha := (stdSimplex.monotone_apply a) hji
    have hb := (stdSimplex.monotone_apply b) hji
    change a j ≤ a i at ha
    change b j ≤ b i at hb
    have haj : (a j).val = 1 := congrArg Fin.val hj
    have hbjv : (b j).val = 1 := congrArg Fin.val hbj
    apply Fin.ext
    have ha' := (a i).isLt
    have hb' := (b i).isLt
    omega

/-- 同じ像を持つ元の単体は、同じ単体か、双方が元の長辺を経由する。 -/
lemma walkingRetractionTriangle_kernel {n : ℕ} {a b : (Δ[2] : SSet.{u}) _⦋n⦌}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingRetractionTriangle.app (Opposite.op ⦋n⦌) a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingRetractionTriangle.app (Opposite.op ⦋n⦌) b) :
    a = b ∨ (∀ i, a i ≠ 1) ∧ (∀ i, b i ≠ 1) := by
  by_cases hj : ∃ j, a j = 1
  · obtain ⟨j, hj⟩ := hj
    exact Or.inl (triangleSimplex_eq_of_one_fibers (walkingRetractionTriangle_one_iff h) j hj)
  · right
    have ha : ∀ i, a i ≠ 1 := fun i hi ↦ hj ⟨i, hi⟩
    exact ⟨ha, fun i hi ↦ ha i ((walkingRetractionTriangle_one_iff h i).mpr hi)⟩

/-- 中央頂点を避ける元の単体は、元の長辺の包含を厳密に経由する。 -/
lemma triangleSimplex_longEdge_factor {n : ℕ} (a : (Δ[2] : SSet.{u}) _⦋n⦌)
    (h : ∀ i, a i ≠ 1) :
    ∃ c : (Δ[1] : SSet.{u}) _⦋n⦌, (stdSimplex.δ (1 : Fin 3)).app _ c = a := by
  have ha : a ∈ (Subcomplex.range (stdSimplex.δ (1 : Fin 3))).obj (Opposite.op ⦋n⦌) := by
    rw [stdSimplex.range_δ, stdSimplex.mem_face_iff]
    intro i
    simpa only [Finset.mem_compl, Finset.mem_singleton] using h i
  exact ha

/-- 元の長辺を経由する二単体の二つの単体は、同じ Ret の商で厳密に等しい。 -/
lemma weakTriangle_eq_of_avoids_one {n : ℕ} {a b : (Δ[2] : SSet.{u}) _⦋n⦌}
    (ha : ∀ i, a i ≠ 1) (hb : ∀ i, b i ≠ 1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakTriangle.app (Opposite.op ⦋n⦌) a = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakTriangle.app (Opposite.op ⦋n⦌) b := by
  obtain ⟨a', rfl⟩ := triangleSimplex_longEdge_factor a ha
  obtain ⟨b', rfl⟩ := triangleSimplex_longEdge_factor b hb
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋n⦌) a') _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakTriangle_longEdge
  have k := congrArg (fun f ↦ f.app (Opposite.op ⦋n⦌) b') _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakTriangle_longEdge
  simp only [NatTrans.comp_app_apply] at h k
  exact h.trans ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakImagePoint.app (Opposite.op ⦋n⦌))
    (by apply SSet.stdSimplex.ext; intro i; apply Fin.ext; omega)).trans k.symm)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
