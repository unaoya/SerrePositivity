module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.StandardSimplexInnerFaceIndex

/-!
概要：挿入する頂点より前の頂点が残る面の番号は零ではない。
方針：非退化単体の単射性で欠ける頂点を同定し、単調性で最初の面を除く。
規約：最後の面は許すので、right horn の接合を判定できる。
使われ方：right fibration に対する相対 twisted arrow 比較の全境界充填。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 欠ける頂点の前に面の頂点が残れば、その面は最初の面ではない。 -/
lemma stdSimplexFace_ne_zero {m d : ℕ}
    (x : (Δ[m] : SSet.{u}) _⦋d⦌) (y : (Δ[m] : SSet.{u}) _⦋d + 1⦌)
    (hy : y ∈ (Δ[m] : SSet.{u}).nonDegenerate (d + 1)) (k : Fin (d + 2))
    (hk : (Δ[m] : SSet.{u}).δ k y = x) (p : Fin (m + 1))
    (hs : Finset.univ.image y = insert p (Finset.univ.image x))
    (hin : ∃ a ∈ Finset.univ.image x, a < p) : k ≠ 0 := by
  classical
  have hyinj := (stdSimplex.mem_nonDegenerate_iff_strictMono y).mp hy |>.injective
  have hmiss : y k ∉ Finset.univ.image x := by
    intro hv
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hv
    rw [← hk, stdSimplex.δ_apply] at ht
    exact Fin.succAbove_ne _ _ (hyinj ht)
  have hpoint : y k = p := by
    have hv : y k ∈ Finset.univ.image y :=
      Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    rw [hs] at hv
    exact (Finset.mem_insert.mp hv).resolve_right hmiss
  obtain ⟨a, ha, hap⟩ := hin
  obtain ⟨ta, _, rfl⟩ := Finset.mem_image.mp ha
  intro hz
  have hh := (stdSimplex.monotone_apply y)
    (show k ≤ k.succAbove ta by rw [hz]; exact Fin.zero_le _)
  change y k ≤ y (k.succAbove ta) at hh
  rw [hpoint] at hh
  have he := congrArg (fun f ↦ f ta) hk
  change y (k.succAbove ta) = x ta at he
  rw [he] at hh
  exact (not_le_of_gt hap) hh

/-- 一意な余次元一の面でも、同じ片側の頂点条件で零番目の面を除ける。 -/
lemma stdSimplexUniqueFace_ne_zero {m : ℕ} (x y : (Δ[m] : SSet.{u}).N)
    (h : x.toS.IsUniquelyCodimOneFace y.toS) (p : Fin (m + 1))
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport y = insert p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport x))
    (hin : ∃ a ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport x, a < p) : h.index rfl ≠ 0 := by
  classical
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport_eq_image] at hs hin
  obtain ⟨d, x, rfl⟩ := x.mk_surjective
  obtain ⟨e, y, rfl⟩ := y.mk_surjective
  obtain rfl : e = d + 1 := h.dim_eq
  exact stdSimplexFace_ne_zero x.val y.val y.property (h.index rfl) (h.δ_index rfl) p hs hin

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
