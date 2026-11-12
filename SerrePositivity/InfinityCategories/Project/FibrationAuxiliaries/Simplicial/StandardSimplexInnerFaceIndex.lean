module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseOutsideSimplices

/-!
概要：標準単体の余次元一の面で、欠ける頂点が内部なら面の番号も内部となる。
方針：非退化単体の頂点の単射性で欠ける頂点を同定し、前後の頂点と単調性を使う。
規約：単体の次元を含めた型 N で述べ、pairing の表示に依存しない。
使われ方：有限頂点集合の内部点の挿入から pairing の inner 条件へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 頂点の像の内部にある一頂点を欠く面は、最初または最後の面ではない。 -/
lemma stdSimplexFace_innerIndex {m d : ℕ}
    (x : (Δ[m] : SSet.{u}) _⦋d⦌) (y : (Δ[m] : SSet.{u}) _⦋d + 1⦌)
    (hy : y ∈ (Δ[m] : SSet.{u}).nonDegenerate (d + 1)) (k : Fin (d + 2))
    (hk : (Δ[m] : SSet.{u}).δ k y = x) (p : Fin (m + 1))
    (hs : Finset.univ.image y = insert p (Finset.univ.image x))
    (hin : ∃ a ∈ Finset.univ.image x,
      ∃ b ∈ Finset.univ.image x, a < p ∧ p < b) :
    k ≠ 0 ∧ k ≠ Fin.last (d + 1) := by
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
  obtain ⟨a, ha, b, hb, hap, hpb⟩ := hin
  obtain ⟨ta, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨tb, _, rfl⟩ := Finset.mem_image.mp hb
  have hmono := stdSimplex.monotone_apply y
  constructor
  · intro hz
    have hh := hmono (show k ≤ k.succAbove ta by rw [hz]; exact Fin.zero_le _)
    change y k ≤ y (k.succAbove ta) at hh
    rw [hpoint] at hh
    have he := congrArg (fun f ↦ f ta) hk
    change y (k.succAbove ta) = x ta at he
    rw [he] at hh
    exact (not_le_of_gt hap) hh
  · intro hn
    have hh := hmono (show k.succAbove tb ≤ k by rw [hn]; exact Fin.le_last _)
    change y (k.succAbove tb) ≤ y k at hh
    rw [hpoint] at hh
    have he := congrArg (fun f ↦ f tb) hk
    change y (k.succAbove tb) = x tb at he
    rw [he] at hh
    exact (not_le_of_gt hpb) hh

/-- 欠ける頂点の前後に面の頂点があれば、一意な面の番号は両端ではない。 -/
lemma stdSimplexUniqueFace_innerIndex {m : ℕ} (x y : (Δ[m] : SSet.{u}).N)
    (h : x.toS.IsUniquelyCodimOneFace y.toS) (p : Fin (m + 1))
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport y = insert p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport x))
    (hin : ∃ a ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport x,
      ∃ b ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport x, a < p ∧ p < b) :
    h.index rfl ≠ 0 ∧ h.index rfl ≠ Fin.last (x.dim + 1) := by
  classical
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport_eq_image] at hs hin
  obtain ⟨d, x, rfl⟩ := x.mk_surjective
  obtain ⟨e, y, rfl⟩ := y.mk_surjective
  obtain rfl : e = d + 1 := h.dim_eq
  have hk := h.δ_index rfl
  exact stdSimplexFace_innerIndex x.val y.val y.property (h.index rfl) hk p hs hin

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
