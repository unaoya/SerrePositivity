module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseExtensionDomain

/-!
概要：edgewise の延長領域の外にある単体を対にするための頂点集合の計算。
方針：左頂点が含まれるとき、対応する右頂点の挿入・削除は欠ける対の有無を変えない。
規約：頂点集合は有限集合として扱い、単体の退化の判定とは分離する。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、右端射影の境界延長のホーン接合。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：有限頂点集合が edgewise の右延長領域の一面を張る条件。
方針：右側だけに含まれるか、ある対応する一対が両方とも欠けることを要求する。
規約：空の頂点集合も条件を満たす。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、延長領域の外の非退化単体の判定。 -/
def EdgewiseSupportInDomain (n : ℕ) (S : Finset (Fin (n + n + 1 + 1))) : Prop :=
  S ⊆ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertices n ∨
    ∃ i : Fin (n + 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n i ∉ S ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n i ∉ S

/-- 概要：単体の延長領域への所属は、その全頂点の像の有限集合の条件と一致する。
方針：面の所属条件と有限集合の像への所属を照合する。
規約：単体 s の退化性は問わない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、単体的な延長領域と有限頂点集合の接続。 -/
lemma mem_edgewiseRightExtensionDomain_iff_support {n d : ℕ}
    (s : (Δ[n + n + 1] : SSet.{u}) _⦋d⦌) :
    s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightExtensionDomain n).obj (Opposite.op ⦋d⦌) ↔
      EdgewiseSupportInDomain n (Finset.univ.image s) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.mem_edgewiseRightExtensionDomain_iff]
  unfold EdgewiseSupportInDomain
  constructor
  · rintro (h | ⟨i, h⟩)
    · left
      intro v hv
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertices, Finset.mem_filter, Finset.mem_univ, true_and] using h j
    · right
      refine ⟨i, ?_, ?_⟩
      · intro hv
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hv
        exact (h j).1 hj
      · intro hv
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hv
        exact (h j).2 hj
  · rintro (h | ⟨i, hl, hr⟩)
    · left
      intro j
      have hj := h (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertices, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    · right
      refine ⟨i, fun j ↦ ⟨?_, ?_⟩⟩
      · intro hj
        exact hl (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)
      · intro hj
        exact hr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)

/-- 概要：右側の対応する頂点の番号は添字を区別する。
方針：番号 n+1+i の等式から i の番号の等式を取り出す。
規約：添字は Fin(n+1)。
使われ方：Kerodon Remark 8.1.1.2（Tag 03JH）、pairing で挿入する頂点の一意性。 -/
lemma edgewiseRightVertex_injective (n : ℕ) : Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex] at hv
  omega

/-- 概要：左頂点を既に含む頂点集合では、対応する右頂点の挿入は領域への所属を変えない。
方針：右半分の条件と欠ける対の条件をそれぞれ比較する。
規約：挿入する右頂点が既に含まれていてもよい。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、領域の外の単体の対を取る基本則。 -/
lemma edgewiseSupportInDomain_insert_right_iff {n : ℕ}
    (S : Finset (Fin (n + n + 1 + 1))) (i : Fin (n + 1))
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n i ∈ S) :
    EdgewiseSupportInDomain n (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n i) S) ↔
      EdgewiseSupportInDomain n S := by
  unfold EdgewiseSupportInDomain
  constructor
  · rintro (h | ⟨j, hl, hr⟩)
    · exact Or.inl (Finset.Subset.trans (Finset.subset_insert _ _) h)
    · exact Or.inr ⟨j, fun hj ↦ hl (Finset.mem_insert_of_mem hj),
        fun hj ↦ hr (Finset.mem_insert_of_mem hj)⟩
  · rintro (h | ⟨j, hl, hr⟩)
    · left
      refine Finset.insert_subset ?_ h
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertices, Finset.mem_filter, Finset.mem_univ,
        true_and, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex]
      omega
    · have hij : i ≠ j := by
        rintro rfl
        exact hl hi
      right
      refine ⟨j, ?_, ?_⟩
      · simp only [Finset.mem_insert, not_or]
        exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex_ne_right n j i, hl⟩
      · simp only [Finset.mem_insert, not_or]
        exact ⟨fun h ↦ hij ((edgewiseRightVertex_injective n h).symm), hr⟩

/-- 概要：左頂点を既に含む頂点集合では、対応する右頂点の削除も領域への所属を変えない。
方針：左右の頂点が異なることを使い、削除後の集合への挿入の法則に戻す。
規約：削除する右頂点が元々存在しない場合も含む。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、pairing の逆操作の整合性。 -/
lemma edgewiseSupportInDomain_erase_right_iff {n : ℕ}
    (S : Finset (Fin (n + n + 1 + 1))) (i : Fin (n + 1))
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n i ∈ S) :
    EdgewiseSupportInDomain n (S.erase (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n i)) ↔
      EdgewiseSupportInDomain n S := by
  by_cases hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n i ∈ S
  · have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n i ∈ S.erase (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n i) := by
      exact Finset.mem_erase.mpr ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex_ne_right n i i, hi⟩
    have h := edgewiseSupportInDomain_insert_right_iff (S.erase (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n i)) i he
    rw [Finset.insert_erase hr] at h
    exact h.symm
  · rw [Finset.erase_eq_of_notMem hr]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
