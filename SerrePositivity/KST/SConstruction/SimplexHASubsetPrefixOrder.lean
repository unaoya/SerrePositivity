module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubset
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexSubsetInclusionOrder
public import Mathlib.Data.Finset.Sort

/-! # 元の任意部分集合を HA 頂点列と終点で読む
概要：元の二点以上の部分集合を、昇順の始点・内部列と元の最大頂点に分けて回収する。
方針：元の有限昇順列挙から最後の番号だけを除き、全頂点の像を照合する。
規約：元の部分集合・両端・次元を保持。使われ方：任意 HA 成分の逆律の有限帰納。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の二点以上の部分集合の全頂点を、元の HA 次元に一段加えた列として読む。 -/
def simplexHASubsetFullOrder {N : ℕ} (I : Finset (Fin (N + 1))) (hI : 2 ≤ I.card) :
    Fin (I.card - 2 + 1 + 1) ↪o Fin (N + 1) :=
  I.orderEmbOfFin (by omega)

/-- 元の部分集合の終点を除く、元の HA 始点・内部頂点列。 -/
def simplexHASubsetPrefixOrder {N : ℕ} (I : Finset (Fin (N + 1))) (hI : 2 ≤ I.card) :
    Fin (I.card - 2 + 1) ↪o Fin (N + 1) :=
  Fin.castSuccOrderEmb.trans (simplexHASubsetFullOrder I hI)

/-- 元の全部分集合列の始点は、同じ元の最小頂点。 -/
lemma simplexHASubsetFullOrder_first {N : ℕ} (I : Finset (Fin (N + 1))) (hI : 2 ≤ I.card) :
    simplexHASubsetFullOrder I hI 0 = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) :=
  Finset.orderEmbOfFin_zero (show I.card = I.card - 2 + 1 + 1 by omega) (by omega)

/-- 元の全部分集合列の終点は、同じ元の最大頂点。 -/
lemma simplexHASubsetFullOrder_last {N : ℕ} (I : Finset (Fin (N + 1))) (hI : 2 ≤ I.card) :
    simplexHASubsetFullOrder I hI (Fin.last (I.card - 2 + 1)) =
      I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) :=
  Finset.orderEmbOfFin_last (show I.card = I.card - 2 + 1 + 1 by omega) (by omega)

/-- 元の HA 部分集合列は、元の同じ最小頂点を始点とする。 -/
lemma simplexHASubsetPrefixOrder_first {N : ℕ} (I : Finset (Fin (N + 1))) (hI : 2 ≤ I.card) :
    simplexHASubsetPrefixOrder I hI 0 = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) :=
  simplexHASubsetFullOrder_first I hI

/-- 元の HA 部分集合列の最後は、元の最大頂点より厳密に左。 -/
lemma simplexHASubsetPrefixOrder_last_lt {N : ℕ} (I : Finset (Fin (N + 1)))
    (hI : 2 ≤ I.card) :
    simplexHASubsetPrefixOrder I hI (Fin.last (I.card - 2)) <
      I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) :=
  lt_of_lt_of_eq ((simplexHASubsetFullOrder I hI).strictMono (Fin.castSucc_lt_last _))
    (simplexHASubsetFullOrder_last I hI)

/-- 元の HA 部分集合列と元の最大頂点を合わせると、元の部分集合全体が戻る。 -/
lemma simplexHASubsetPrefixOrder_subset {N : ℕ} (I : Finset (Fin (N + 1))) (hI : 2 ≤ I.card) :
    simplexHADecodeSubset (I.card - 2) (simplexHASubsetPrefixOrder I hI)
      {I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)} = I := by
  have hr : Set.range (simplexHASubsetFullOrder I hI) = I :=
    I.range_orderEmbOfFin (show I.card = I.card - 2 + 1 + 1 by omega)
  ext x
  rw [simplexHADecodeSubset_mem]
  have hx : x ∈ I ↔ ∃ j, simplexHASubsetFullOrder I hI j = x :=
    (Set.ext_iff.mp hr x).symm
  rw [hx]
  constructor
  · rintro (⟨j, hj⟩ | ht)
    · exact ⟨j.castSucc, hj⟩
    · exact ⟨Fin.last (I.card - 2 + 1),
        (simplexHASubsetFullOrder_last I hI).trans (Finset.mem_singleton.mp ht).symm⟩
  · rintro ⟨j, rfl⟩
    refine Fin.lastCases ?_ (fun i => Or.inl ⟨i, rfl⟩) j
    exact Or.inr ((simplexHASubsetFullOrder_last I hI) ▸ Finset.mem_singleton_self _)

end SerrePositivity.KST.SConstruction
