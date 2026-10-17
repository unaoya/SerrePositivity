module
public import SerrePositivity.InfinityCategories.DGNerve.FaceRhsComparison
public import SerrePositivity.InfinityCategories.DGNerve.CospanCommonData

/-! # 左右の先頭・D 側の右辺の直接比較

概要：左右の零未知境界データで、先頭と D 側の右辺は異種等号で一致する。
方針：これらの集合が最初の末尾頂点を含まないことと共通面のデータの等式を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：型付きの残差の左右共通性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：左右の零未知境界データの先頭の右辺は異種等号で一致する。
方針：最初の末尾頂点を含まない先頭集合に共通面の比較を適用する。
規約：HTT §1.2.13。使われ方：r₀ を左右で一つに同定する。 -/
lemma cospanBoundaryZeroData_prefixRhs_heq {n : ℕ}
    (F : join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ dgNerve A D) :
    HEq (cospanBoundaryLeftZeroData F).cospanPrefixRhs
      (cospanBoundaryRightZeroData F).cospanPrefixRhs := by
  have hf := cospanBoundaryZeroData_common F
  dsimp only [cospanCommonOrderHom] at hf
  unfold SimplexData.cospanPrefixRhs
  exact SimplexData.rhs_heq_of_face_pullback_eq _ _ (cospanFirstTail n) hf _
    (cospanTail_notMem_prefix _ (cospanApex_lt_firstTail n)) _ _ _ _ _ _ _

/-- 概要：左右の零未知境界データの D 側の右辺は異種等号で一致する。
方針：最初の末尾頂点を含まない D 側の集合に共通面の比較を適用する。
規約：HTT §1.2.13。使われ方：r_D を左右で一つに同定する。 -/
lemma cospanBoundaryZeroData_D_rhs_heq {n : ℕ}
    (F : join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ dgNerve A D) :
    HEq ((cospanBoundaryLeftZeroData F).cospanOneTailRhs (cospanLastTail n)
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)))
      ((cospanBoundaryRightZeroData F).cospanOneTailRhs (cospanLastTail n)
        ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))) := by
  have hf := cospanBoundaryZeroData_common F
  dsimp only [cospanCommonOrderHom] at hf
  have hn : cospanFirstTail n ∉ insert (cospanLastTail n) (cospanPrefixFaces n) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨ne_of_lt (cospanFirstTail_lt_lastTail n),
      cospanTail_notMem_prefix _ (cospanApex_lt_firstTail n)⟩
  unfold SimplexData.cospanOneTailRhs
  exact SimplexData.rhs_heq_of_face_pullback_eq _ _ (cospanFirstTail n) hf _ hn _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.DGNerve
