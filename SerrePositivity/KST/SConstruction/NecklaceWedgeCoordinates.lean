module
public import SerrePositivity.KST.SConstruction.NecklaceWedgeAscending

/-! # 連結の右端からの元の数値座標
概要：元の necklace の数値座標で、右ブロックが先、左ブロックが後であると示す。
方針：昇順列挙の一意性と Fin.rev の番号を照合する。
規約：因子順は変えない。使われ方：元の cubeVertexJoin と wedge の一致。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction.NecklaceShape

/-- 左の元の数値座標を、右ブロックの後へ置く。 -/
def wedgeCoordinateLeft (T U : NecklaceShape) (i : Fin T.dimension) :
    Fin (T.wedge U).dimension :=
  ⟨U.dimension + i.val, by rw [T.wedge_dimension U]; have := i.isLt; omega⟩

/-- 右の元の数値座標は、連結後の最初のブロックに置く。 -/
def wedgeCoordinateRight (T U : NecklaceShape) (i : Fin U.dimension) :
    Fin (T.wedge U).dimension :=
  ⟨i.val, by rw [T.wedge_dimension U]; have := i.isLt; omega⟩

/-- 左の数値ブロックは、元の左の非 joint 頂点の包含と厳密に一致する。 -/
lemma nonjointCoordinate_wedge_left (T U : NecklaceShape) (i : Fin T.dimension) :
    (T.wedge U).nonjointCoordinate (T.wedgeCoordinateLeft U i) =
      T.wedgeNonjointLeft U (T.nonjointCoordinate i) := by
  have hi := T.wedgeAscendingIso_index U (Fin.castAdd U.dimension i.rev)
  change ((T.wedge U).nonjointAscending.symm
    (T.wedgeAscendingEquiv U (Fin.castAdd U.dimension i.rev))).val = i.rev.val at hi
  rw [wedgeAscendingEquiv_left] at hi
  change (T.wedge U).nonjointAscending (T.wedgeCoordinateLeft U i).rev =
    T.wedgeNonjointLeft U (T.nonjointAscending i.rev)
  apply (T.wedge U).nonjointAscending.symm.injective
  rw [OrderIso.symm_apply_apply]
  apply Fin.ext
  have hn := T.wedge_dimension U
  have hb := i.isLt
  simp only [Fin.val_rev, wedgeCoordinateLeft] at hi ⊢
  omega

/-- 右の数値ブロックは、元の右の非 joint 頂点の番号移動と厳密に一致する。 -/
lemma nonjointCoordinate_wedge_right (T U : NecklaceShape) (i : Fin U.dimension) :
    (T.wedge U).nonjointCoordinate (T.wedgeCoordinateRight U i) =
      T.wedgeNonjointRight U (U.nonjointCoordinate i) := by
  have hi := T.wedgeAscendingIso_index U (Fin.natAdd T.dimension i.rev)
  change ((T.wedge U).nonjointAscending.symm
    (T.wedgeAscendingEquiv U (Fin.natAdd T.dimension i.rev))).val = T.dimension + i.rev.val at hi
  rw [wedgeAscendingEquiv_right] at hi
  change (T.wedge U).nonjointAscending (T.wedgeCoordinateRight U i).rev =
    T.wedgeNonjointRight U (U.nonjointAscending i.rev)
  apply (T.wedge U).nonjointAscending.symm.injective
  rw [OrderIso.symm_apply_apply]
  apply Fin.ext
  have hn := T.wedge_dimension U
  have hb := i.isLt
  simp only [Fin.val_rev, wedgeCoordinateRight] at hi ⊢
  omega

/-- 元の連結後の全数値座標は、左右の元のどちらかのブロックに入る。 -/
lemma wedgeCoordinate_cases (T U : NecklaceShape) (i : Fin (T.wedge U).dimension) :
    (∃ j, T.wedgeCoordinateLeft U j = i) ∨ (∃ j, T.wedgeCoordinateRight U j = i) := by
  by_cases h : i.val < U.dimension
  · exact Or.inr ⟨⟨i.val, h⟩, Fin.ext rfl⟩
  · have hn := T.wedge_dimension U
    have hb := i.isLt
    exact Or.inl ⟨⟨i.val - U.dimension, by omega⟩, Fin.ext (by
      change U.dimension + (i.val - U.dimension) = i.val
      omega)⟩

end SerrePositivity.KST.SConstruction.NecklaceShape
