module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgeAscending

/-! # 連結の右端からの元の数値座標
概要：元の necklace の数値座標で、右ブロックが先、左ブロックが後であると示す。
方針：昇順列挙の一意性と Fin.rev の番号を照合する。
規約：因子順は変えない。使われ方：元の cubeVertexJoin と wedge の一致。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics


/-- 左の元の数値座標を、右ブロックの後へ置く。 -/
def wedgeCoordinateLeft (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (i : Fin T.dimension) :
    Fin (T.wedge U).dimension :=
  ⟨U.dimension + i.val, by rw [T.wedge_dimension U]; have := i.isLt; omega⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeCoordinateLeft)


/-- 右の元の数値座標は、連結後の最初のブロックに置く。 -/
def wedgeCoordinateRight (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (i : Fin U.dimension) :
    Fin (T.wedge U).dimension :=
  ⟨i.val, by rw [T.wedge_dimension U]; have := i.isLt; omega⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeCoordinateRight)


/-- 左の数値ブロックは、元の左の非 joint 頂点の包含と厳密に一致する。 -/
lemma nonjointCoordinate_wedge_left (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (i : Fin T.dimension) :
    (T.wedge U).nonjointCoordinate (T.wedgeCoordinateLeft U i) =
      T.wedgeNonjointLeft U (T.nonjointCoordinate i) := by
  have hi := T.wedgeAscendingIso_index U (Fin.castAdd U.dimension i.rev)
  change ((T.wedge U).nonjointAscending.symm
    (T.wedgeAscendingEquiv U (Fin.castAdd U.dimension i.rev))).val = i.rev.val at hi
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeAscendingEquiv_left] at hi
  change (T.wedge U).nonjointAscending (T.wedgeCoordinateLeft U i).rev =
    T.wedgeNonjointLeft U (T.nonjointAscending i.rev)
  apply (T.wedge U).nonjointAscending.symm.injective
  rw [OrderIso.symm_apply_apply]
  apply Fin.ext
  have hn := T.wedge_dimension U
  have hb := i.isLt
  simp only [Fin.val_rev, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeCoordinateLeft] at hi ⊢
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (nonjointCoordinate_wedge_left)


/-- 右の数値ブロックは、元の右の非 joint 頂点の番号移動と厳密に一致する。 -/
lemma nonjointCoordinate_wedge_right (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (i : Fin U.dimension) :
    (T.wedge U).nonjointCoordinate (T.wedgeCoordinateRight U i) =
      T.wedgeNonjointRight U (U.nonjointCoordinate i) := by
  have hi := T.wedgeAscendingIso_index U (Fin.natAdd T.dimension i.rev)
  change ((T.wedge U).nonjointAscending.symm
    (T.wedgeAscendingEquiv U (Fin.natAdd T.dimension i.rev))).val = T.dimension + i.rev.val at hi
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeAscendingEquiv_right] at hi
  change (T.wedge U).nonjointAscending (T.wedgeCoordinateRight U i).rev =
    T.wedgeNonjointRight U (U.nonjointAscending i.rev)
  apply (T.wedge U).nonjointAscending.symm.injective
  rw [OrderIso.symm_apply_apply]
  apply Fin.ext
  have hn := T.wedge_dimension U
  have hb := i.isLt
  simp only [Fin.val_rev, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeCoordinateRight] at hi ⊢
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (nonjointCoordinate_wedge_right)


/-- 元の連結後の全数値座標は、左右の元のどちらかのブロックに入る。 -/
lemma wedgeCoordinate_cases (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (i : Fin (T.wedge U).dimension) :
    (∃ j, T.wedgeCoordinateLeft U j = i) ∨ (∃ j, T.wedgeCoordinateRight U j = i) := by
  by_cases h : i.val < U.dimension
  · exact Or.inr ⟨⟨i.val, h⟩, Fin.ext rfl⟩
  · have hn := T.wedge_dimension U
    have hb := i.isLt
    exact Or.inl ⟨⟨i.val - U.dimension, by omega⟩, Fin.ext (by
      change U.dimension + (i.val - U.dimension) = i.val
      omega)⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeCoordinate_cases)


end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.nonjointCoordinate_wedge_left := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.nonjointCoordinate_wedge_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.nonjointCoordinate_wedge_right := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.nonjointCoordinate_wedge_right

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeCoordinateLeft (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeCoordinateLeft := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeCoordinateLeft

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeCoordinateRight (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeCoordinateRight := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeCoordinateRight

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeCoordinate_cases := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeCoordinate_cases

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeCoordinateLeft._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeCoordinateLeft._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeCoordinateLeft.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeCoordinateLeft.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeCoordinateRight._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeCoordinateRight._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeCoordinateRight.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeCoordinateRight.eq_1
