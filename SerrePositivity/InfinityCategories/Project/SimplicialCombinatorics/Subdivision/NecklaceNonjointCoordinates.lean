module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Cubes.NecklaceBooleanCube
public import Mathlib.Data.Finset.Sort

/-! # 元の非 joint 頂点の個数と右端からの数値座標
概要：元の非 joint 頂点を既存の dimension 個の数値座標で一意に列挙する。
方針：元の番号の有限集合を昇順に列挙した後、Fin.rev で右端からの順序へ移す。
規約：既存の cube の座標零は右端。使われ方：necklace の元の Bool 作用の数値座標化。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
namespace NecklaceShape


/-- 元の非 joint 頂点の番号全体。 -/
def nonjointNumbers (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : Finset ℕ :=
  (Finset.range (T.vertexMax + 1)).filter (fun j => j ∉ T.joints)

/-- 元の番号集合の大きさは既存の立方体の次元。 -/
lemma nonjointNumbers_card (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : T.nonjointNumbers.card = T.dimension := rfl

/-- 元の番号の部分型と同じ非 joint 頂点の順序同型。 -/
def nonjointNumberIso (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : T.nonjointNumbers ≃o T.NonjointVertex where
  toFun j := ⟨⟨j.val, Finset.mem_range.mp (Finset.mem_filter.mp j.property).1⟩,
    (Finset.mem_filter.mp j.property).2⟩
  invFun v := ⟨v.val.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr v.val.isLt, v.property⟩⟩
  left_inv _ := by apply Subtype.ext; rfl
  right_inv _ := by apply Subtype.ext; apply Fin.ext; rfl
  map_rel_iff' := by intro a b; rfl

/-- 元の非 joint 頂点の、元の番号による昇順列挙。 -/
def nonjointAscending (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : Fin T.dimension ≃o T.NonjointVertex :=
  (T.nonjointNumbers.orderIsoOfFin T.nonjointNumbers_card).trans T.nonjointNumberIso

/-- 元の非 joint 頂点を、既存の cube と同じ右端からの座標で列挙する。 -/
def nonjointCoordinate (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : Fin T.dimension ≃ T.NonjointVertex :=
  Fin.revPerm.trans T.nonjointAscending.toEquiv

/-- 元の数値座標の順序は、非 joint 頂点の元の順序と逆向き。 -/
lemma nonjointCoordinate_lt (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (i j : Fin T.dimension) :
    (T.nonjointCoordinate i).val < (T.nonjointCoordinate j).val ↔ j < i := by
  change T.nonjointAscending i.rev < T.nonjointAscending j.rev ↔ j < i
  rw [OrderIso.lt_iff_lt, Fin.rev_lt_rev]

/-- 元の非 joint 頂点数は既存の dimension と一致する。 -/
lemma nonjointVertex_card (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : Fintype.card T.NonjointVertex = T.dimension :=
  (Fintype.card_congr T.nonjointCoordinate).symm.trans (Fintype.card_fin _)

end NecklaceShape
end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointAscending (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.nonjointAscending := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointAscending

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointCoordinate (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.nonjointCoordinate := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointCoordinate

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.nonjointCoordinate_lt := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointCoordinate_lt

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointNumberIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.nonjointNumberIso := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointNumberIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointNumbers (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.nonjointNumbers := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointNumbers

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.nonjointNumbers_card := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointNumbers_card

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.nonjointVertex_card := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointVertex_card

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.nonjointNumberIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointNumberIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.nonjointNumberIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointNumberIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.nonjointNumberIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointNumberIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.nonjointNumberIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointNumberIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.nonjointNumberIso._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointNumberIso._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.nonjointNumberIso._proof_6 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.nonjointNumberIso._proof_6
