module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceInWedge
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklacePostcomposition

/-! # necklace 連結と入力の後合成の両立
概要：固定端点の連結は、元の単体集合の写像による後合成を保つ。
方針：native な wedge の両包含への制限で二つの射を判定する。
規約：元の全単体的写像の厳密な等号。使われ方：rigidification の入力関手性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet

/-- 入力の後合成と連結は、元の全単体的写像について厳密に一致する。 -/
lemma necklaceInWedge_postcompose_map {K L : SSet.{u}} (a : K ⟶ L)
    {x y z : K _⦋0⦌} (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a x y).obj T)
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a y z).obj U)).map = (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U).map ≫ a := by
  have h : T.necklace.down.pointMap T.necklace.down.last ≫ (T.map ≫ a) =
      U.necklace.down.pointMap U.necklace.down.first ≫ (U.map ≫ a) := by
    rw [← Category.assoc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_seam T U]
  change T.necklace.down.wedgeDesc U.necklace.down (T.map ≫ a) (U.map ≫ a) h =
        T.necklace.down.wedgeDesc U.necklace.down T.map U.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_seam T U) ≫ a
  apply T.necklace.down.wedge_hom_ext U.necklace.down
  · rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInl_desc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInl_desc]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInr_desc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInr_desc]

/-- 後合成した可換三角形の連結は、元の連結 necklace 射を保持する。 -/
lemma necklaceInWedge_postcompose_hom {K L : SSet.{u}} (a : K ⟶ L)
    {x y z : K _⦋0⦌} {T T' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y} {U U' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z}
    (f : T ⟶ T') (g : U ⟶ U') :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeMap ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a x y).map f)
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a y z).map g)).necklaceHom =
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeMap f g).necklaceHom := rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInWedge_postcompose_hom := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_postcompose_hom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInWedge_postcompose_map := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_postcompose_map
