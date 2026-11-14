module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgeInclusions
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceInWedge

/-! # 結合同型と元の K への augmentation
概要：固定端点 necklace の三重連結の二つの augmentation が元の結合同型で一致する。
方針：元の三つの包含で射を判定し、元の二重の降下の回収式を使う。
規約：全単体的写像の厳密等号。使われ方：K 内の構造同型と cubical 合成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet

/-- 三つの元のブロックで一致する augmentation は、元の結合同型で一致する。 -/
lemma necklaceAssociator_desc (T U V : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) {K : SSet.{u}}
    (a : T.down.carrier ⟶ K) (b : U.down.carrier ⟶ K) (c : V.down.carrier ⟶ K)
    (l : ((T.down.wedge U.down).wedge V.down).carrier ⟶ K)
    (r : (T.down.wedge (U.down.wedge V.down)).carrier ⟶ K)
    (hl1 : T.down.wedgeInl U.down ≫ (T.down.wedge U.down).wedgeInl V.down ≫ l = a)
    (hl2 : T.down.wedgeInr U.down ≫ (T.down.wedge U.down).wedgeInl V.down ≫ l = b)
    (hl3 : (T.down.wedge U.down).wedgeInr V.down ≫ l = c)
    (hr1 : T.down.wedgeInl (U.down.wedge V.down) ≫ r = a)
    (hr2 : U.down.wedgeInl V.down ≫ T.down.wedgeInr (U.down.wedge V.down) ≫ r = b)
    (hr3 : U.down.wedgeInr V.down ≫ T.down.wedgeInr (U.down.wedge V.down) ≫ r = c) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator T U V).hom.map ≫ r = l := by
  apply (T.down.wedge U.down).wedge_hom_ext V.down
  · apply T.down.wedge_hom_ext U.down
    · rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_inl_inl_assoc, hr1, hl1]
    · rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_inr_inl_assoc, hr2, hl2]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_inr_assoc, hr3, hl3]

/-- 元の固定端点の三重連結の augmentation は、元の結合同型と厳密に可換。 -/
lemma necklaceInAssociator_augmentation {K : SSet.{u}} {w x y z : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K w x) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (V : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator T.necklace U.necklace V.necklace).hom.map ≫
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge U V)).map =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U) V).map := by
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_desc T.necklace U.necklace V.necklace T.map U.map V.map
  · exact (congrArg (fun e => T.necklace.down.wedgeInl U.necklace.down ≫ e)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_inl (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U) V)).trans (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_inl T U)
  · exact (congrArg (fun e => T.necklace.down.wedgeInr U.necklace.down ≫ e)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_inl (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U) V)).trans (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_inr T U)
  · exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_inr (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U) V
  · exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_inl T (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge U V)
  · exact (congrArg (fun e => U.necklace.down.wedgeInl V.necklace.down ≫ e)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_inr T (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge U V))).trans (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_inl U V)
  · exact (congrArg (fun e => U.necklace.down.wedgeInr V.necklace.down ≫ e)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_inr T (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge U V))).trans (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_inr U V)

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceAssociator_desc := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_desc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInAssociator_augmentation := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInAssociator_augmentation
