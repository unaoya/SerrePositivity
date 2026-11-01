module
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceWedgeInclusions
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceInWedge

/-! # 結合同型と元の K への augmentation
概要：固定端点 necklace の三重連結の二つの augmentation が元の結合同型で一致する。
方針：元の三つの包含で射を判定し、元の二重の降下の回収式を使う。
規約：全単体的写像の厳密等号。使われ方：K 内の構造同型と cubical 合成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 三つの元のブロックで一致する augmentation は、元の結合同型で一致する。 -/
lemma necklaceAssociator_desc (T U V : Necklace.{u}) {K : SSet.{u}}
    (a : T.down.carrier ⟶ K) (b : U.down.carrier ⟶ K) (c : V.down.carrier ⟶ K)
    (l : ((T.down.wedge U.down).wedge V.down).carrier ⟶ K)
    (r : (T.down.wedge (U.down.wedge V.down)).carrier ⟶ K)
    (hl1 : T.down.wedgeInl U.down ≫ (T.down.wedge U.down).wedgeInl V.down ≫ l = a)
    (hl2 : T.down.wedgeInr U.down ≫ (T.down.wedge U.down).wedgeInl V.down ≫ l = b)
    (hl3 : (T.down.wedge U.down).wedgeInr V.down ≫ l = c)
    (hr1 : T.down.wedgeInl (U.down.wedge V.down) ≫ r = a)
    (hr2 : U.down.wedgeInl V.down ≫ T.down.wedgeInr (U.down.wedge V.down) ≫ r = b)
    (hr3 : U.down.wedgeInr V.down ≫ T.down.wedgeInr (U.down.wedge V.down) ≫ r = c) :
    (necklaceAssociator T U V).hom.map ≫ r = l := by
  apply (T.down.wedge U.down).wedge_hom_ext V.down
  · apply T.down.wedge_hom_ext U.down
    · rw [necklaceAssociator_inl_inl_assoc, hr1, hl1]
    · rw [necklaceAssociator_inr_inl_assoc, hr2, hl2]
  · rw [necklaceAssociator_inr_assoc, hr3, hl3]

/-- 元の固定端点の三重連結の augmentation は、元の結合同型と厳密に可換。 -/
lemma necklaceInAssociator_augmentation {K : SSet.{u}} {w x y z : K _⦋0⦌}
    (T : NecklaceIn K w x) (U : NecklaceIn K x y) (V : NecklaceIn K y z) :
    (necklaceAssociator T.necklace U.necklace V.necklace).hom.map ≫
        (necklaceInWedge T (necklaceInWedge U V)).map =
      (necklaceInWedge (necklaceInWedge T U) V).map := by
  apply necklaceAssociator_desc T.necklace U.necklace V.necklace T.map U.map V.map
  · exact (congrArg (fun e => T.necklace.down.wedgeInl U.necklace.down ≫ e)
      (necklaceInWedge_inl (necklaceInWedge T U) V)).trans (necklaceInWedge_inl T U)
  · exact (congrArg (fun e => T.necklace.down.wedgeInr U.necklace.down ≫ e)
      (necklaceInWedge_inl (necklaceInWedge T U) V)).trans (necklaceInWedge_inr T U)
  · exact necklaceInWedge_inr (necklaceInWedge T U) V
  · exact necklaceInWedge_inl T (necklaceInWedge U V)
  · exact (congrArg (fun e => U.necklace.down.wedgeInl V.necklace.down ≫ e)
      (necklaceInWedge_inr T (necklaceInWedge U V))).trans (necklaceInWedge_inl U V)
  · exact (congrArg (fun e => U.necklace.down.wedgeInr V.necklace.down ≫ e)
      (necklaceInWedge_inr T (necklaceInWedge U V))).trans (necklaceInWedge_inr U V)

end SerrePositivity.KST.SConstruction
