module
public import SerrePositivity.KST.SConstruction.NecklaceInWedge
public import SerrePositivity.KST.SConstruction.NecklacePostcomposition

/-! # necklace 連結と入力の後合成の両立
概要：固定端点の連結は、元の単体集合の写像による後合成を保つ。
方針：native な wedge の両包含への制限で二つの射を判定する。
規約：元の全単体的写像の厳密な等号。使われ方：rigidification の入力関手性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 入力の後合成と連結は、元の全単体的写像について厳密に一致する。 -/
lemma necklaceInWedge_postcompose_map {K L : SSet.{u}} (a : K ⟶ L)
    {x y z : K _⦋0⦌} (T : NecklaceIn K x y) (U : NecklaceIn K y z) :
    (necklaceInWedge ((necklaceInPostcompose a x y).obj T)
      ((necklaceInPostcompose a y z).obj U)).map = (necklaceInWedge T U).map ≫ a := by
  have h : T.necklace.down.pointMap T.necklace.down.last ≫ (T.map ≫ a) =
      U.necklace.down.pointMap U.necklace.down.first ≫ (U.map ≫ a) := by
    rw [← Category.assoc, ← Category.assoc, necklaceInWedge_seam T U]
  change T.necklace.down.wedgeDesc U.necklace.down (T.map ≫ a) (U.map ≫ a) h =
        T.necklace.down.wedgeDesc U.necklace.down T.map U.map (necklaceInWedge_seam T U) ≫ a
  apply T.necklace.down.wedge_hom_ext U.necklace.down
  · rw [NecklaceShape.wedgeInl_desc, ← Category.assoc, NecklaceShape.wedgeInl_desc]
  · rw [NecklaceShape.wedgeInr_desc, ← Category.assoc, NecklaceShape.wedgeInr_desc]

/-- 後合成した可換三角形の連結は、元の連結 necklace 射を保持する。 -/
lemma necklaceInWedge_postcompose_hom {K L : SSet.{u}} (a : K ⟶ L)
    {x y z : K _⦋0⦌} {T T' : NecklaceIn K x y} {U U' : NecklaceIn K y z}
    (f : T ⟶ T') (g : U ⟶ U') :
    (necklaceInWedgeMap ((necklaceInPostcompose a x y).map f)
      ((necklaceInPostcompose a y z).map g)).necklaceHom =
        (necklaceInWedgeMap f g).necklaceHom := rfl

end SerrePositivity.KST.SConstruction
