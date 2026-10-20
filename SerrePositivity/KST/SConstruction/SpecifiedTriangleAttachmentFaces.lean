module
public import SerrePositivity.KST.SConstruction.SpecifiedTriangleAttachment

/-! # 元の指定三角形の全ホーン面を同じ実複体内で回収する
概要：ホーンに沿って貼った元の全三角形の各指定面を、既存の同じ全区間へ照合する。
方針：pushout の共有ホーンの等号を、各面包含で前合成する。
規約：実複体内の全区間の等号を使い、写像先だけの一致にしない。
使われ方：元の raw BF 比較三角形を貼る共有頂点の厳密な回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 元の指定ホーンの各全辺は、貼った同じ三角形の同じ全辺。 -/
lemma specifiedTriangleAttachment_face {B : SSet.{u}} {k : Fin 3}
    (a : (Λ[2, k] : SSet.{u}) ⟶ B) (i : Fin 3) (hi : i ≠ k) :
    stdSimplex.δ i ≫ specifiedTriangleAttachmentCell a =
      SSet.horn.ι k i hi ≫ a ≫ specifiedTriangleAttachmentOriginal a := by
  calc
    _ = SSet.horn.ι k i hi ≫ (SSet.horn 2 k).ι ≫ specifiedTriangleAttachmentCell a := by
      rw [← Category.assoc, SSet.horn.ι_ι]
    _ = _ := congrArg (SSet.horn.ι k i hi ≫ ·) (specifiedTriangleAttachment_shared a).symm

end SerrePositivity.KST.SConstruction
