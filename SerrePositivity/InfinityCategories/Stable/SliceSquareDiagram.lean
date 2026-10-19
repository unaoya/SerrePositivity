module
public import SerrePositivity.InfinityCategories.Core.ConeFamily
public import SerrePositivity.InfinityCategories.Core.Pullback

/-! # 固定した cospan 上の錐の四角形表示

概要：slice の錐を全錐の図式、さらに四角形の図式へ写す。
方針：錐の族の比較写像を全図式に含め、形状同型の逆で前合成する。
規約：普遍性は不要。使われ方：D7 の始点の前合成を四角形全体の射へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial

/-- Slice の錐を全錐の関手単体集合へ写す。 -/
def sliceConeDiagramMap {K X : SSet.{u}} (p : K ⟶ X) :
    sliceOver p ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X :=
  sliceConeFamilyMap p ≫ vertexFiberι (coneRestriction K X) (functorVertex p)

/-- 全錐図式への比較の零次成分。 -/
lemma sliceConeDiagramMap_vertex {K X : SSet.{u}} (p : K ⟶ X) (c : JoinCone p) :
    (sliceConeDiagramMap p).app (Opposite.op ⦋0⦌) c = functorVertex c.val :=
  congrArg Subtype.val (sliceConeFamilyMap_app_zero p c)

/-- 固定した cospan の錐を四角形全体の関手単体集合へ写す。 -/
def sliceSquareDiagramMap {X : SSet.{u}} (p : (horn 2 2 : SSet.{u}) ⟶ X) :
    sliceOver p ⟶ (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X :=
  sliceConeDiagramMap p ≫ (pre cospanConeSquareIso.inv).app X

/-- 四角形表示の零次成分は形状同型の逆で制限した全錐。 -/
lemma sliceSquareDiagramMap_vertex {X : SSet.{u}}
    (p : (horn 2 2 : SSet.{u}) ⟶ X) (c : JoinCone p) :
    (sliceSquareDiagramMap p).app (Opposite.op ⦋0⦌) c =
      functorVertex (cospanConeSquareIso.inv ≫ c.val) := by
  change ((pre cospanConeSquareIso.inv).app X).app (Opposite.op ⦋0⦌)
    ((sliceConeDiagramMap p).app (Opposite.op ⦋0⦌) c) = _
  rw [sliceConeDiagramMap_vertex]
  rfl

/-- 四角形の引き戻し錐の図式表示は元の四角形。 -/
lemma sliceSquareDiagramMap_pullbackCone {X : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (sliceSquareDiagramMap (pullbackCospan F)).app (Opposite.op ⦋0⦌) (pullbackCone F) =
      functorVertex F := by
  rw [sliceSquareDiagramMap_vertex]
  change functorVertex (cospanConeSquareIso.inv ≫ (cospanConeSquareIso.hom ≫ F)) = _
  rw [Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories
