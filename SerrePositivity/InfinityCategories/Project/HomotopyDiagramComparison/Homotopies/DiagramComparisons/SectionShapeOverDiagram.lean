module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SectionShapeColimit

/-!
概要：単体集合の形状の余極限を、指定した図式の底上の余極限として表示する。
方針：各部分の包含の後に元の図式を合成し、Over の忘却関手で普遍性を反映する。
規約：形状の余極限は通常の単体集合の余極限。∞ 余極限を仮定しない。
使われ方：coherent な図式を骨格・セルの和に制限した切断空間の極限表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {S : SSet.{u}} {J : Type w} [SmallCategory J]
  {F : J ⥤ SSet.{u}} (c : Cocone F) (p : c.pt ⟶ S)

/-- 形状の各部分からの包含に沿って元の図式を制限した、底上の図式。 -/
def sectionShapeOverDiagram : J ⥤ Over S where
  obj j := Over.mk (c.ι.app j ≫ p)
  map f := Over.homMk (F.map f) (by
    change F.map f ≫ (_ ≫ p) = _ ≫ p
    rw [← Category.assoc, c.w f])

/-- 元の図式は各部分の制限の底上の余錐となる。 -/
def sectionShapeOverCocone : Cocone (sectionShapeOverDiagram c p) where
  pt := Over.mk p
  ι :=
    { app j := Over.homMk (c.ι.app j) rfl
      naturality := by
        intro a b f
        apply (Over.forget S).map_injective
        exact c.w f }

/-- 形状の余極限は、元の図式の底上の制限の図式でも余極限になる。 -/
def sectionShapeOverCocone_isColimit (hc : IsColimit c) :
    IsColimit (sectionShapeOverCocone c p) := by
  apply isColimitOfReflects (Over.forget S)
  exact hc

/-- 指定図式の切断空間は、各部分に制限した切断空間の極限として計算できる。 -/
def sectionShapeOverCone_isLimit {E : SSet.{u}} (q : E ⟶ S) (hc : IsColimit c) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeFunctorOverColimitCone q (sectionShapeOverDiagram c p)
      (sectionShapeOverCocone c p)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeFunctorOverColimitCone_isLimit q _ _ (sectionShapeOverCocone_isColimit c p hc)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
