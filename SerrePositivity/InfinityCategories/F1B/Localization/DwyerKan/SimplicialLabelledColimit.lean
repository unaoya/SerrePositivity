module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.SimplicialLabelledDegrees

/-!
# 単体集合の元の余極限と値の fiber の交換同型

概要：元の fiber の図式の余極限は元の余極限の fiber に同型である。
方針：各次数の余極限性を評価の共同反映で束ねる。
規約：filtered 性や単体集合のモデル構造を仮定しない。
使われ方：元の hammock 上の値の fiber の余極限表示。
-/

@[expose] public section
universe uI vI u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.SimplicialLabelledColimit
open CategoryTheory CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I] {X : I ⥤ SSet.{u}} {B : Type u}
  (L : Labels X B) (β : B) [HasColimit X] [HasColimitsOfShape I (Type u)]

def fiberCocone_isColimit : IsColimit (fiberCocone L β) :=
  evaluationJointlyReflectsColimits _ (fiberDegree_isColimit L β)

def colimitFiberIso : colimit (fiberDiagram L β) ≅
    SimplicialValueFiber.space (colimitValue L) β :=
  (colimit.isColimit (fiberDiagram L β)).coconePointUniqueUpToIso (fiberCocone_isColimit L β)

lemma colimitFiberIso_fac (i : I) :
    colimit.ι (fiberDiagram L β) i ≫ (colimitFiberIso L β).hom = fiberCoconeApp L β i :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (fiberDiagram L β))
    (fiberCocone_isColimit L β) i

lemma colimitFiberIso_fac_inclusion (i : I) :
    colimit.ι (fiberDiagram L β) i ≫ (colimitFiberIso L β).hom ≫
      SimplicialValueFiber.inclusion (colimitValue L) β =
        SimplicialValueFiber.inclusion (L.value i) β ≫ colimit.ι X i := by
  rw [← Category.assoc, colimitFiberIso_fac, fiberCoconeApp_inclusion]

end SerrePositivity.EInfinity.Hammock.SimplicialLabelledColimit
