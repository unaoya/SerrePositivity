module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightFibrationDiagramColimit
public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightStraighteningFiberDiagram
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictNativeCocones

/-!
概要：strict な right fibration 余極限の元の余錐を、同じ right straightening で前層へ写す。
方針：全空間の元の余極限の脚を底上の射とし、その同じ通常の余錐を coherent に実現する。
規約：前層側の同じ余錐を固定する。ここではその余極限性をまだ主張しない。
使われ方：元の fiber 余錐との全高次比較で前層余極限性を示す際の指定余錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable {B : SSet.{u}} {I : Type u} [SmallCategory I] [IsFiltered I]

/-- 元の全空間の余極限の脚を底上の射にした同じ right fibration 余錐。 -/
def strictRightFibrationColimitCocone (F : I ⥤ RightFibrationObject B) : Cocone F where
  pt := strictRightFibrationColimit F
  ι := { app i := Over.homMk (colimit.ι (rightFibrationTotalDiagram F) i)
           (strictRightFibrationColimitProjection_ι F i)
         naturality _ _ f := by
           apply Over.OverMorphism.ext
           change (rightFibrationTotalDiagram F).map f ≫ colimit.ι _ _ = colimit.ι _ _ ≫ 𝟙 _
           rw [Category.comp_id]
           exact colimit.w _ f }

/-- 指定した right fibration 余錐の全空間の脚は元の同じ余極限の脚。 -/
lemma strictRightFibrationColimitCocone_ι_left (F : I ⥤ RightFibrationObject B) (i : I) :
    ((strictRightFibrationColimitCocone F).ι.app i).left =
      colimit.ι (rightFibrationTotalDiagram F) i := rfl

/-- 元の同じ right fibration 余錐の分類写像による実際の前層余錐。 -/
def strictRightStraighteningCocone (F : I ⥤ RightFibrationObject B) :
    JoinCocone (strictCoherentDiagram F ≫ rightStraighteningInfinityMap B) :=
  coherentCoconePost (strictNativeCocone (strictRightFibrationColimitCocone F))
    (rightStraighteningInfinityMap B)

/-- この前層余錐の頂点は同じ strict 余極限対象の分類像。 -/
lemma strictRightStraighteningCocone_vertex (F : I ⥤ RightFibrationObject B) :
    (strictRightStraighteningCocone F).vertex =
      (rightStraighteningInfinityMap B).app _
        (coherentNerveVertex (strictRightFibrationColimit F)) := by
  rw [strictRightStraighteningCocone, coherentCoconePost_vertex, strictNativeCocone_vertex]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
