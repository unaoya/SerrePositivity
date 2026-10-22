module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightFibrationColimitFiber

/-!
概要：strict right fibration 余極限の同じ fiber の元の余錐と、その余極限性。
方針：構成済みの比較同型で通常の余極限余錐を移し、各脚を元の fiber 写像に同定する。
規約：全空間の余極限の脚が誘導する同じ fiber 写像を保つ。
使われ方：coherent な前層図式の評価された余錐との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {B : SSet.{u}} {I : Type u} [SmallCategory I] [IsFiltered I]

/-- 同じ strict 余極限の fiber を頂点とする元の fiber 図式の余錐。 -/
def strictRightFibrationFiberColimitCocone (F : I ⥤ RightFibrationObject B)
    (b : B _⦋0⦌) : Cocone (rightFibrationFiberDiagram F b) where
  pt := vertexFiber (strictRightFibrationColimitProjection F) b
  ι := { app i := colimit.ι _ i ≫ (strictRightFibrationColimitFiberIso F b).hom
         naturality _ _ f := by
           change _ ≫ _ ≫ _ = _ ≫ 𝟙 _
           rw [colimit.w_assoc, Category.comp_id] }

/-- 元の各脚は全空間の同じ余極限の脚が誘導する実際の fiber 写像。 -/
lemma strictRightFibrationFiberColimitCocone_ι (F : I ⥤ RightFibrationObject B)
    (b : B _⦋0⦌) (i : I) :
    (strictRightFibrationFiberColimitCocone F b).ι.app i =
      vertexFiberMap (F.obj i).val.hom (strictRightFibrationColimitProjection F)
        (colimit.ι (rightFibrationTotalDiagram F) i)
        (strictRightFibrationColimitProjection_ι F i) b := by
  apply vertexFiber_hom_ext _ b
  change (colimit.ι _ i ≫ (strictRightFibrationColimitFiberIso F b).hom) ≫ _ = _
  rw [Category.assoc, strictRightFibrationColimitFiberIso_hom_ι,
    colimit.ι_map, vertexFiberMap_ι]
  rfl

/-- 同じ元の fiber 余錐は通常の単体集合の余極限。 -/
def strictRightFibrationFiberColimitCocone_isColimit
    (F : I ⥤ RightFibrationObject B) (b : B _⦋0⦌) :
    IsColimit (strictRightFibrationFiberColimitCocone F b) :=
  IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cocone.ext (strictRightFibrationColimitFiberIso F b))

end SerrePositivity.InfinityCategories.F2.Ind
