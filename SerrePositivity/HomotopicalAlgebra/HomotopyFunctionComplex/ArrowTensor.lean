module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ArrowLiftingClass
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.RelativeBoundaryTensor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorBoundary
public import Mathlib.CategoryTheory.Limits.Comma

/-! # Relative subcomplex tensors as ordinary tensors in the arrow category

The comparison is constructed from actual colimit cocones. It needs only
finite colimits in C, not a model structure on C or on its arrow category.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.ArrowTensor
variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]
  {A B : SimplexCategory ⥤ C} (α : A ⟶ B)

def diagram : SimplexCategory ⥤ Arrow C where
  obj n := Arrow.mk (α.app n)
  map f := Arrow.homMk (A.map f) (B.map f) (α.naturality f)
  map_id n := Arrow.hom_ext _ _ (A.map_id n) (B.map_id n)
  map_comp f g := Arrow.hom_ext _ _ (A.map_comp f g) (B.map_comp f g)

variable {n : SimplexCategory} (S : (SSet.stdSimplex.{v}.obj n).Subcomplex)

abbrev sourceMap := HomPresentation.tensorSourceMap (SubcomplexTensor.diagram S) α

def cocone : Cocone (SubcomplexTensor.diagram S ⋙ diagram α) where
  pt := Arrow.mk (sourceMap α S)
  ι := {
    app x := Arrow.homMk
      (colimit.ι (SubcomplexTensor.diagram S ⋙ A) x)
      (colimit.ι (SubcomplexTensor.diagram S ⋙ B) x)
      (HomPresentation.ι_tensorSourceMap _ α x)
    naturality x y f := by
      apply Arrow.hom_ext
      · change (SubcomplexTensor.diagram S ⋙ A).map f ≫ colimit.ι _ y =
          colimit.ι _ x ≫ 𝟙 _
        simpa only [Category.comp_id] using colimit.w (SubcomplexTensor.diagram S ⋙ A) f
      · change (SubcomplexTensor.diagram S ⋙ B).map f ≫ colimit.ι _ y =
          colimit.ι _ x ≫ 𝟙 _
        simpa only [Category.comp_id] using colimit.w (SubcomplexTensor.diagram S ⋙ B) f }

set_option backward.isDefEq.respectTransparency false in
def isColimit : IsColimit (cocone α S) :=
  Comma.fstSndJointlyReflectColimit
    (colimit.isColimit (SubcomplexTensor.diagram S ⋙ A))
    (colimit.isColimit (SubcomplexTensor.diagram S ⋙ B))

def objIso : SubcomplexTensor.obj S (diagram α) ≅ Arrow.mk (sourceMap α S) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (isColimit α S)

@[reassoc (attr := simp)]
lemma ι_objIso_hom (x : S.toSSet.N) :
    colimit.ι (SubcomplexTensor.diagram S ⋙ diagram α) x ≫ (objIso α S).hom =
      (cocone α S).ι.app x :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom (isColimit α S) x

abbrev inclusionSquare : Arrow.mk (sourceMap α S) ⟶ (diagram α).obj n :=
  Arrow.homMk (SubcomplexTensor.inclusion S A) (SubcomplexTensor.inclusion S B)
    (HomPresentation.tensorSourceMap_tensorMap _ α (SubcomplexTensor.simplexCocone S)).symm

lemma objIso_inclusionSquare :
    (objIso α S).hom ≫ inclusionSquare α S = SubcomplexTensor.inclusion S (diagram α) := by
  apply colimit.hom_ext
  intro x
  rw [← Category.assoc, ι_objIso_hom]
  change (cocone α S).ι.app x ≫ inclusionSquare α S =
    colimit.ι (SubcomplexTensor.diagram S ⋙ diagram α) x ≫
      colimit.desc _ ((diagram α).mapCocone (SubcomplexTensor.simplexCocone S))
  rw [colimit.ι_desc]
  apply Arrow.hom_ext
  · exact colimit.ι_desc _ x
  · exact colimit.ι_desc _ x

def inclusionArrowIso : Arrow.mk (SubcomplexTensor.inclusion S (diagram α)) ≅
    Arrow.mk (inclusionSquare α S) :=
  Arrow.isoMk (objIso α S) (Iso.refl ((diagram α).obj n)) (by
    change (objIso α S).hom ≫ inclusionSquare α S =
      SubcomplexTensor.inclusion S (diagram α) ≫ 𝟙 _
    rw [Category.comp_id, objIso_inclusionSquare])

end SerrePositivity.HomotopyFunctionComplex.ArrowTensor
