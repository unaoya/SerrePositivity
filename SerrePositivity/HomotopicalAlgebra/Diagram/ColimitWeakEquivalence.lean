module

public import SerrePositivity.HomotopicalAlgebra.Smith.WeakEquivalencesAccessible
public import Mathlib.CategoryTheory.Limits.Comma

/-! # Actual colimit maps from filtered-colimit closure in the arrow category -/

@[expose] public section
universe w s t v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.DiagramModel
variable {C : Type u} [Category.{v} C] {K : Type t} [Category.{s} K]

def arrowDiagram {F G : K ⥤ C} (α : F ⟶ G) : K ⥤ Arrow C where
  obj k := Arrow.mk (α.app k)
  map f := Arrow.homMk (F.map f) (G.map f) (α.naturality f)
  map_id k := by ext <;> simp
  map_comp f g := by ext <;> simp

def arrowColimitCocone [HasColimitsOfShape K C] {F G : K ⥤ C} (α : F ⟶ G) :
    Cocone (arrowDiagram α) where
  pt := Arrow.mk (colim.map α)
  ι :=
    { app k := Arrow.homMk (colimit.ι F k) (colimit.ι G k) (colimit.ι_map α k)
      naturality k l f := by
        apply Arrow.hom_ext
        · exact (colimit.w F f).trans (Category.comp_id _).symm
        · exact (colimit.w G f).trans (Category.comp_id _).symm }

def arrowColimitCoconeIsColimit [HasColimitsOfShape K C] {F G : K ⥤ C} (α : F ⟶ G) :
    IsColimit (arrowColimitCocone α) :=
  Comma.fstSndJointlyReflectColimit (colimit.isColimit F) (colimit.isColimit G)

lemma colimitMap_mem [HasColimitsOfShape K C] (W : MorphismProperty C)
    [(Smith.arrowProperty W).IsClosedUnderColimitsOfShape K]
    {F G : K ⥤ C} (α : F ⟶ G) (hα : ∀ k, W (α.app k)) : W (colim.map α) :=
  (Smith.arrowProperty W).prop_of_isColimit (arrowColimitCoconeIsColimit α) hα

variable [HomotopicalAlgebra.ModelCategory C]

/-- Accessibility of the original W and its full inclusion gives preservation
of weak equivalences by the actual sufficiently filtered colimit functor. -/
lemma filtered_colimitMap_weakEquivalence (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [HasCardinalFilteredColimits.{w}
      (Smith.arrowProperty (HomotopicalAlgebra.weakEquivalences C)).FullSubcategory κ]
    [(Smith.arrowInclusion (HomotopicalAlgebra.weakEquivalences C)).IsCardinalAccessible κ]
    {K : Type w} [SmallCategory K] [IsCardinalFiltered K κ] [HasColimitsOfShape K C]
    {F G : K ⥤ C} (α : F ⟶ G) (hα : ∀ k, HomotopicalAlgebra.weakEquivalences C (α.app k)) :
    HomotopicalAlgebra.weakEquivalences C (colim.map α) := by
  let P := Smith.arrowProperty (HomotopicalAlgebra.weakEquivalences C)
  have : P.IsClosedUnderIsomorphisms :=
    { of_iso := fun e h ↦ ((HomotopicalAlgebra.weakEquivalences C).arrow_mk_iso_iff e).mp h }
  have : HasColimitsOfShape K P.FullSubcategory :=
    HasCardinalFilteredColimits.hasColimitsOfShape _ κ K
  have := Functor.preservesColimitsOfShape_of_isCardinalAccessible P.ι κ K
  have := ObjectProperty.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι P K
  exact colimitMap_mem _ α hα

end SerrePositivity.DiagramModel
