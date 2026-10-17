module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ParameterChoiceDiagram
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ComparisonTriangleTransport

/-! # A strict small parameter diagram with natural families of comparison triangles

The root triangle supplies a natural point by actual restriction. Whole
root choice families, and their relative extensions, transport naturally.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.ComparisonTriangleParameterDiagram
open KanComparisonTriangle
variable {T K : SSet.{v}} {f g z : T ⟶ K}
  (F : SSet.Homotopy f z) (G : SSet.Homotopy g z)

abbrev diagram : (Over T)ᵒᵖ ⥤ SSet.{v} :=
  ParameterChoiceDiagram.diagram T K (SSet.horn 2 2).ι (hornMap F G)

abbrev projection := ParameterChoiceDiagram.projection T K (SSet.horn 2 2).ι (hornMap F G)

abbrev family {L : SSet.{v}} (c : L ⟶ ComparisonTriangleChoices.obj F G) :=
  ParameterChoiceDiagram.family T K (SSet.horn 2 2).ι (hornMap F G) c

abbrev point (a : Data F G) :
    (Functor.const (Over T)ᵒᵖ).obj (SSet.stdSimplex.obj (SimplexCategory.mk 0)) ⟶ diagram F G :=
  ParameterChoiceDiagram.point T K (SSet.horn 2 2).ι (hornMap F G) a.triangle
    (Data.horn_restriction F G a)

lemma point_projection (a : Data F G) : point F G a ≫ projection F G = 𝟙 _ :=
  ParameterChoiceDiagram.point_projection _ _ _ _ _ _

def objectIso (σ : (Over T)ᵒᵖ) : (diagram F G).obj σ ≅
    ComparisonTriangleChoices.obj (HomotopyClasses.preHomotopy σ.unop.hom F)
      (HomotopyClasses.preHomotopy σ.unop.hom G) :=
  eqToIso (congrArg (fun b => RelativeChoiceSpace.obj (SSet.horn 2 2).ι b)
    (ComparisonTriangleTransport.hornMap_post F G _ _ ((pre σ.unop.hom).app K)
      (curry_pre_app σ.unop.hom F.h) (curry_pre_app σ.unop.hom G.h)))

def evaluated {L : SSet.{v}} (c : L ⟶ ComparisonTriangleChoices.obj F G) (σ : (Over T)ᵒᵖ) :
    σ.unop.left ⊗ (SSet.stdSimplex.obj (SimplexCategory.mk 2) ⊗ L) ⟶ K :=
  uncurry (RelativeChoiceSpace.family (SSet.horn 2 2).ι
    ((ParameterChoiceDiagram.parameterize T K (hornMap F G)).app σ) ((family F G c).app σ))

lemma evaluated_restriction {L : SSet.{v}} (c : L ⟶ ComparisonTriangleChoices.obj F G)
    (σ : (Over T)ᵒᵖ) : evaluated F G c σ =
    σ.unop.hom ▷ (SSet.stdSimplex.obj (SimplexCategory.mk 2) ⊗ L) ≫
      uncurry (ComparisonTriangleChoices.family F G c) := by
  rw [evaluated, ParameterChoiceDiagram.family_evaluation]
  exact uncurry_pre_app K (ComparisonTriangleChoices.family F G c) σ.unop.hom

variable (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

include hK in
lemma object_boundary_rlp (σ : (Over T)ᵒᵖ) : SSet.modelCategoryQuillen.I.rlp
    (terminal.from ((diagram F G).obj σ)) :=
  LocalizedRelativeChoice.boundary_rlp _ ComparisonTriangleChoices.horn_localized_isIso
    (SimplexParameterHom.native_kan σ.unop.left K hK) _

include hK in
lemma family_relative_extension {U V : SSet.{v}} (i : U ⟶ V) [Mono i]
    (c : U ⟶ ComparisonTriangleChoices.obj F G) :
    ∃ e : V ⟶ ComparisonTriangleChoices.obj F G, i ≫ e = c ∧
      (Functor.const (Over T)ᵒᵖ).map i ≫ family F G e = family F G c := by
  obtain ⟨e, he, _⟩ := ComparisonTriangleChoices.relative_extension F G hK i c
  refine ⟨e, he, ?_⟩
  apply NatTrans.ext
  funext σ
  change i ≫ (e ≫ (ParameterChoiceDiagram.transport T K _ (hornMap F G)).app σ) = _
  rw [← Category.assoc, he]
  rfl

include hK in
def pointIntervalData (a b : Data F G) :
    { q : SSet.stdSimplex.obj (SimplexCategory.mk 1) ⟶ ComparisonTriangleChoices.obj F G //
      SSet.stdSimplex.δ (1 : Fin 2) ≫ q = ComparisonTriangleChoices.ofData F G a ∧
      SSet.stdSimplex.δ (0 : Fin 2) ≫ q = ComparisonTriangleChoices.ofData F G b } := by
  let h := LocalizedRelativeChoice.interval (SSet.horn 2 2).ι
    ComparisonTriangleChoices.horn_localized_isIso (SimplexParameterHom.native_kan T K hK)
    (hornMap F G) (ComparisonTriangleChoices.ofData F G a) (ComparisonTriangleChoices.ofData F G b)
  exact ⟨h.choose, h.choose_spec⟩

abbrev pointInterval (a b : Data F G) := family F G (pointIntervalData F G hK a b).val

lemma pointInterval_zero (a b : Data F G) :
    (Functor.const (Over T)ᵒᵖ).map (SSet.stdSimplex.δ (1 : Fin 2)) ≫
      pointInterval F G hK a b = point F G a := by
  apply NatTrans.ext
  funext σ
  change SSet.stdSimplex.δ (1 : Fin 2) ≫
      ((pointIntervalData F G hK a b).val ≫
        (ParameterChoiceDiagram.transport T K _ (hornMap F G)).app σ) = _
  rw [← Category.assoc, (pointIntervalData F G hK a b).property.1]
  rfl

lemma pointInterval_one (a b : Data F G) :
    (Functor.const (Over T)ᵒᵖ).map (SSet.stdSimplex.δ (0 : Fin 2)) ≫
      pointInterval F G hK a b = point F G b := by
  apply NatTrans.ext
  funext σ
  change SSet.stdSimplex.δ (0 : Fin 2) ≫
      ((pointIntervalData F G hK a b).val ≫
        (ParameterChoiceDiagram.transport T K _ (hornMap F G)).app σ) = _
  rw [← Category.assoc, (pointIntervalData F G hK a b).property.2]
  rfl

end SerrePositivity.SimplicialModel.ComparisonTriangleParameterDiagram
