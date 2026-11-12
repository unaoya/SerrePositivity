module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SimplicialTensorAugmentation

/-! # Natural weak comparison with actual enriched mapping spaces

For any supplied cofibrant replacement Q, the standard tensor frame is
weakly augmented over the identity. A common cofibrant frame compares it
with an arbitrary strong resolution family. The resulting cospan consists
of natural transformations of actual bifunctors, with actual enriched Map
as one endpoint. Source functorial factorization is explicit input.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.SimplicialMapComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [EnrichedOrdinaryCategory SSet.{v} C] [ModelCategory SSet.{v}]
  (S : SerrePositivity.Enriched.TensorCotensor SSet.{v} C)
  [SerrePositivity.Quillen.IsQuillenBifunctor S.tensor]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hw : weakEquivalences SSet.{v} = SimplicialHomotopy.weakEquivalences)
  (Q : C ⥤ C) (ε : Q ⟶ 𝟭 C)
  (hQ : ∀ X, IsCofibrant (Q.obj X)) (hε : ∀ X, weakEquivalences C (ε.app X))

def tensorFrame : CosimplicialFrameFamily (C := C) where
  obj := Q ⋙ tensorCosimplicialFamily S
  augmentation := Functor.whiskerLeft Q (tensorAugmentation S) ≫
    Functor.whiskerRight ε (Functor.const SimplexCategory)
  cofibrant X := by
    have := hQ X
    exact tensorCosimplicial_reedyCofibrant S hcof (Q.obj X)
  weak X n := by
    have := hQ X
    exact (weakEquivalences C).comp_mem _ _
      (tensorAugmentation_weakEquivalence S hcof hw (Q.obj X) n) (hε X)

variable
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (q : CofibrantResolutionFamily (C := C) simplex) (R : C ⥤ C)

abbrev middle : Cᵒᵖ ⥤ C ⥤ SSet.{v} :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom (FrameComparison.commonObj cof q (tensorFrame S hcof hw Q ε hQ hε)) R

abbrev fromResolution : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom q.obj R ⟶ middle S hcof hw Q ε hQ hε cof q R :=
  FrameComparison.homLeft cof q (tensorFrame S hcof hw Q ε hQ hε) R

def fromMap : enrichedReplacementHom Q R ⟶ middle S hcof hw Q ε hQ hε cof q R :=
  (replacedTensorHomIso S Q R).inv ≫
    FrameComparison.homRight cof q (tensorFrame S hcof hw Q ε hQ hε) R

lemma middle_kanComplex (hR : ∀ Y, IsFibrant (R.obj Y)) (X : Cᵒᵖ) (Y : C) :
    SSet.KanComplex (((middle S hcof hw Q ε hQ hε cof q R).obj X).obj Y) :=
  FrameComparison.commonHom_kanComplex cof q (tensorFrame S hcof hw Q ε hQ hε) R hR X Y

lemma fromResolution_weakEquivalence (hR : ∀ Y, IsFibrant (R.obj Y)) (X : Cᵒᵖ) (Y : C) :
    SimplicialHomotopy.weakEquivalences
      (((fromResolution S hcof hw Q ε hQ hε cof q R).app X).app Y) := by
  rw [← hw]
  exact FrameComparison.homLeft_weakEquivalence cof q
    (tensorFrame S hcof hw Q ε hQ hε) hcof R hR X Y

lemma fromMap_weakEquivalence (hR : ∀ Y, IsFibrant (R.obj Y)) (X : Cᵒᵖ) (Y : C) :
    SimplicialHomotopy.weakEquivalences
      (((fromMap S hcof hw Q ε hQ hε cof q R).app X).app Y) := by
  rw [← hw]
  change weakEquivalences SSet.{v}
    (((replacedTensorHomIso S Q R).inv.app X).app Y ≫
      ((FrameComparison.homRight cof q (tensorFrame S hcof hw Q ε hQ hε) R).app X).app Y)
  have : IsIso (((replacedTensorHomIso S Q R).inv.app X).app Y) :=
    inferInstanceAs (IsIso (((replacedTensorHomIso S Q R).app X).app Y).inv)
  exact (weakEquivalences SSet.{v}).comp_mem _ _
    ((weakEquivalences SSet.{v}).of_isIso _)
    (FrameComparison.homRight_weakEquivalence cof q
      (tensorFrame S hcof hw Q ε hQ hε) hcof R hR X Y)

end SerrePositivity.HomotopyFunctionComplex.SimplicialMapComparison
