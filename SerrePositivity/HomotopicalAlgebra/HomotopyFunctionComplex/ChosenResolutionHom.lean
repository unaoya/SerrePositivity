module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.ResolutionHom
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution
public import SerrePositivity.HomotopicalAlgebra.Generated.Replacement

/-! # Simplicial Hom from actual chosen source factorizations

This constructs the candidate with n-simplices `Q(X)[n] ⟶ R(Y)`.
Chosen source factorizations are explicit inputs. `HornTensor` proves Kan
fibrancy, and `SourceInvariance` proves invariance in both variables using an
explicit simplicial value model. `PiZero` proves the natural comparison of
components with ordinary localization morphisms. This conditional construction
is not the arbitrary-model-source F1 theorem.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C]

abbrev fibrantTarget
    (source : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)) :
    C ⥤ C := ModelReplacement.terminalArrows C ⋙ source.Z

def fibrantTargetComparison
    (source : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)) :
    𝟭 C ⟶ fibrantTarget source where
  app X := source.i.app (Arrow.mk (terminal.from X))
  naturality {_ _} f := source.i.naturality ((ModelReplacement.terminalArrows C).map f)

lemma fibrantTargetComparison_weakEquivalence
    (source : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X : C) : weakEquivalences C ((fibrantTargetComparison source).app X) :=
  (source.hi (Arrow.mk (terminal.from X))).2

lemma fibrantTarget_isFibrant
    (source : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X : C) : IsFibrant ((fibrantTarget source).obj X) :=
  (isFibrant_iff_of_isTerminal (source.p.app (Arrow.mk (terminal.from X))) terminalIsTerminal).mpr
    ⟨source.hp _⟩

lemma fibrantTarget_map_weakEquivalence
    (source : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    weakEquivalences C ((fibrantTarget source).map f) := by
  have h := (fibrantTargetComparison source).naturality f
  have hc := (weakEquivalences C).comp_mem f ((fibrantTargetComparison source).app Y) hf
    (fibrantTargetComparison_weakEquivalence source Y)
  exact (weakEquivalences C).of_precomp _ _
    (fibrantTargetComparison_weakEquivalence source X) (h ▸ hc)

abbrev chosenResolutionHom
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)) :
    Cᵒᵖ ⥤ C ⥤ SSet.{v} :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom (Reedy.cosimplicialResolutionFamily cof).obj (fibrantTarget fib)

end SerrePositivity.HomotopyFunctionComplex
