module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SimplicialMapComparison

/-! # The enriched Map comparison from explicit source factorization data

Both Q and R are restrictions of the supplied source factorizations.
No independent replacement functors or frame hypotheses are required.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C]

abbrev cofibrantSource
    (source : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    C ⥤ C := ModelReplacement.initialArrows C ⋙ source.Z

def cofibrantSourceComparison
    (source : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    cofibrantSource source ⟶ 𝟭 C where
  app X := source.p.app (Arrow.mk (initial.to X))
  naturality {_ _} f := source.p.naturality ((ModelReplacement.initialArrows C).map f)

lemma cofibrantSource_isCofibrant
    (source : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (X : C) : IsCofibrant ((cofibrantSource source).obj X) :=
  (isCofibrant_iff_of_isInitial (source.i.app (Arrow.mk (initial.to X))) initialIsInitial).mpr
    ⟨source.hi _⟩

lemma cofibrantSourceComparison_trivialFibration
    (source : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (X : C) : trivialFibrations C ((cofibrantSourceComparison source).app X) :=
  source.hp (Arrow.mk (initial.to X))

namespace ChosenMapComparison
variable [EnrichedOrdinaryCategory SSet.{v} C] [ModelCategory SSet.{v}]
  (S : SerrePositivity.Enriched.TensorCotensor SSet.{v} C)
  [SerrePositivity.Quillen.IsQuillenBifunctor S.tensor]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hw : weakEquivalences SSet.{v} = SimplicialHomotopy.weakEquivalences)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

abbrev frame := SimplicialMapComparison.tensorFrame S hcof hw
  (cofibrantSource cof) (cofibrantSourceComparison cof) (cofibrantSource_isCofibrant cof)
  (fun X ↦ (cofibrantSourceComparison_trivialFibration cof X).2)

abbrev middle : Cᵒᵖ ⥤ C ⥤ SSet.{v} :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom (FrameComparison.commonObj cof (Reedy.cosimplicialResolutionFamily cof)
    (frame S hcof hw cof)) (fibrantTarget fib)

abbrev fromResolution : chosenResolutionHom cof fib ⟶ middle S hcof hw cof fib :=
  FrameComparison.homLeft cof (Reedy.cosimplicialResolutionFamily cof)
    (frame S hcof hw cof) (fibrantTarget fib)

abbrev fromMap : enrichedReplacementHom (cofibrantSource cof) (fibrantTarget fib) ⟶
    middle S hcof hw cof fib :=
  SimplicialMapComparison.fromMap S hcof hw (cofibrantSource cof)
    (cofibrantSourceComparison cof) (cofibrantSource_isCofibrant cof)
    (fun X ↦ (cofibrantSourceComparison_trivialFibration cof X).2) cof
    (Reedy.cosimplicialResolutionFamily cof) (fibrantTarget fib)

lemma middle_kanComplex (X : Cᵒᵖ) (Y : C) :
    SSet.KanComplex (((middle S hcof hw cof fib).obj X).obj Y) :=
  FrameComparison.commonHom_kanComplex cof (Reedy.cosimplicialResolutionFamily cof)
    (frame S hcof hw cof) (fibrantTarget fib) (fibrantTarget_isFibrant fib) X Y

lemma geometricWeakEquivalences (X : Cᵒᵖ) (Y : C) :
    SimplicialHomotopy.weakEquivalences
        (((fromResolution S hcof hw cof fib).app X).app Y) ∧
      SimplicialHomotopy.weakEquivalences
        (((fromMap S hcof hw cof fib).app X).app Y) := by
  constructor
  · rw [← hw]
    exact FrameComparison.homLeft_weakEquivalence cof (Reedy.cosimplicialResolutionFamily cof)
      (frame S hcof hw cof) hcof (fibrantTarget fib) (fibrantTarget_isFibrant fib) X Y
  · exact SimplicialMapComparison.fromMap_weakEquivalence S hcof hw (cofibrantSource cof)
      (cofibrantSourceComparison cof) (cofibrantSource_isCofibrant cof)
      (fun X ↦ (cofibrantSourceComparison_trivialFibration cof X).2) cof
      (Reedy.cosimplicialResolutionFamily cof) (fibrantTarget fib)
      (fibrantTarget_isFibrant fib) X Y

end ChosenMapComparison
end SerrePositivity.HomotopyFunctionComplex
