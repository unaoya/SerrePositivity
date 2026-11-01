module
public import Mathlib.AlgebraicTopology.ModelCategory.Basic

public import SerrePositivity.HomotopicalAlgebra.Simplicial.GeneratedLeftClass
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-! # Actual functorial cofibrant and fibrant replacements

The chosen functorial model factorizations are restricted to arrows from the
initial object and to the terminal object. Their comparison maps are natural
transformations, rather than independent objectwise choices.
-/

@[expose] public section
universe u v
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
namespace SerrePositivity.ModelReplacement
variable (C : Type u) [Category.{v} C] [ModelCategory C]

def initialArrows : C ⥤ Arrow C where
  obj X := Arrow.mk (initial.to X)
  map f := Arrow.homMk (𝟙 _) f (by simp)

def terminalArrows : C ⥤ Arrow C where
  obj X := Arrow.mk (terminal.from X)
  map f := Arrow.homMk f (𝟙 _) (by simp)

section Cofibrant
variable [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]

def cofibrantReplacement : C ⥤ C := initialArrows C ⋙
  (MorphismProperty.functorialFactorizationData (cofibrations C) (trivialFibrations C)).Z

def cofibrantComparison : cofibrantReplacement C ⟶ 𝟭 C where
  app X := (MorphismProperty.functorialFactorizationData
    (cofibrations C) (trivialFibrations C)).p.app (Arrow.mk (initial.to X))
  naturality {_X _Y} f := (MorphismProperty.functorialFactorizationData
    (cofibrations C) (trivialFibrations C)).p.naturality ((initialArrows C).map f)

lemma cofibrantReplacement_isCofibrant (X : C) : IsCofibrant ((cofibrantReplacement C).obj X) := by
  let d := MorphismProperty.functorialFactorizationData (cofibrations C) (trivialFibrations C)
  exact (isCofibrant_iff_of_isInitial (d.i.app (Arrow.mk (initial.to X))) initialIsInitial).2
    ((cofibration_iff _).2 (d.hi _))

lemma cofibrantComparison_trivialFibration (X : C) :
    trivialFibrations C ((cofibrantComparison C).app X) :=
  (MorphismProperty.functorialFactorizationData
    (cofibrations C) (trivialFibrations C)).hp (Arrow.mk (initial.to X))
end Cofibrant

section Fibrant
variable [(trivialCofibrations C).HasFunctorialFactorization (fibrations C)]

def fibrantReplacement : C ⥤ C := terminalArrows C ⋙
  (MorphismProperty.functorialFactorizationData (trivialCofibrations C) (fibrations C)).Z

def fibrantComparison : 𝟭 C ⟶ fibrantReplacement C where
  app X := (MorphismProperty.functorialFactorizationData
    (trivialCofibrations C) (fibrations C)).i.app (Arrow.mk (terminal.from X))
  naturality {_X _Y} f := (MorphismProperty.functorialFactorizationData
    (trivialCofibrations C) (fibrations C)).i.naturality ((terminalArrows C).map f)

lemma fibrantReplacement_isFibrant (X : C) : IsFibrant ((fibrantReplacement C).obj X) := by
  let d := MorphismProperty.functorialFactorizationData (trivialCofibrations C) (fibrations C)
  exact (isFibrant_iff_of_isTerminal (d.p.app (Arrow.mk (terminal.from X))) terminalIsTerminal).2
    ((fibration_iff _).2 (d.hp _))

lemma fibrantComparison_trivialCofibration (X : C) :
    trivialCofibrations C ((fibrantComparison C).app X) :=
  (MorphismProperty.functorialFactorizationData
    (trivialCofibrations C) (fibrations C)).hi (Arrow.mk (terminal.from X))
end Fibrant

end SerrePositivity.ModelReplacement
