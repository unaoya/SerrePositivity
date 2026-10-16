module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.FiberFunctor

/-! # Reindexing actual fiber diagrams and changing equal point families -/

@[expose] public section
universe v uD vD uE vE
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.FiberFunctor
variable {D : Type uD} [Category.{vD} D] {F G : D ⥤ SSet.{v}} (p : F ⟶ G)
  (b : (Functor.const D).obj (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) ⟶ G)

/-- Objectwise chosen pullbacks reindex to exactly the corresponding fiber diagram. -/
def reindex {E : Type uE} [Category.{vE} E] (H : E ⥤ D) :
    H ⋙ functor p b ≅ functor (Functor.whiskerLeft H p) (Functor.whiskerLeft H b) := Iso.refl _

def congrPoint
    (b' : (Functor.const D).obj (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) ⟶ G)
    (h : b = b') : functor p b ≅ functor p b' := eqToIso (congrArg (fun c => functor p c) h)

end SerrePositivity.SimplicialModel.FiberFunctor
