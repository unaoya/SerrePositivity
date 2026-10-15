module
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Comparison of a chosen cokernel with the final term of a short exact sequence -/
@[expose] public noncomputable section
namespace SerrePositivity
open CategoryTheory Category Limits

/-- Compare the chosen cokernel of a short exact sequence with its final object. -/
def shortExactCokernelIso
    {C : Type*} [Category C] [Abelian C] (T : ShortComplex C) (hT : T.ShortExact) :
    cokernel T.f ≅ T.X₃ :=
  (cokernelIsCokernel T.f).coconePointUniqueUpToIso hT.gIsCokernel

@[reassoc]
lemma shortExactCokernelIso_π_hom
    {C : Type*} [Category C] [Abelian C] (T : ShortComplex C) (hT : T.ShortExact) :
    cokernel.π T.f ≫ (shortExactCokernelIso T hT).hom = T.g :=
  (cokernelIsCokernel T.f).comp_coconePointUniqueUpToIso_hom
    hT.gIsCokernel WalkingParallelPair.one

namespace Adams

/-- Compatibility name for the common short exact cokernel comparison. -/
abbrev shortExactCokernelIso
    {C : Type*} [Category C] [Abelian C] (T : ShortComplex C) (hT : T.ShortExact) :
    cokernel T.f ≅ T.X₃ := SerrePositivity.shortExactCokernelIso T hT

end Adams
end SerrePositivity
