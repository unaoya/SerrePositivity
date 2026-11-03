module
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # PerfとKaroubi延長の本質像・完全忠実性・shift整合性検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Idempotents
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) : (finiteCellKaroubiFunctor A D S).Full := inferInstance
example (S : Set D) : (finiteCellKaroubiFunctor A D S).Faithful := inferInstance
example (S : Set D) : (finiteCellKaroubiFunctor A D S).CommShift ℤ := inferInstance
example (S : Set D) : NatTrans.CommShift (finiteCellKaroubiFunctor_fac A D S).hom ℤ := inferInstance

example (S : Set D) (X : DerivedModuleCategory A D) :
    modulePerfectOver A D S X ↔ (finiteCellKaroubiFunctor A D S).essImage
      ((toKaroubi (DerivedModuleCategory A D)).obj X) :=
  modulePerfectOver_iff_karoubi_essImage A D S X

example (X : DerivedModuleCategory (ZMod 2) PUnit.{1}) :
    modulePerfect (ZMod 2) PUnit.{1} X ↔
      (finiteCellKaroubiFunctor (ZMod 2) PUnit.{1} Set.univ).essImage
        ((toKaroubi (DerivedModuleCategory (ZMod 2) PUnit.{1})).obj X) :=
  modulePerfect_iff_karoubi_essImage (ZMod 2) PUnit.{1} X

#print axioms DerivedFiniteCellCategoryOver
#print axioms derivedFiniteCellInclusion
#print axioms derivedFiniteCellInclusionFull
#print axioms derivedFiniteCellInclusionFaithful
#print axioms derivedFiniteCellInclusionCommShift
#print axioms finiteCellKaroubiFunctor
#print axioms finiteCellKaroubiFunctorFull
#print axioms finiteCellKaroubiFunctorFaithful
#print axioms finiteCellKaroubiFunctor_fac
#print axioms modulePerfectOver_iff_karoubi_essImage
#print axioms finiteCellKaroubiFunctorCommShift
#print axioms finiteCellKaroubiFunctorFacCommShift
#print axioms modulePerfect_iff_karoubi_essImage
