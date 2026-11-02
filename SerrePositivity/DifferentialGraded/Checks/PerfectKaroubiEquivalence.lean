module
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # finite cellのKaroubi包絡とPerfの三角同値の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Idempotents
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) : IsIdempotentComplete (PerfectModuleCategoryOver A D S) := inferInstance

example (S : Set D) :
    (finiteCellKaroubiPerfectEquivalence A D S).inverse.IsTriangulated := inferInstance

example (S : Set D) :
    NatTrans.CommShift (finiteCellKaroubiPerfectEquivalence A D S).unitIso.hom ℤ := inferInstance

example (S : Set D) :
    NatTrans.CommShift (finiteCellKaroubiPerfectEquivalence A D S).counitIso.hom ℤ := inferInstance

example (S : Set D) (X : PerfectModuleCategoryOver A D S) :
    ∃ P : Karoubi (DerivedFiniteCellCategoryOver A D S),
      Nonempty ((finiteCellKaroubiToPerfect A D S).obj P ≅ X) :=
  Functor.EssSurj.mem_essImage (finiteCellKaroubiToPerfect A D S) X

example (S : Set D) (P : Karoubi (DerivedFiniteCellCategoryOver A D S)) :
    modulePerfectOver A D S ((finiteCellKaroubiRealization A D S).obj P) :=
  finiteCellKaroubiRealization_perfect A D S P

example : IsIdempotentComplete (PerfectModuleCategory (ZMod 2) PUnit.{1}) := inferInstance
example : (finiteCellKaroubiPerfectEquivalence (ZMod 2) PUnit.{1} Set.univ).IsTriangulated :=
  inferInstance

#print axioms moduleDerivedKaroubiEquivalence
#print axioms moduleDerivedKaroubiEquivalenceFunctorCommShift
#print axioms moduleDerivedKaroubiEquivalenceInverseCommShift
#print axioms moduleDerivedKaroubiEquivalenceCommShift
#print axioms moduleDerivedKaroubiEquivalenceIsTriangulated
#print axioms finiteCellKaroubiRealization
#print axioms finiteCellKaroubiRealizationFull
#print axioms finiteCellKaroubiRealizationFaithful
#print axioms finiteCellKaroubiRealizationCommShift
#print axioms finiteCellKaroubiRealizationIsTriangulated
#print axioms finiteCellKaroubiRealizationToKaroubiIso
#print axioms finiteCellKaroubiRealizationToKaroubiIsoCommShift
#print axioms finiteCellKaroubiRealization_fac
#print axioms finiteCellKaroubiRealizationFacCommShift
#print axioms finiteCellKaroubiRealization_perfect
#print axioms finiteCellKaroubiToPerfect
#print axioms finiteCellKaroubiToPerfectFull
#print axioms finiteCellKaroubiToPerfectFaithful
#print axioms finiteCellKaroubiToPerfectEssSurj
#print axioms finiteCellKaroubiToPerfectIsEquivalence
#print axioms finiteCellKaroubiToPerfectCommShift
#print axioms finiteCellKaroubiToPerfectIsTriangulated
#print axioms finiteCellKaroubiToPerfectCompInclusion
#print axioms finiteCellKaroubiToPerfectCompInclusionCommShift
#print axioms finiteCellKaroubiPerfectEquivalence
#print axioms finiteCellKaroubiPerfectEquivalenceFunctorCommShift
#print axioms finiteCellKaroubiPerfectEquivalenceInverseCommShift
#print axioms finiteCellKaroubiPerfectEquivalenceCommShift
#print axioms finiteCellKaroubiPerfectEquivalenceIsTriangulated
#print axioms perfectModuleCategoryOverIsIdempotentComplete
