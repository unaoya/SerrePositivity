module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedEquivalenceTriangles
public import SerrePositivity.DifferentialGraded.Perfect.CompactConverse

/-! # U13dを適用しcompact⇒Perf入力を除いたU14c

既存の入力付きAPIは保持する。Endの対象型は一対象なのでSmall.{u}の条件を満たす。
指定集合Sのthick生成と、全導来圏のcompact生成はそれぞれ明示する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits

lemma endomorphismCompactToPerfect (A : Type u) [CommRing A]
    {C : Type*} [DGCategory A C] (E : C)
    (N : DerivedModuleCategory A (EndomorphismObject E))
    (hN : moduleCompact A (EndomorphismObject E) N) :
    modulePerfect A (EndomorphismObject E) N :=
  (moduleCompact_iff_perfect A (EndomorphismObject E) N).1 hN

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)

lemma perfectEndomorphismHom_preservesCoproduct_ofPerfect {J : Type u}
    (F : J → DerivedModuleCategory A D) :
    PreservesColimit (Discrete.functor F) (endomorphismDerivedHom A D E.val E.property.1) :=
  perfectEndomorphismHom_preservesCoproduct A D S E (endomorphismCompactToPerfect A E.val) F

variable (hgen : endomorphismThickGeneratesPerfect A D S E)
include hgen

lemma endomorphismDerivedUnit_isIso_of_compact_ofThickGenerator
    (N : DerivedModuleCategory A (EndomorphismObject E.val))
    (hN : moduleCompact A (EndomorphismObject E.val) N) :
    IsIso ((endomorphismDerivedUnit A D E.val E.property.1).app N) :=
  endomorphismDerivedUnit_isIso_of_compact A D S E hgen
    (endomorphismCompactToPerfect A E.val) N hN

lemma endomorphismDerivedUnit_isIso_all_ofThickGenerator
    (N : DerivedModuleCategory A (EndomorphismObject E.val)) :
    IsIso ((endomorphismDerivedUnit A D E.val E.property.1).app N) :=
  endomorphismDerivedUnit_isIso_all A D S E (endomorphismCompactToPerfect A E.val) hgen N

variable (hCG : endomorphismCompactGenerator A D E.val)
include hCG

lemma endomorphismDerivedCounit_isIso_all_ofCompactGenerator (X : DerivedModuleCategory A D) :
    IsIso ((endomorphismDerivedCounit A D E.val E.property.1).app X) :=
  endomorphismDerivedCounit_isIso_all A D S E (endomorphismCompactToPerfect A E.val) hgen hCG X

def endomorphismDerivedEquivalence_ofCompactGenerator :
    DerivedModuleCategory A (EndomorphismObject E.val) ≌ DerivedModuleCategory A D :=
  endomorphismDerivedEquivalence A D S E (endomorphismCompactToPerfect A E.val) hgen hCG

lemma endomorphismDerivedEquivalence_ofCompactGenerator_functor :
    (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).functor =
      endomorphismDerivedTensor A D E.val := rfl

lemma endomorphismDerivedEquivalence_ofCompactGenerator_inverse :
    (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).inverse =
      endomorphismDerivedHom A D E.val E.property.1 := rfl

lemma endomorphismDerivedEquivalence_ofCompactGenerator_unit :
    (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).unitIso.hom =
      endomorphismDerivedUnit A D E.val E.property.1 := rfl

lemma endomorphismDerivedEquivalence_ofCompactGenerator_counit :
    (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).counitIso.hom =
      endomorphismDerivedCounit A D E.val E.property.1 := rfl

local instance :
    (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).inverse.CommShift ℤ :=
  endomorphismDerivedHomCommShift A D E.val E.property.1

lemma endomorphismDerivedEquivalence_ofCompactGenerator_commShift :
    letI : (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).functor.CommShift
        ℤ :=
      endomorphismDerivedTensorCommShift A D E.val E.property.1
    (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).CommShift ℤ :=
  endomorphismDerivedEquivalence_commShift A D S E (endomorphismCompactToPerfect A E.val) hgen hCG

lemma endomorphismDerivedEquivalence_ofCompactGenerator_isTriangulated :
    letI : (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).functor.CommShift
        ℤ :=
      endomorphismDerivedTensorCommShift A D E.val E.property.1
    letI := endomorphismDerivedEquivalence_ofCompactGenerator_commShift A D S E hgen hCG
    (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).IsTriangulated :=
  endomorphismDerivedEquivalence_isTriangulated A D S E
    (endomorphismCompactToPerfect A E.val) hgen hCG

def endomorphismDerivedEquivalence_ofCompactGenerator_PerfectTensorSquare :
    perfectEndomorphismTensorToPerfect A D S E ⋙ perfectModuleInclusion A D S ≅
      perfectModuleInclusion A (EndomorphismObject E.val) Set.univ ⋙
        (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).functor :=
  endomorphismDerivedEquivalencePerfectTensorSquare A D S E
    (endomorphismCompactToPerfect A E.val) hgen hCG

def endomorphismDerivedEquivalence_ofCompactGenerator_PerfectHomSquare :
    perfectEndomorphismHomToPerfect A D S E hgen ⋙
        perfectModuleInclusion A (EndomorphismObject E.val) Set.univ ≅
      perfectModuleInclusion A D S ⋙
        (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).inverse :=
  endomorphismDerivedEquivalencePerfectHomSquare A D S E
    (endomorphismCompactToPerfect A E.val) hgen hCG

end SerrePositivity.DifferentialGraded
