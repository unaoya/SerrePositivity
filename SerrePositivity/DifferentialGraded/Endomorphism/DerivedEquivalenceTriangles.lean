module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedEquivalence

/-! # 全主導来圏同値の実際のshiftと三角性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (compactToPerfect : ∀ P : DerivedModuleCategory A (EndomorphismObject E.val),
  moduleCompact A (EndomorphismObject E.val) P →
    modulePerfect A (EndomorphismObject E.val) P)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)
variable (hCG : endomorphismCompactGenerator A D E.val)

local instance :
    (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).inverse.CommShift ℤ :=
  endomorphismDerivedHomCommShift A D E.val E.property.1

/-- 同値の両側に既存の実際のtensor/Hom shiftを使う。 -/
lemma endomorphismDerivedEquivalence_commShift :
    letI : (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).functor.CommShift ℤ :=
      endomorphismDerivedTensorCommShift A D E.val E.property.1
    (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).CommShift ℤ := by
  let : (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).functor.CommShift ℤ :=
    endomorphismDerivedTensorCommShift A D E.val E.property.1
  let := endomorphismDerivedTensorCommShift A D E.val E.property.1
  let := endomorphismDerivedHomCommShift A D E.val E.property.1
  apply Equivalence.CommShift.mk'
  change NatTrans.CommShift (endomorphismDerivedUnit A D E.val E.property.1) ℤ
  exact endomorphismDerivedUnit_commShift A D E.val E.property.1

lemma endomorphismDerivedEquivalence_isTriangulated :
    letI : (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).functor.CommShift ℤ :=
      endomorphismDerivedTensorCommShift A D E.val E.property.1
    letI := endomorphismDerivedEquivalence_commShift A D S E compactToPerfect hgen hCG
    (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).IsTriangulated := by
  let : (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).functor.CommShift ℤ :=
    endomorphismDerivedTensorCommShift A D E.val E.property.1
  let := endomorphismDerivedEquivalence_commShift A D S E compactToPerfect hgen hCG
  exact Equivalence.IsTriangulated.mk' _
    (endomorphismDerivedTensorIsTriangulated A D E.val E.property.1)

/-- 同値のtensorをPerfへ制限した正方形は、既存の実際のtensor制限と一致する。 -/
def endomorphismDerivedEquivalencePerfectTensorSquare :
    perfectEndomorphismTensorToPerfect A D S E ⋙ perfectModuleInclusion A D S ≅
      perfectModuleInclusion A (EndomorphismObject E.val) Set.univ ⋙
        (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).functor :=
  perfectEndomorphismTensorInclusionIso A D S E

/-- 逆関手HomのPerf包含正方形も、既存のPerf比較そのもの。 -/
def endomorphismDerivedEquivalencePerfectHomSquare :
    perfectEndomorphismHomToPerfect A D S E hgen ⋙
        perfectModuleInclusion A (EndomorphismObject E.val) Set.univ ≅
      perfectModuleInclusion A D S ⋙
        (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).inverse :=
  perfectEndomorphismHomInclusionIso A D S E hgen

end SerrePositivity.DifferentialGraded
