module

public import SerrePositivity.EInfinity.PowerOperation.ComplexRelativeElementTransport
public import SerrePositivity.EInfinity.PowerOperation.ComplexRelativeElementReference
public import SerrePositivity.EInfinity.PowerOperation.ComplexRelativeElementWeak
public import SerrePositivity.EInfinity.FrameHom.PinchedFamilyWeakDetection
public import SerrePositivity.EInfinity.ComplexLimits.ProbeKProjectiveValues

/-!
# 指定複体 hammock 比較の同じ pinched 誘導射の弱同値性

DAG XIII §2.2 の native な降下の核心。指定 sourceIso で運んだ全族を元の弱な
基準族と同じ全関手の射として照合し、実際の比較関手の誘導射を検出する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open FullFaithfulAndEssentiallySurjectiveFunctors (pinchedHomMap)
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors
open AdjointFunctorsBetweenInfinityCategories (intervalFamilyHom)
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma complexRelativeElementDerivedPinchedMap_reference_family (X Y : Complex A) :
    intervalFamilyHom (complexRelativeElementDerivedPinchedMap A X Y ≫
      MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) =
    intervalFamilyHom (complexRelativeElementReferencePinchedMap A X Y ≫
      MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) := by
  apply Arrow.mk_injective _ _
  exact (complexRelativeElementDerivedPinchedMap_roof_arrow A X Y).trans
    ((complexRelativeElementDerivedRoof_arrow A X Y).trans
      (complexRelativeElementReferencePinchedMap_roof_arrow A X Y).symm)

lemma complexRelativeElementDerivedPinchedMap_weak (X Y : KProjectiveComplex A) :
    IsWeakHomotopyEquivalence (complexRelativeElementDerivedPinchedMap A X.val Y.val) :=
  FrameHom.pinchedFamily_weak_of_intervalFamilyHom_eq _ _
    (complexRelativeElementReferencePinchedMap_weak A X Y)
    (complexRelativeElementDerivedPinchedMap_reference_family A X.val Y.val)

lemma complexHammockDerivedComparison_probe_pinched_weak
    (X : Complex A) (Y : KProjectiveComplex A) :
    IsWeakHomotopyEquivalence (pinchedHomMap (complexHammockDerivedComparison A)
      ((complexHammockSource A).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ ((complexRelativeUp A).obj ((framedLimitProbeFunctor A).obj X))))
      ((complexHammockSource A).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ ((complexRelativeUp A).obj Y.val)))) := by
  have hd := complexRelativeElementDerivedPinchedMap_weak A (framedLimitKProjectiveProbe A X) Y
  dsimp only [framedLimitKProjectiveProbe, complexRelativeElementDerivedPinchedMap] at hd
  rw [← Category.assoc] at hd
  have he := (complexRelativeElementEndpointEquivalence A
    ((framedLimitProbeFunctor A).obj X) Y.val).isQCatEquivalence.isWeakHomotopyEquivalence
  have hc := he.cancel_right hd
  exact (complexRelativeElementHammockPinchedMap_weak A X Y.val).cancel_left hc

end SerrePositivity.EInfinity.PowerOperation
