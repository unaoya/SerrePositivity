module

public import SerrePositivity.InfinityCategories.F1.ScaffoldJointTestComparison
public import SerrePositivity.InfinityCategories.F1.SimplicialOverTestFamily

/-!
概要：復元 span の逆を全始域の Hom 関手の族の一つの同型として表す。
方針：共同テスト同型を実際の関手圏に curry し、二つの脚を同じ族で合成する。
規約：同型は全始域・全標的・全高次で自然。全空間側の比較とはまだ区別する。
使われ方：表現可能な族から元の全空間側へ比較を回収するための入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- universal scaffold の前合成は、全始域の Hom 関手の族の一つの同型。 -/
def universalScaffoldTestFamilyIso (C : Type u) [Category.{u} C] :
    FunctorIso
      (simplicialOverTestFamily (leftFibrationOverEnriched (nerve C)))
      (simplicialOverTestFamily (strictTransportReplacementOverEnriched C)) :=
  (universalScaffoldOverComparison C).testFamilyIso
    (universalScaffoldOverComparison_isPrecompositionEquivalence C)

/-- taut scaffold も同じ始域の Hom 関手の族の同型を与える。 -/
def tautScaffoldTestFamilyIso (C : Type u) [Category.{u} C] :
    FunctorIso
      (simplicialOverTestFamily (strictTransportWeightedOverEnriched C))
      (simplicialOverTestFamily (strictTransportReplacementOverEnriched C)) :=
  (tautScaffoldOverComparison C).testFamilyIso
    (tautScaffoldOverComparison_isPrecompositionEquivalence C)

/-- 元と復元後の全始域の Hom 関手の族は、一つの関手同型を持つ。 -/
def leftStrictTransportReconstructionTestFamilyIso (C : Type u) [Category.{u} C] :
    FunctorIso
      (simplicialOverTestFamily (leftFibrationOverEnriched (nerve C)))
      (simplicialOverTestFamily (strictTransportWeightedOverEnriched C)) :=
  universalScaffoldTestFamilyIso C ≪≫ (tautScaffoldTestFamilyIso C).symm

/-- strict transport を weighted nerve へ戻す自己豊穣関手。 -/
def strictTransportWeightedEnriched (C : Type u) [Category.{u} C] :
    EnrichedFunctor SSet.{u} (LeftFibrationObject (nerve C))
      (LeftFibrationObject (nerve C)) :=
  ((leftStrictTransportEnriched (C := C)).comp SSet strictTransportKanDiagramEnriched).comp
    SSet (weightedNerveKanEnriched C)

/-- 同じ自己作用を全底上対象の圏へ含めると、既存の復元 span の終域になる。 -/
lemma strictTransportWeightedEnriched_over (C : Type u) [Category.{u} C] :
    (strictTransportWeightedEnriched C).comp SSet (leftFibrationOverEnriched (nerve C)) =
      strictTransportWeightedOverEnriched C := rfl

/-- 標準 Hom の族は、実際の復元自己関手による前合成と一つの関手同型を持つ。 -/
def leftStrictTransportReconstructionHomFamilyIso (C : Type u) [Category.{u} C] :
    FunctorIso (leftFibrationHomTestFamily (nerve C))
      (coherentNerveMap (simplicialEnrichedOpposite (strictTransportWeightedEnriched C)) ≫
        leftFibrationHomTestFamily (nerve C)) := by
  have e := leftStrictTransportReconstructionTestFamilyIso C
  change FunctorIso (leftFibrationHomTestFamily (nerve C))
    (simplicialOverTestFamily ((strictTransportWeightedEnriched C).comp SSet
      (leftFibrationOverEnriched (nerve C)))) at e
  rw [simplicialOverTestFamily_leftFibration] at e
  exact e

end SerrePositivity.InfinityCategories
