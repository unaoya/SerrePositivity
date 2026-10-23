module

public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldEnrichedSpan
public import SerrePositivity.InfinityCategories.F1.Diagrams.RelativeSectionDiagram
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationCoherentEvaluation

/-!
概要：自然な復元 span を全 left fibrations からの相対 Hom のテストで比較する。
方針：各脚の前合成同値性を豊穣自然な前合成比較の共同実現に適用する。
規約：固定した始域に対し、標的の全対象と全高次を同時に比較する。
使われ方：全空間側の span の逆を共同の比較として実現するための入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 底上の自然な比較の前合成同値な成分は、全標的への相対 Hom の関手同型を与える。 -/
def SimplicialOverComparison.testIso {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C] {B : SSet.{u}} [Quasicategory B]
    {F G : EnrichedFunctor SSet.{u} C (SimplicialOverObject B)}
    (η : SimplicialOverComparison F G) (X : C)
    (h : IsPrecompositionEquivalence (η.val X).left) :
    FunctorIso (leftFibrationCoherentEvaluation (G.obj X).val)
      (leftFibrationCoherentEvaluation (F.obj X).val) :=
  kanEnrichedComparisonIso (relativeFunctorOverPreComparison (η.val X))
    (fun q ↦ relativeFunctorOverPre_isQCatEquivalence q.val.hom (η.val X) h)

/-- universal scaffold に沿う前合成は、全標的の coherent な相対 Hom 図式の同型。 -/
def universalScaffoldTestIso (C : Type u) [Category.{u} C]
    (p : LeftFibrationObject (nerve C)) :
    FunctorIso (leftFibrationCoherentEvaluation p.val)
      (leftFibrationCoherentEvaluation ((strictTransportReplacementOverEnriched C).obj p).val) :=
  (universalScaffoldOverComparison C).testIso p
    (universalScaffoldOverComparison_isPrecompositionEquivalence C p)

/-- taut scaffold に沿う前合成も、同じ全標的の coherent な相対 Hom 図式の同型。 -/
def tautScaffoldTestIso (C : Type u) [Category.{u} C]
    (p : LeftFibrationObject (nerve C)) :
    FunctorIso
      (leftFibrationCoherentEvaluation ((strictTransportWeightedOverEnriched C).obj p).val)
      (leftFibrationCoherentEvaluation ((strictTransportReplacementOverEnriched C).obj p).val) :=
  (tautScaffoldOverComparison C).testIso p
    (tautScaffoldOverComparison_isPrecompositionEquivalence C p)

/-- 同じ自然な span により、元と復元後から全標的への coherent な相対 Hom を比較する。 -/
def leftStrictTransportReconstructionTestIso (C : Type u) [Category.{u} C]
    (p : LeftFibrationObject (nerve C)) :
    FunctorIso (leftFibrationCoherentEvaluation p.val)
      (leftFibrationCoherentEvaluation ((strictTransportWeightedOverEnriched C).obj p).val) :=
  universalScaffoldTestIso C p ≪≫ (tautScaffoldTestIso C p).symm

end SerrePositivity.InfinityCategories
