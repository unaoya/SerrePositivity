module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramValueKanComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningFunctorIso
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SectionsFiberwiseEquivalence

/-!
概要：同じ値の係数比較を、底を保つunstraighteningと切断の同値へ移す。
方針：全関手同型を任意の指定底へ制限し、底上の比較と相対後合成を使う。
規約：比較するのはcoherent係数の切断であり、通常endとの一致は別に必要。
使われ方：HTT 4.2.4.4のRR02における係数比較の移送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
  (X Y : StrictComplexDiagram A d) {B : SSet.{u}} [Quasicategory B]
  (a : B ⟶ nerve (AsSmall.{u} ((strictDiagramIndex d)ᵒᵖ × strictDiagramIndex d)))

/-- 同じ評価係数を、指定した底の射に沿って制限する。 -/
def strictDiagramEvaluatedValueCoefficient :
    (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map a ≫
    kanDiagramCoherentNerve (strictDiagramEvaluatedValueKan A d X Y)

/-- 同じ標準係数を、同じ底の射に沿って制限する。 -/
def strictDiagramStandardValueCoefficient :
    (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map a ≫
    kanDiagramCoherentNerve (strictDiagramStandardValueKan A d X Y)

/-- 制限後も同じ全関手同型で係数を比較する。 -/
def strictDiagramValueCoefficientIso :
    FunctorIso (strictDiagramEvaluatedValueCoefficient A d X Y a)
      (strictDiagramStandardValueCoefficient A d X Y a) :=
  FunctorIso.precomp (strictDiagramValueKanIso A d X Y)
    ((SSet.uliftFunctor.{u + 1, u}).map a)

/-- 指定の係数同型から選んだ、底上の小さい全空間の比較。 -/
def strictDiagramValueTotalComparison :
    smallLeftUnstraightening (strictDiagramEvaluatedValueCoefficient A d X Y a) ⟶
      smallLeftUnstraightening (strictDiagramStandardValueCoefficient A d X Y a) :=
  smallLeftUnstraighteningComparisonOfFunctorIso (strictDiagramValueCoefficientIso A d X Y a)

/-- 同じ全空間の射が、底を厳密に保つ等式。 -/
lemma strictDiagramValueTotalComparison_projection :
    strictDiagramValueTotalComparison A d X Y a ≫
      smallLeftUnstraighteningProjection (strictDiagramStandardValueCoefficient A d X Y a) =
    smallLeftUnstraighteningProjection (strictDiagramEvaluatedValueCoefficient A d X Y a) :=
  smallLeftUnstraighteningComparisonOfFunctorIso_projection (strictDiagramValueCoefficientIso A d X Y a)

/-- 底を保つ同じ射の後合成による、coherent係数の切断の比較。 -/
def strictDiagramValueSectionsComparison :
    simplicialSections (smallLeftUnstraighteningProjection
      (strictDiagramEvaluatedValueCoefficient A d X Y a)) ⟶
    simplicialSections (smallLeftUnstraighteningProjection
      (strictDiagramStandardValueCoefficient A d X Y a)) :=
  simplicialSectionsMap (strictDiagramValueTotalComparison A d X Y a)
    (strictDiagramValueTotalComparison_projection A d X Y a)

/-- 同じ切断比較は、底上の逆射による相対後合成の同値からホモトピー同値となる。 -/
lemma strictDiagramValueSectionsComparison_equivalence :
    IsSimplicialHomotopyEquivalence (strictDiagramValueSectionsComparison A d X Y a) := by
  let p := smallLeftUnstraighteningProjection (strictDiagramEvaluatedValueCoefficient A d X Y a)
  let q := smallLeftUnstraighteningProjection (strictDiagramStandardValueCoefficient A d X Y a)
  haveI := simplicialSections_kanComplex p
  haveI := simplicialSections_kanComplex q
  have he := relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence
    p q (strictDiagramValueTotalComparison A d X Y a)
    (strictDiagramValueTotalComparison_projection A d X Y a)
    (smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence
      (strictDiagramValueCoefficientIso A d X Y a)) (𝟙 B)
  have hp := (qCatEquivalenceOfIso (simplicialSectionsRelativeIso p)).isQCatEquivalence
  have hq := (qCatEquivalenceOfIso (simplicialSectionsRelativeIso q)).isQCatEquivalence
  apply IsQCatEquivalence.isSimplicialHomotopyEquivalence
  apply hq.cancel_right
  change IsQCatEquivalence
    (simplicialSectionsMap (strictDiagramValueTotalComparison A d X Y a)
      (strictDiagramValueTotalComparison_projection A d X Y a) ≫
        (simplicialSectionsRelativeIso q).hom)
  rw [simplicialSectionsRelativeIso_naturality]
  exact hp.comp he

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
