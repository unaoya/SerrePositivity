module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightSpaceValueComparison
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.EquivalenceInverseSquare
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CovariantRepresentableValueNaturality
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightUniverseValueNaturality
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightSectionsLimitFactorization
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SmallUnstraighteningValueTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SpaceEdgeTransportValue
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FamilyEquivalenceReflection

/-!
概要：G8 の元の宇宙変更の値比較と、同じ指定辺の値の作用の全族自然性。
方針：普遍的な pointed space の fiber と同じ復元射の値比較を経由する。
規約：正本の spaceUniverseValueEquivalence の選択を保持する。
使われ方：G8 の四角形②の宇宙変更の因子。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open IsomorphismsAndIsofibrations Equivalence MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors

namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：元のテンソル随伴の値から右写像空間への後段の同じ比較。
方針：宇宙変更、表現の指定成分の逆、共変表現可能値の比較を合成する。
規約：全て正本と同じ選択。使われ方：G8 の後段の自然性。 -/
def spaceTensorHomValueTail {E : SSet.{u + 1}} [Quasicategory E]
    {M : E _⦋0⦌} (t : SpaceTensorData M) (c : E _⦋0⦌) :
    QCatEquivalence
      ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject (t.hom.app _ c)).obj)
      (Basic.pinchedHom M c) :=
  (SetWeight.spaceUniverseValueEquivalence (t.hom.app _ c)).trans
    ((SetWeight.spaceValueEquivalence (t.represents.app (ULift.up c))).symm.trans
      (covariantRepresentableValueEquivalence M c))

/-- 概要：正本の同じ Hom 値比較は、指定辺の値の作用と標準後合成を全族で結ぶ。
方針：宇宙変更の自然性、表現の自然同型の正方形と同じ逆、表現可能値の自然性を合成する。
規約：点ごとの比較ではなく写像全体の同型。使われ方：G8 の後段の接続。 -/
def spaceTensorHomValueTail_edgeIso {E : SSet.{u + 1}} [Quasicategory E]
    {M : E _⦋0⦌} (t : SpaceTensorData M) {a b : E _⦋0⦌} (e : E.Edge a b) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (spaceInfinityEdgeValue (e.map t.hom)) ≫
        (spaceTensorHomValueTail t b).hom)
      ((spaceTensorHomValueTail t a).hom ≫
        postcompose M (SSet.Truncated.HomotopyCategory.homMk e)) := by
  let e' : ((SSet.uliftFunctor.{u + 2, u + 1}).obj E).Edge (ULift.up a) (ULift.up b) :=
    SSet.Edge.ofTruncated (uliftTruncatedEdge.{u + 1, u + 2} e)
  let s := t.represents.app (ULift.up a)
  let r := t.represents.app (ULift.up b)
  let f := e'.map (covariantRepresentableInfinity M)
  let g := e'.map ((SSet.uliftFunctor.{u + 2, u + 1}).map t.hom ≫ spaceUniverseDiagram)
  have h : SSet.Truncated.HomotopyCategory.homMk f.toTruncated ≫ r.hom =
      s.hom ≫ SSet.Truncated.HomotopyCategory.homMk g.toTruncated :=
    t.represents.toNatIso.hom.naturality
      (SSet.Truncated.HomotopyCategory.homMk e'.toTruncated)
  have hi := functorIsoInverseSquare
    (SetWeight.spaceValueEquivalence s) (SetWeight.spaceValueEquivalence r)
    (spaceInfinityEdgeValue f) (spaceInfinityEdgeValue g)
    (setWeightSpaceValueSquareIso s r f g h)
  have hg : g = ((SSet.Edge.ofTruncated
      (uliftTruncatedEdge.{u + 1, u + 2} (e.map t.hom))).map spaceUniverseDiagram) := by
    apply SSet.Edge.ext
    rfl
  rw [hg] at hi
  have h₀ := FunctorIso.postcomp (setWeightUniverseValue_edgeIso (e.map t.hom))
    ((SetWeight.spaceValueEquivalence r).inv ≫
      (covariantRepresentableValueEquivalence M b).hom)
  have h₁ := FunctorIso.precomp
    (FunctorIso.postcomp hi (covariantRepresentableValueEquivalence M b).hom)
    (SetWeight.spaceUniverseValueEquivalence (t.hom.app _ a)).hom
  have h₂ := FunctorIso.precomp (covariantRepresentableValue_postcomposeIso M e)
    ((SetWeight.spaceUniverseValueEquivalence (t.hom.app _ a)).hom ≫
      (SetWeight.spaceValueEquivalence s).inv)
  simp only [spaceTensorHomValueTail, QCatEquivalence.trans, QCatEquivalence.symm,
    Category.assoc]
  simp only [Category.assoc] at h₀ h₁ h₂
  exact h₀ ≪≫ h₁ ≪≫ h₂

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
