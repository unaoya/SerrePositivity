module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RepresentablePresheafValues
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenASliceOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SmallUnstraighteningValueTransport

/-!
概要：表現可能値の元の反転 slice 比較を、同じ coslice 上で輸送に全自然な比較として表示する。
方針：既存の底上の反転同型と元の復元射を合成し、fiber の値の自然性を使う。
規約：反転や unstraightening の比較を作り直さない。
使われ方：G8 の同じ共変表現可能値の比較の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions IsomorphismsAndIsofibrations Equivalence MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Project.FilteredExchange

namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

variable {B : SSet.{u}} [Quasicategory B] (z : B _⦋0⦌)

/-- 概要：反対底の coslice から元の表現可能前層の小さい unstraightening への同じ比較。
方針：既存の底上の反転同型の逆と元の復元射を合成する。
規約：比較の選択を保持。使われ方：指定 fiber 値比較の自然性。 -/
def reversedRepresentableComparison :
    sliceUnder (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm z)) ⟶
      smallLeftUnstraightening (representablePresheafInfinity z) :=
  (cofinalPointSliceOverOpIso z).inv.left ≫
    RepresentableUnstraighteningComparison.representableLeftUnstraighteningComparison z

/-- 概要：同じ復元比較は反対の底を厳密に保つ。
方針：既存の復元射の射影と底上の反転同型の式を使う。
規約：射の厳密な等式。使われ方：fiber 射の定義。 -/
lemma reversedRepresentableComparison_projection :
    reversedRepresentableComparison z ≫
      smallLeftUnstraighteningProjection (representablePresheafInfinity z) =
        sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm z)) := by
  unfold reversedRepresentableComparison
  rw [Category.assoc,
    RepresentableUnstraighteningComparison.representableLeftUnstraighteningComparison_projection]
  exact (cofinalPointSliceOverOpIso z).inv.w

/-- 概要：反対底上の同じ比較は全空間の前合成同値。
方針：底上の同型と既存の復元の前合成同値を合成する。
規約：元の実射について述べる。使われ方：指定 fiber 値の同値性。 -/
lemma reversedRepresentableComparison_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (reversedRepresentableComparison z) :=
  (isPrecompositionEquivalence_of_iso
    ((Over.forget B.op).mapIso (cofinalPointSliceOverOpIso z).symm)).comp
      (RepresentableUnstraighteningComparison.representableLeftUnstraighteningComparison_isPrecompositionEquivalence z)

/-- 概要：反対底の coslice fiber を、元の表現可能前層の値へ送る同じ比較。
方針：同じ復元射の fiber と小さい値の指定比較を合成する。
規約：fiber の表示を保持。使われ方：元の表現可能値比較の全族表示。 -/
def reversedRepresentableValueEquivalence (b : B.op _⦋0⦌) :
    QCatEquivalence
      (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm z))) b)
      (spaceInfinityObject ((representablePresheafInfinity z).app _ (ULift.up b))).obj :=
  (vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence
    (sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm z)))
    (smallLeftUnstraighteningProjection (representablePresheafInfinity z))
    (reversedRepresentableComparison z) (reversedRepresentableComparison_projection z)
    (reversedRepresentableComparison_isPrecompositionEquivalence z) b).choose.trans
      (smallLeftUnstraighteningFiberValueEquivalence (representablePresheafInfinity z) b)

/-- 概要：反対底の coslice の元の値比較は、同じ辺の値の作用に全自然。
方針：同じ復元射の輸送の自然性と小さい値比較の自然性を合成する。
規約：全 fiber の写像を比較。使われ方：G8 の表現可能値の後合成。 -/
def reversedRepresentableValueTransportIso {a b : B.op _⦋0⦌} (e : B.op.Edge a b) :
    FunctorIso
      (edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm z))) e ≫
        (reversedRepresentableValueEquivalence z b).hom)
      ((reversedRepresentableValueEquivalence z a).hom ≫
        spaceInfinityEdgeValue ((SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, u + 1} e)).map
          (representablePresheafInfinity z))) := by
  simpa only [reversedRepresentableValueEquivalence, QCatEquivalence.trans,
    IsQCatEquivalence.choose, Category.assoc] using
      smallUnstraighteningFiberMapValue_transportIso
        (sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm z)))
        (representablePresheafInfinity z) (reversedRepresentableComparison z)
        (reversedRepresentableComparison_projection z) e

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
