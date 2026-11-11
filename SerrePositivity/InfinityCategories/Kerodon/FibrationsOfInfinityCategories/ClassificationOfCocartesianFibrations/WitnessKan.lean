module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessEdges
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise

/-!
概要：空間値 transport witnesses は Kan 複体。
方針：表現の辺を底の各 fiber で比較し、全辺の可逆性から Kan 性を得る。
規約：非空性と可縮性を仮定しない。基底の quasicategory 性も不要。
使われ方：Kerodon Lemma 5.6.8.7（Tag 02SG）、表現空間の制限の全ホーン持ち上げ。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：同じ left fibration の二つの表現を結ぶ四角形の辺は可逆。
方針：分類図式の辺を対象ごとの可逆性で判定し、left fibration で反映する。
規約：元の底 B は任意の単体集合。
使われ方：Kerodon §5.6.8（Tag 02S9）、transport witnesses の辺の可逆性。 -/
lemma transportSquareEdge_isInvertible {E B : SSet.{u + 1}} {p : E ⟶ B}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {R S : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p}
    (e : SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex R.toSquare) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S.toSquare)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessDiagramEdge e) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessDiagramEdge e).toTruncated).mpr
    intro b
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (show (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgeAt (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessDiagramEdge e) b).edge =
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessDiagramEdge e).toTruncated.map
          ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b))).edge from rfl)).mp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessDiagramEdge_at_isInvertible e b)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_reflects_invertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p) e.toTruncated
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (show (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessDiagramEdge e).edge =
      (e.toTruncated.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p))).edge from rfl)).mp hd

/-- 概要：transport witnesses の全ての辺は可逆。
方針：両端の表現を頂点対応で回収し、全部分複体の包含の充満忠実性を使う。
規約：辺自体に可逆性の条件を追加しない。
使われ方：Kerodon Lemma 5.6.8.7（Tag 02SG）、選択空間の亜群性。 -/
lemma transportWitnessEdge_isInvertible {E B : SSet.{u + 1}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p) _⦋0⦌} (e : SSet.Edge x y) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  obtain ⟨R, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex_surjective p x
  obtain ⟨S, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex_surjective p y
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsTransportWitnessVertex p)).reflects_isInvertibleEdge e.toTruncated
  exact transportSquareEdge_isInvertible (e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι p))

/-- 概要：任意の left fibration の空間値 transport witnesses は Kan 複体。
方針：全てのホモトピー圏の射を辺で表し、全辺の可逆性から Kan 性を得る。
規約：表現の存在や小ささを仮定せず、空の選択空間も許す。
使われ方：Kerodon Lemma 5.6.8.7（Tag 02SG）、相対表現の延長のホーン充填の入力。 -/
instance transportWitnessSpace_kanComplex {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p) := by
  have hg : IsGroupoid (hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p)) := by
    constructor
    intro a b f
    obtain ⟨a, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨b, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective b
    obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p) a b f
    exact transportWitnessEdge_isInvertible p (SSet.Edge.ofTruncated e)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.kanComplex_of_isGroupoid _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
