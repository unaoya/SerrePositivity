module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeVertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.OppositeKanHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ComparisonFiberFunctor
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanWhiteheadComparison

/-!
概要：Kan 複体間の任意の射の導来 fiber と単体集合の反転の実際の同値。
方針：元の path 置換の切断を反転し、反転した fibration の strict fiber と導来 fiber を比較する。
規約：元の射に fibration 性を要求しない。fiber と底の点の反転を明示する。
使われ方：HTT 4.2.4.1、反転係数の比較から元の q_x の導来 fiber へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：Kan 複体間の射の可逆 path 置換への定値 path の切断はホモトピー同値。
方針：元の始域への射影の自明 Kan fibration 性と切断の左逆の式に二対三則を使う。
規約：元の射の fibration 性は不要。
使われ方：反転した元の射と反転した path 置換の導来 fiber の比較。 -/
lemma kanEquivalencePathReplacementSection_homotopyEquivalence {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection p) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection p)
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection p) := by
    apply hp.cancel_right
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_projection]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence
  exact hs.isSimplicialHomotopyEquivalence

/-- 概要：反転した元の射から反転した path 置換への切断が誘導する実際の導来 fiber の射。
方針：切断の厳密な分解を反転し、同じ底上の源の比較を使う。
規約：底の点は元の b の反転に固定する。
使われ方：反転係数の導来 fiber の共通の fibration 模型への移送。 -/
def oppositeComparisonFiberSectionMap {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p))
        (SSet.opObjEquiv.symm b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberMap (SSet.opFunctor.map p)
    (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p))
    (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection p))
    (by rw [← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_map])
    (SSet.opObjEquiv.symm b)

/-- 概要：反転した切断による fiber 射は元の源成分の反転と厳密に可換。
方針：同じ底上の導来 fiber の射の源成分の式を使う。
規約：反転した path 置換への切断をそのまま使う。
使われ方：元の比較射のデータとの整合性の確認。 -/
lemma oppositeComparisonFiberSectionMap_source {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    oppositeComparisonFiberSectionMap p b ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberSource (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p))
          (SSet.opObjEquiv.symm b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberSource (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b) ≫
        SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection p) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberMap_source _ _ _ _ _

/-- 概要：反転した切断が誘導する実際の導来 fiber の射はホモトピー同値。
方針：元の切断のホモトピー同値性を反転し、同じ底上の源の比較へ渡す。
規約：両端の Kan 性だけを要求し、元の射の fibration 性は不要。
使われ方：反転した元の比較と反転した fibration の導来 fiber の同定。 -/
lemma oppositeComparisonFiberSectionMap_homotopyEquivalence {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (oppositeComparisonFiberSectionMap p b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberMap_homotopyEquivalence _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.oppositeKanHomotopyEquivalence
      (kanEquivalencePathReplacementSection_homotopyEquivalence p)) (SSet.opObjEquiv.symm b)

/-- 概要：任意の Kan 複体間の比較射の導来 fiber の反転と反転した比較射の導来 fiber は同値。
方針：反転した path 置換の strict fiber を介し、strict・導来比較と切断の比較を合成する。
規約：元の射の fibration 性や fiber の非空性・可縮性は要求しない。
使われ方：HTT 4.2.4.1、反転係数の q′ と元の q_x の導来 fiber の直接比較。 -/
def oppositeComparisonFiberEquivalence {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber p b).op
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.oppositeVertexFiberIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p) b)).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.fibrationStrictDerivedFiberEquivalence
      (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p)) (SSet.opObjEquiv.symm b)).trans
        (oppositeComparisonFiberSectionMap_homotopyEquivalence p b).isQCatEquivalence.choose.symm)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
