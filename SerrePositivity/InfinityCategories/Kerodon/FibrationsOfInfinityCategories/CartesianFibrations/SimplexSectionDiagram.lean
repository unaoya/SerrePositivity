module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexDomains
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramEdges
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeSectionInitialRestriction

/-!
概要：任意の底の全単体の切断を一つの coherent な系へ実現する。
方針：標準単体の図式に相対切断の豊穣図式の共同評価を適用する。
規約：始点を保つ射を可逆にするが、元の底への降下は別に証明する。
使われ方：一般の底上の straightening の全次数の組立てへの入力。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：底の全単体の切断は全 left fibrations 上の一つの coherent な関手の系となる。
方針：標準単体の図式を切断の共同評価へ渡す。
規約：単体とその面・退化を個別には選び直さない。
使われ方：元の底へ降ろす前の全次数の共同切断評価。 -/
def transportSimplexSectionInfinity (B : SSet.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)) ⟶
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B)).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionDiagramInfinity (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B)

/-- 概要：全単体の切断の共同評価は指定単体で実際の相対切断空間を返す。
方針：一般の相対切断図式の頂点公式を標準単体に適用する。
規約：指定単体は Yoneda の実際の射で表す。
使われ方：全次数の系と各単体上の切断の接続。 -/
lemma transportSimplexSectionInfinity_vertex {B : SSet.{u}} {n : SimplexCategory}
    (σ : B.obj (Opposite.op n)) :
    (transportSimplexSectionInfinity B).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex σ))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation (Over.mk (SSet.yonedaEquiv.symm σ)))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionDiagramInfinity_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B) _

/-- 概要：単体圏上の共同評価は任意の添字図式への制限と厳密に可換。
方針：相対切断の図式の制限公式をそのまま使う。
規約：面と退化の高次の整合性を同じ射で保持する。
使われ方：元の底の全単体を同時に比較する。 -/
lemma transportSimplexSectionInfinity_reindex {B : SSet.{u}} {J : Type u} [Category.{u} J]
    (k : J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) :
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫ transportSimplexSectionInfinity B =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionDiagramInfinity (k.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionDiagramInfinity_reindex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B) k

/-- 概要：単体圏の射が最初の頂点を保つという条件。
方針：実際の標準単体の射と最初の頂点包含の可換性で定義する。
規約：非単射な退化作用素も許す。
使われ方：共同切断評価で反転する射を明示する。 -/
def TransportSimplexPreservesFirst {B : SSet.{u}} {i j : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B}
    (f : i ⟶ j) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex j.objDown.obj.unop.len ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B).map f.op).left =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex i.objDown.obj.unop.len

/-- 概要：最初の頂点を保つ単体作用素は指定した反転条件を満たす。
方針：標準単体の射と最初の頂点の合成を各次数で計算する。
規約：単体作用素は単射でなくてもよい。
使われ方：面と退化の具体的な制限を共同評価で反転する。 -/
lemma transportSimplexRestriction_preservesFirst {B : SSet.{u}} {m n : SimplexCategory}
    (α : m ⟶ n) (σ : B.obj (Opposite.op n)) (hα : α.toOrderHom 0 = 0) :
    TransportSimplexPreservesFirst (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction α σ) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex m.len ≫ stdSimplex.map α = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n.len
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro x
  apply stdSimplex.ext
  intro k
  change α.toOrderHom 0 = 0
  exact hα

/-- 概要：始点を保つ単体圏の射の像は全対象の関手空間で可逆な辺。
方針：各対象の始点を保つ切断制限の同値性を大域的な辺の可逆性へ反映する。
規約：像は共同評価の実際の辺。
使われ方：単体圏上の共同評価を元の底へ降ろすための反転条件。 -/
lemma transportSimplexSectionInfinity_isInvertible_of_preservesFirst
    {B : SSet.{u}} {i j : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B} (f : i ⟶ j)
    (hf : TransportSimplexPreservesFirst f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramIndexEdge f).map
      (transportSimplexSectionInfinity B)).toTruncated := by
  let D := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B)
  apply D.realization_edge_isInvertible f
  intro p
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p.val.hom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B).map f.op))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeFunctorOverPre_isQCatEquivalence_of_firstVertex p.val.hom _ hf

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
