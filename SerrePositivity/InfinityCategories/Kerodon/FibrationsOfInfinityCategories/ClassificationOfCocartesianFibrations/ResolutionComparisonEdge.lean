module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ResolutionComparisonFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorFamilyTranspose
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramConstantParameter
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanInvertible

/-!
概要：空間の恒等関手から解像への実際の coherent な変換。
方針：二点の図式の族を転置し、二点の底の辺をその写像で送る。
規約：各頂点での辺は標準比較そのものであり、逆写像の選択は使わない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、任意の coherent な図式に自然な比較を与える。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：標準比較の二点の添字の零から一への辺。
方針：二点の順序の通常の射の nerve の辺を宇宙持ち上げする。
規約：端点は元の対象の nerve の頂点を持ち上げたもの。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、比較の族から実際の変換を取り出す辺。 -/
def coherentResolutionComparisonIndexEdge :
    SSet.Edge (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} (Fin 2))))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up (0 : Fin 2))))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up (1 : Fin 2)))) :=
  SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, u + 1}
    (nerve.edgeMk (homOfLE
      (show (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) ≤ ULift.up 1 from by decide))).toTruncated)

/-- 概要：空間の恒等関手から解像への coherent な変換の辺。
方針：標準比較の族を転置し、二点の添字の辺を写して端点を正規化する。
規約：変換は関手単体集合の一つの辺として構成する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、一般の coherent な図式へ引き戻せる比較。 -/
noncomputable def coherentResolutionComparisonEdge :
    SSet.Edge (X := (ihom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionInfinityMap.{u}) :=
  (coherentResolutionComparisonIndexEdge.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionComparisonFamily)).ofEq
      (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionComparisonFamily_zero])
      (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionComparisonFamily_one])

/-- 概要：coherent な比較の辺を Kan 複体で評価すると標準比較の coherent な辺になる。
方針：転置の評価公式、定値パラメーターの共同評価、通常の図式の辺の計算を組み合わせる。
規約：端点の表示に依存しない一単体の等式として述べる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、大域的な比較の点ごとの可逆性。 -/
lemma coherentResolutionComparisonEdge_at (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgeAt coherentResolutionComparisonEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex K)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (show K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionKanEnriched.obj K from _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison K.obj)).edge := by
  change ((coherentResolutionComparisonIndexEdge.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionComparisonFamily)).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex K))).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily_edgeAt]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramDiagonalSimplex
    (nerve.edgeMk (homOfLE
      (show (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) ≤ ULift.up 1 from by decide))).edge
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionArrowEnriched).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex K) 1)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramDiagonalSimplex_constant]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_edge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionArrowDiagram K) _

/-- 概要：恒等関手から解像への coherent な比較の辺は可逆。
方針：任意の空間の頂点を Kan 複体で表し、標準比較の同値性を点ごとの可逆性の判定へ適用する。
規約：構成済みの比較の辺そのものについて述べる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、解像への比較の大域的な可逆性。 -/
lemma coherentResolutionComparisonEdge_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge coherentResolutionComparisonEdge.{u} := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt coherentResolutionComparisonEdge.toTruncated).mpr
  intro s
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object s]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgeAt coherentResolutionComparisonEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject s))).toTruncated
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (coherentResolutionComparisonEdge_at (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject s))).mpr
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject s).obj)

/-- 概要：空間の恒等関手と解像の自己写像の間の大域的な関手同型。
方針：構成済みの coherent な辺の可逆性からホモトピー圏の同型を取る。
規約：順方向の射は標準比較の辺の類。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、任意の coherent な空間値図式への自然な置換。 -/
noncomputable def coherentResolutionInfinityComparisonIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (𝟙 _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionInfinityMap.{u} := by
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk
      coherentResolutionComparisonEdge.{u}.toTruncated) := coherentResolutionComparisonEdge_isInvertible
  exact asIso (SSet.Truncated.HomotopyCategory.homMk coherentResolutionComparisonEdge.toTruncated)

/-- 概要：解像の自己写像は空間の coherent nerve の同値。
方針：恒等写像を逆に取り、標準比較の関手同型を両側の逆条件に使う。
規約：順方向は構成した豊穣解像の coherent nerve の写像。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な図式の解像による同値不変性。 -/
noncomputable def coherentResolutionInfinityEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionInfinityMap
  inv := 𝟙 _
  homInvIso := by simpa only [Category.comp_id] using coherentResolutionInfinityComparisonIso.symm
  invHomIso := by simpa only [Category.id_comp] using coherentResolutionInfinityComparisonIso.symm

/-- 概要：任意の coherent な空間値図式はその解像による後合成と関手同型。
方針：空間全体の標準比較の関手同型を図式で前合成する。
規約：底 B は任意の単体集合。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strictification の比較において図式全体を自然に解像する。 -/
noncomputable def coherentResolutionDiagramComparisonIso {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionInfinityMap) := by
  simpa only [Category.comp_id] using coherentResolutionInfinityComparisonIso.precomp F

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
