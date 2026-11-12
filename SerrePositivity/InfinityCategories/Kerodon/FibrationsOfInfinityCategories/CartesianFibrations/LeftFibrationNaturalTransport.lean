module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorEvaluationComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ScaffoldFirstVertex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-!
概要：底の一本の辺に沿う fiber transport を全 left fibrations 上の実際の変換にする。
方針：切断評価の始点の大域的同型を逆にし終点評価と合成して辺で実現する。
規約：全対象と全高次の相対射を同時に動かす関手空間で構成する。
使われ方：一般の底上の straightening の共同評価の辺の作用。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：辺上の全切断の始点評価は全 left fibrations 上で一つの関手同型。
方針：最初の頂点の left anodyne 性を豊穣評価の比較へ適用する。
規約：始点の fiber は元の射影の実際の fiber。
使われ方：対象ごとに独立な持ち上げを選ばず transport を定義する。 -/
def leftFibrationNaturalTransportSourceIso {B : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation (Over.mk e)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation (e.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonIso e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex_leftAnodyne 1)

/-- 概要：辺に沿う transport は全対象の fiber 評価関手間の実際の辺として選べる。
方針：大域的な始点同型の逆と終点評価の合成を関手空間の辺で表す。
規約：関手空間の高次単体を含む自然性を保持する。
使われ方：共同評価の底の辺方向の作用。 -/
def leftFibrationNaturalTransportEdge {B : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ B) :
    SSet.Edge (X := (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B)).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation (e.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation (e.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _
    ((leftFibrationNaturalTransportSourceIso e).inv ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonEdge e (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))))

/-- 概要：選択した transport の辺は指定した二つの評価の合成を表す。
方針：辺を選んだときの関手空間の代表元の条件を取り出す。
規約：対象ごとの別の transport への置き換えを行わない。
使われ方：全対象の transport と切断による比較の計算。 -/
lemma leftFibrationNaturalTransportEdge_hom {B : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ B) :
    SSet.Truncated.HomotopyCategory.homMk (leftFibrationNaturalTransportEdge e) =
      (leftFibrationNaturalTransportSourceIso e).inv ≫
        SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonEdge e (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ _)

/-- 概要：全切断の始点評価に続けて transport すると終点評価に一致する。
方針：実際の辺の式を代入して始点同型の正逆を相殺する。
規約：全対象の関手空間のホモトピー圏での厳密な等式。
使われ方：共同評価の辺の作用の切断表示による特徴づけ。 -/
lemma leftFibrationNaturalTransportEdge_source {B : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ B) :
    (leftFibrationNaturalTransportSourceIso e).hom ≫
        SSet.Truncated.HomotopyCategory.homMk (leftFibrationNaturalTransportEdge e) =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonEdge e (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  rw [leftFibrationNaturalTransportEdge_hom, Iso.hom_inv_id_assoc]

/-- 概要：全対象の transport の辺を区間と fibration の ∞ 圏の積上の図式にする。
方針：選択した実際の辺の prism 表示を取る。
規約：二つの端点は実際の fiber 評価関手。
使われ方：共同評価を高次の底の単体へ延長するための一単体。 -/
def leftFibrationNaturalTransportPrism {B : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ B) :
    (Δ[1] : SSet.{u + 1}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism (leftFibrationNaturalTransportEdge e)

/-- 概要：全対象の transport の prism の始点は始点の fiber 評価。
方針：辺の prism の始点公式を使う。
規約：単体集合の射の厳密な等式。
使われ方：共同評価の零側の境界条件。 -/
lemma leftFibrationNaturalTransportPrism_zero {B : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B) ≫ leftFibrationNaturalTransportPrism e =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation (e.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism_zero _

/-- 概要：全対象の transport の prism の終点は終点の fiber 評価。
方針：辺の prism の終点公式を使う。
規約：単体集合の射の厳密な等式。
使われ方：共同評価の一側の境界条件。 -/
lemma leftFibrationNaturalTransportPrism_one {B : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B) ≫ leftFibrationNaturalTransportPrism e =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation (e.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism_one _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
