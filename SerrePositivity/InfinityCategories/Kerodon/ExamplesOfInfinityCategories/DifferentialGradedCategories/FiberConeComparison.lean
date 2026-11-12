module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FiberPullback
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FiberConeVertex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TerminalEdgeIso
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ComplexEdgeEquivalence

/-! # 任意の極限錐から標準 fiber への比較

概要：標準 cospan 上の任意の極限錐から標準 fiber への誘導射はホモトピー同値、したがって擬同型。
方針：標準終対象への slice の比較辺を射影し、極限の一意性、N3、複体ホモトピー圏との比較を使う。
規約：HTT §1.2.13、HA §1.3.1。使われ方：任意の引き戻し四角形の頂点と標準 fiber の比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：標準 cospan の任意の錐から標準 fiber 錐への slice の比較辺を選ぶ。
方針：N7c の標準錐の終対象性から比較辺の存在を使う。
規約：比較元の極限性はこの構成には不要。使われ方：誘導射を錐の間の辺として実現する。 -/
def fiberConeComparisonSliceEdge (g : B ⟶ D) (h : C ⟶ D)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h))) :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))) c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h) :=
  Classical.choice ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone_isLimit g h).nonempty_edge c)

/-- 概要：錐の比較辺を射影すると頂点間の複体 dg nerve の辺になる。
方針：slice 射影の二次切断による辺の像を取る。
規約：HTT §1.2.13。使われ方：実際の複体の比較射を取り出す。 -/
def fiberConeComparisonEdge (g : B ⟶ D) (h : C ⟶ D)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h))) :
    SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A (Complex A))
      c.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h).vertex :=
  (fiberConeComparisonSliceEdge g h c).map ((SSet.truncation 2).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h))))

/-- 概要：標準錐の頂点の唯一の対象は標準 fiber である。
方針：標準錐の頂点の同定を対象で評価する。
規約：HTT §1.2.13。使われ方：比較射の終域を実際の fiber に合わせる。 -/
lemma standardFiberCone_vertex_obj (g : B ⟶ D) (h : C ⟶ D) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h).vertex).obj 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h :=
  congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) 0 => s.obj 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone_vertex g h)

/-- 概要：比較辺の終点を実際の標準 fiber の頂点に同定する。
方針：標準錐の頂点の等式に沿って比較辺の終点を移す。
規約：HTT §1.2.13。使われ方：頂点から標準 fiber への誘導射そのものの辺。 -/
def fiberConeComparisonCanonicalEdge (g : B ⟶ D) (h : C ⟶ D)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h))) :
    SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A (Complex A))
      c.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeTransportTarget (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone_vertex g h) (fiberConeComparisonEdge g h c)

/-- 概要：錐の頂点から標準 fiber への実際の chain map。
方針：終点を標準 fiber に同定した比較辺の閉零射を chain map に直す。
規約：極限性を仮定しない誘導射。使われ方：引き戻しの頂点の擬同型判定。 -/
def fiberConeComparison (g : B ⟶ D) (h : C ⟶ D)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h))) :
    c.vertex.obj 0 ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap (fiberConeComparisonCanonicalEdge g h c)

/-- 概要：比較元も極限錐なら、射影した比較辺の類は nerve のホモトピー圏で同型。
方針：slice の二つの終対象間の指定辺の同型性を、射影が誘導する関手で写す。
規約：HTT §1.2.13 の極限の一意性。使われ方：H⁰ 比較へ渡す同型性。 -/
lemma fiberConeComparisonEdge_isIso (g : B ⟶ D) (h : C ⟶ D)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    IsIso (SSet.Truncated.HomotopyCategory₂.homMk (fiberConeComparisonEdge g h c)) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isIso_homMk_of_terminal hc (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone_isLimit g h)
    (fiberConeComparisonSliceEdge g h c)
  change IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))).map
      (SSet.Truncated.HomotopyCategory₂.homMk (fiberConeComparisonSliceEdge g h c)))
  infer_instance

/-- 概要：標準 fiber そのものを終点とする比較辺のホモトピー類は同型。
方針：射影した比較辺の同型性を、終点の等式に沿う移送で保つ。
規約：HTT §1.2.13。使われ方：実際の誘導射の nerve ホモトピー圏での同型性。 -/
lemma fiberConeComparisonCanonicalEdge_isIso (g : B ⟶ D) (h : C ⟶ D)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    IsIso (SSet.Truncated.HomotopyCategory₂.homMk
      (fiberConeComparisonCanonicalEdge g h c)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isIso_homMk_edgeTransportTarget (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone_vertex g h) _
    (fiberConeComparisonEdge_isIso g h c hc)

/-- 概要：比較辺の閉零射の H⁰ の類は同型。
方針：N3 の toH0 関手が同型を保つことを使う。
規約：HA §1.3.1、Kerodon §2.5.3（Tag 00PK）。使われ方：複体のホモトピー同値への比較。 -/
lemma fiberConeComparisonEdge_H0_isIso (g : B ⟶ D) (h : C ⟶ D)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    IsIso ((toHomotopy A (Complex A)).map
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (fiberConeComparisonCanonicalEdge g h c))) := by
  have := fiberConeComparisonCanonicalEdge_isIso g h c hc
  change IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 A (Complex A)).map
    (SSet.Truncated.HomotopyCategory₂.homMk (fiberConeComparisonCanonicalEdge g h c)))
  infer_instance

/-- 概要：極限錐の頂点から標準 fiber への誘導射はホモトピー同値。
方針：比較辺の同型性を複体のホモトピー同値へ移し、終域の同定である同型射を合成する。
規約：HTT §1.2.13、HA §1.3.1。使われ方：D4 の比較射の擬同型性。 -/
lemma fiberConeComparison_homotopyEquivalence (g : B ⟶ D) (h : C ⟶ D)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} A) (.up ℤ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberConeComparison g h c) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap_homotopyEquivalence _ (fiberConeComparisonCanonicalEdge_isIso g h c hc)

/-- 概要：極限錐の頂点から標準 fiber への誘導射は擬同型。
方針：同じ誘導射を順射に持つホモトピー同値を取り、ホモロジー上の同型性を使う。
規約：任意の可換環と非有界複体。使われ方：引き戻し四角形の fiber による判定の必要性。 -/
lemma fiberConeComparison_quasiIso (g : B ⟶ D) (h : C ⟶ D)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    QuasiIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberConeComparison g h c) := by
  obtain ⟨e, he⟩ := fiberConeComparison_homotopyEquivalence g h c hc
  rw [← he]
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
