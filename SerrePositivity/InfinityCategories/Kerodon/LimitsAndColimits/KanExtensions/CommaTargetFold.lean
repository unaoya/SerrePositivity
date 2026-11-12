module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.CompositionSquareCollapse

/-!
概要：合成三角形を始域が固定された矢印の正方形へ移す。
方針：矢印の始点を 0、標的の時間変化を 1→2 へ送る。
規約：第一因子は輸送の時間、第二因子は矢印の区間。
使われ方：comma の固定始域の fiber の辺の持ち上げ。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：矢印の始点を固定する正方形から三角形への単調写像。
方針：矢印の零端は 0、一端は時間に応じ 1,2 とする。
規約：座標は輸送時間、矢印の順。
使われ方：合成三角形からの図式の引き戻し。 -/
def kanCommaTargetFoldOrder : Fin 2 × Fin 2 →o Fin 3 where
  toFun p := if p.2 = 0 then 0 else if p.1 = 0 then 1 else 2
  monotone' := by decide

/-- 概要：始点を固定し標的を輸送する合成正方形。
方針：頂点の単調写像を標準単体の射へ移す。
規約：両因子は標準区間。
使われ方：図式の辺の合成による comma の辺。 -/
def kanCommaTargetFold : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[2] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap kanCommaTargetFoldOrder

/-- 概要：輸送の零端は元の矢印。
方針：標準一単体で有限計算する。
規約：時間は第一因子。
使われ方：指定した始点の comma の頂点の回収。 -/
lemma kanCommaTargetFold_start : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫
    kanCommaTargetFold = stdSimplex.δ (2 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：矢印の始域は最初の頂点に定値。
方針：標準一単体で有限計算する。
規約：矢印は第二因子。
使われ方：固定始域の条件。 -/
lemma kanCommaTargetFold_source : (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
    kanCommaTargetFold = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 3)) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：矢印の標的の変化は三角形の後辺。
方針：標準一単体で有限計算する。
規約：射の厳密な等式。
使われ方：指定された標的の辺の回収。 -/
lemma kanCommaTargetFold_target : (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
    kanCommaTargetFold = stdSimplex.δ (0 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
