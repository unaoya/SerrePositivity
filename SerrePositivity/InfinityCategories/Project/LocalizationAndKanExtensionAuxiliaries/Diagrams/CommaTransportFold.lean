module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.CompositionSquareCollapse

/-!
概要：合成三角形を標的が固定された矢印の正方形へ移す畳み込み。
方針：二つの右頂点を三角形の最後の頂点へ送る。
規約：第一因子は矢印の区間、第二因子は始域の輸送の時間。
使われ方：B1 の comma の cartesian lift の実際の図式。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams

/-- 概要：正方形の右辺を一点へ潰す単調写像。
方針：左辺を 0,1、右辺を 2 へ送る。
規約：二つの座標は矢印と輸送時間。
使われ方：標的固定の合成正方形の構成。 -/
def commaTransportFoldOrder : Fin 2 × Fin 2 →o Fin 3 where
  toFun p := if p.1 = 0 then if p.2 = 0 then 0 else 1 else 2
  monotone' := by decide

/-- 概要：合成三角形を標的固定の正方形へ引き戻す射。
方針：頂点の単調写像を標準単体の直積の射にする。
規約：矢印区間が第一因子。
使われ方：comma の標的固定の輸送。 -/
def commaTransportFold : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[2] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap commaTransportFoldOrder

/-- 概要：輸送の終点の矢印は三角形の後辺。
方針：一次単体で有限計算する。
規約：射の厳密な等式。
使われ方：指定した元の comma 頂点の回収。 -/
lemma commaTransportFold_end : (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
    commaTransportFold = stdSimplex.δ (0 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：矢印の始域の時間変化は三角形の前辺。
方針：一次単体で有限計算する。
規約：射の厳密な等式。
使われ方：指定した始域の辺の回収。 -/
lemma commaTransportFold_source : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫
    commaTransportFold = stdSimplex.δ (2 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：矢印の標的は最後の頂点に定値。
方針：一次単体で有限計算する。
規約：射の厳密な等式。
使われ方：標的の退化辺の認識。 -/
lemma commaTransportFold_target : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫
    commaTransportFold = SSet.const (stdSimplex.obj₀Equiv.symm (2 : Fin 3)) := by
  apply SSet.yonedaEquiv.injective
  decide

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams
