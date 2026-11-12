module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.StdSimplexProductMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathLifting

/-!
概要：標準区間の二つの時刻の最大値を単体集合の射として構成する。
方針：二点鎖の直積の最大値の単調写像を標準単体の直積の射へ移す。
規約：座標の順序は最初の時間、二番目の時間。
使われ方：comma の矢印をその標的の恒等矢印へ変形する。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams

/-- 概要：二点鎖の直積から二点鎖への最大値の単調写像。
方針：最大値の両変数の単調性。
規約：Fin 2 の順序を使う。
使われ方：区間の二つの時間を一つに畳む。 -/
def intervalMaximumOrder : Fin 2 × Fin 2 →o Fin 2 where
  toFun a := max a.1 a.2
  monotone' {_a _b} h := max_le_max h.1 h.2

/-- 概要：区間の二つの時間の最大値。
方針：単調写像を標準単体の直積の射へ移す。
規約：quasicategory 性は不要。
使われ方：恒等矢印への comma 内の変形。 -/
def intervalMaximum : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap intervalMaximumOrder

/-- 概要：最初の時間を零に固定すると二番目の時間を回収する。
方針：標準一単体上の有限計算。
規約：prismEndpoint は第一因子を固定する。
使われ方：comma 内の変形の始点。 -/
lemma intervalMaximum_first_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ intervalMaximum = 𝟙 Δ[1] := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：最初の時間を一に固定すると一に定値になる。
方針：標準一単体上の有限計算。
規約：一は Fin 2 の最後の頂点。
使われ方：comma 内の変形の終点。 -/
lemma intervalMaximum_first_one : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫
    intervalMaximum = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：二番目の時間を零に固定すると最初の時間を回収する。
方針：標準一単体上の有限計算。
規約：SSet.ι₀ は第二因子を固定する。
使われ方：変形中の矢印の始域。 -/
lemma intervalMaximum_second_zero : (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
    intervalMaximum = 𝟙 Δ[1] := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：二番目の時間を一に固定すると一に定値になる。
方針：標準一単体上の有限計算。
規約：SSet.ι₁ は第二因子を固定する。
使われ方：変形中の矢印の標的。 -/
lemma intervalMaximum_second_one : (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
    intervalMaximum = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  apply SSet.yonedaEquiv.injective
  decide

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams
