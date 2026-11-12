module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.StdSimplexProductMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathLifting

/-!
概要：標準区間の二時刻の最小値を単体集合の射として構成する。
方針：二点鎖の直積の単調な最小値写像を標準単体へ移す。
規約：全ての端点の式を厳密に保持する。
使われ方：錐の正方形の下辺から対角への両端固定変形。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 二点鎖の直積の最小値は単調。 -/
def intervalMinimumOrder : Fin 2 × Fin 2 →o Fin 2 where
  toFun a := min a.1 a.2
  monotone' {_a _b} h := min_le_min h.1 h.2

/-- 標準区間の二時刻の最小値。 -/
def intervalMinimum : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap intervalMinimumOrder

/-- 最初の時刻零では全時刻で零。 -/
lemma intervalMinimum_first_zero : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ intervalMinimum =
    SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 最初の時刻一では第二時刻を回収する。 -/
lemma intervalMinimum_first_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ intervalMinimum = 𝟙 Δ[1] := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 第二時刻零では全時刻で零。 -/
lemma intervalMinimum_second_zero : (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
    intervalMinimum = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 第二時刻一では最初の時刻を回収する。 -/
lemma intervalMinimum_second_one :
    (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫ intervalMinimum = 𝟙 Δ[1] := by
  apply SSet.yonedaEquiv.injective
  decide

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
