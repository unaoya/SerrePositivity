module
public import SerrePositivity.KST.SConstruction.ThreeSquarePasting
public import SerrePositivity.KST.SConstruction.FamilySquareClockSwap
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-! # 内部 Hom の全正方形を元の二次元円柱へ戻す
概要：パラメータ付き写像空間の正方形を、元の三変数の実写像に戻す。
方針：uncurry と同じ三座標の結合子を使い、四面を全時刻で回収する。
規約：入力正方形の全体を使い、辺やホモトピーを選び直さない。
使われ方：端点固定の辺の比較を、元の全パラメータの実比較円柱へ変換する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {U E : SSet.{u}} (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom U).obj E)

/-- 同じ全正方形を、元のパラメータと独立な二時刻の実写像へ戻す。 -/
def mappingSquareUncurry : (U ⊗ (Δ[1] : SSet.{u})) ⊗ Δ[1] ⟶ E :=
  (α_ U Δ[1] Δ[1]).hom ≫ uncurry Q

/-- 比較時刻零は、同じ元の零辺の実円柱。 -/
lemma mappingSquareUncurry_zero :
    SSet.ι₀ ≫ mappingSquareUncurry Q = uncurry (SSet.ι₀ ≫ Q) := by
  have hi : SSet.ι₀ ≫ (α_ U (Δ[1] : SSet.{u}) Δ[1]).hom =
      U ◁ (SSet.ι₀ (X := (Δ[1] : SSet.{u}))) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  rw [mappingSquareUncurry, ← Category.assoc, hi, ← uncurry_natural_left]

/-- 比較時刻一も、同じ元の一辺の実円柱。 -/
lemma mappingSquareUncurry_one :
    SSet.ι₁ ≫ mappingSquareUncurry Q = uncurry (SSet.ι₁ ≫ Q) := by
  have hi : SSet.ι₁ ≫ (α_ U (Δ[1] : SSet.{u}) Δ[1]).hom =
      U ◁ (SSet.ι₁ (X := (Δ[1] : SSet.{u}))) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  rw [mappingSquareUncurry, ← Category.assoc, hi, ← uncurry_natural_left]

/-- 元の始点の時間方向は、同じ正方形の第一座標零の実制限。 -/
lemma mappingSquareUncurry_source :
    (SSet.ι₀ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ mappingSquareUncurry Q =
      uncurry (pastingSquareVertical 0 ≫ Q) := by
  have hi : (SSet.ι₀ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ (α_ U Δ[1] Δ[1]).hom =
      U ◁ pastingSquareVertical 0 := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  rw [mappingSquareUncurry, ← Category.assoc, hi, ← uncurry_natural_left]

/-- 元の終点の時間方向も、同じ正方形の第一座標一の実制限。 -/
lemma mappingSquareUncurry_target :
    (SSet.ι₁ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ mappingSquareUncurry Q =
      uncurry (pastingSquareVertical 1 ≫ Q) := by
  have hi : (SSet.ι₁ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ (α_ U Δ[1] Δ[1]).hom =
      U ◁ pastingSquareVertical 1 := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  rw [mappingSquareUncurry, ← Category.assoc, hi, ← uncurry_natural_left]

end SerrePositivity.KST.SConstruction
