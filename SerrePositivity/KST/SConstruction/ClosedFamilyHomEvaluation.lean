module
public import SerrePositivity.KST.SConstruction.QuasicategoryEnrichedActionLaws

/-! # 閉 Hom の全族から通常射の作用を回収する
概要：固定入力の curry 表示から、同じ全族作用の通常射での値を取り出す。
方針：元の等式を一度だけ uncurry して右単位子の式を得る。
規約：具体的な図式値を展開しない。使われ方：一次方向実現の元の dg 射の回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet

/-- 固定入力の curry 表示は、元の作用を同じ通常射として回収する。 -/
lemma closedFamily_hom_action {X Y P : SSet.{u}} (p : 𝟙_ SSet.{u} ⟶ P)
    (a : P ⟶ (ihom X).obj Y) (f : X ⟶ Y) (h : p ≫ a = curry' f) :
    (X ◁ p) ≫ uncurry a = (ρ_ X).hom ≫ f := by
  have ht := congrArg (uncurry (C := SSet.{u})) h
  rw [uncurry_natural_left, curry', uncurry_curry] at ht
  exact ht

end SerrePositivity.KST.SConstruction
