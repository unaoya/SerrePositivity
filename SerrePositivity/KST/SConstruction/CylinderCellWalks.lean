module
public import SerrePositivity.KST.SConstruction.FamilyHomotopyChains
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # 全円柱セルの共有面を保つ実際の歩道
概要：円柱セルの全体と、前後の端面が厳密に一致する貼り合わせ順序を保持する。
方針：入口・出口を持つ有限セル歩道として帰納的に表す。
規約：写像先での一致だけでなく、貼り合わせ複体内の共有面の等号を使う。
使われ方：実二次元補正列を、全セルを保持する一つの複体にする。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

/-- 複体内の入口・出口と、同じ共有面に沿って並ぶ全円柱セル。 -/
inductive CylinderCellWalk {U D : SSet.{u}} :
    (U ⟶ D) → (U ⟶ D) → List (U ⊗ (Δ[1] : SSet.{u}) ⟶ D) → Type u
  | nil (i : U ⟶ D) : CylinderCellWalk i i []
  | cons {i j k : U ⟶ D} {cells : List (U ⊗ (Δ[1] : SSet.{u}) ⟶ D)}
      (q : U ⊗ (Δ[1] : SSet.{u}) ⟶ D)
      (h₀ : SSet.ι₀ ≫ q = i) (h₁ : SSet.ι₁ ≫ q = j)
      (tail : CylinderCellWalk j k cells) : CylinderCellWalk i k (q :: cells)

/-- 複体の写像は、元の全セル・共有面・入口・出口を同じ順序で移す。 -/
def cylinderCellWalkMap {U D B : SSet.{u}} {i j : U ⟶ D}
    {cells : List (U ⊗ (Δ[1] : SSet.{u}) ⟶ D)}
    (w : CylinderCellWalk i j cells) (p : D ⟶ B) :
    CylinderCellWalk (i ≫ p) (j ≫ p) (cells.map (· ≫ p)) := by
  induction w with
  | nil i => exact .nil _
  | cons q h₀ h₁ tail ih =>
      exact .cons (q ≫ p) (by rw [← Category.assoc, h₀])
        (by rw [← Category.assoc, h₁]) ih

end SerrePositivity.KST.SConstruction
