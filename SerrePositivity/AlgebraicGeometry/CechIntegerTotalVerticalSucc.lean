module

public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotal
import all SerrePositivity.HomologicalAlgebra.BicomplexProjection

/-!
概要：同じ二重複体の縦次数を一つ送る各射を、元のtotalDescへまとめる。
方針：元のtotalの各直和入射で二方向の微分を照合する。
規約：外次数の符号は保ち、ここでは整数添字のshiftを用いない。
使われ方：元のF8の中心側の全複体の再索引。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits Preadditive
universe u
local notation "up" => ComplexShape.up ℕ
variable (K L : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up)
variable (α : ∀ a b : ℕ, (K.X a).X b ⟶ (L.X a).X (b + 1))

/-- 縦次数を一つ送る同じ各脚を、元の全次数n+1へまとめる。 -/
def cechIntegerTotalVerticalSuccComponent (n : ℕ) : (K.total up).X n ⟶ (L.total up).X (n + 1) :=
  K.totalDesc (fun a b h ↦ α a b ≫ L.ιTotal up a (b + 1) (n + 1)
    (by change a + b = n at h; change a + (b + 1) = n + 1; omega))

/-- 元の各直和入射に沿う、同じ全次数を一つ上げる射の式。 -/
theorem ι_cechIntegerTotalVerticalSuccComponent (a b n : ℕ)
    (h : ComplexShape.π up up up (a, b) = n) :
    K.ιTotal up a b n h ≫ cechIntegerTotalVerticalSuccComponent K L α n =
      α a b ≫ L.ιTotal up a (b + 1) (n + 1)
        (by change a + b = n at h; change a + (b + 1) = n + 1; omega) :=
  HomologicalComplex₂.ι_totalDesc _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- 各射が元の二方向の微分を保てば、同じtotalDescの射も元の全微分を保つ。 -/
theorem cechIntegerTotalVerticalSuccComponent_d
    (hH : ∀ a b, α a b ≫ (L.d a (a + 1)).f (b + 1) =
      (K.d a (a + 1)).f b ≫ α (a + 1) b)
    (hV : ∀ a b, α a b ≫ (L.X a).d (b + 1) (b + 2) =
      (K.X a).d b (b + 1) ≫ α a (b + 1)) (n : ℕ) :
    cechIntegerTotalVerticalSuccComponent K L α n ≫ (L.total up).d (n + 1) (n + 2) =
      (K.total up).d n (n + 1) ≫ cechIntegerTotalVerticalSuccComponent K L α (n + 1) := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  rw [← Category.assoc, ι_cechIntegerTotalVerticalSuccComponent, Category.assoc,
    SerrePositivity.HomologicalAlgebra.total_d_summand L a (b + 1) (n + 1)
      (by change a + b = n at h; change a + (b + 1) = n + 1; omega)]
  rw [← Category.assoc (K.ιTotal up a b n h),
    SerrePositivity.HomologicalAlgebra.total_d_summand K a b n h,
    add_comp, zsmul_comp, Category.assoc, ι_cechIntegerTotalVerticalSuccComponent,
    Category.assoc, ι_cechIntegerTotalVerticalSuccComponent]
  simp only [comp_add, comp_zsmul, ← Category.assoc, hH, hV]

end SerrePositivity.AlgebraicGeometry
