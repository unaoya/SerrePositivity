module

public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotal
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
import all SerrePositivity.HomologicalAlgebra.BicomplexColumnQuasiIso

/-!
概要：元の整数係数の各列の完全性を同じ全複体へ渡す。
方針：既存の行の判定を転置へ適用し、Mathlibの同じtotalFlipIsoで戻す。
規約：元の各項・微分と選択したtotalを保持する。
使われ方：F8の実際の全複体の余単体図式への代入。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
local notation "up" => ComplexShape.up ℕ
variable (K : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up) [K.HasTotal up]

/-- 同じ整数係数の各列が完全なら、元の全複体も完全。 -/
theorem cechIntegerLiftTotal_acyclic_of_columns (h : ∀ a, (K.X a).Acyclic) :
    (K.total up).Acyclic := by
  have hf : (K.flip.total up).Acyclic := by
    apply cechIntegerLiftTotal_acyclic_of_rows
    intro a b
    change (K.X b).ExactAt a
    exact h b a
  intro n
  exact (hf n).of_iso (K.totalFlipIso up)

end SerrePositivity.AlgebraicGeometry
