module

public import SerrePositivity.HomologicalAlgebra.Cech.Basic
public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotal

/-!
概要：元の増大二重複体の各行を、同じ評価後の増大複体と比較する。
方針：B1の加法関手との交換と、既存HAの行によるtotalの完全性を使う。
規約：元の各行・増大・直和入射とtotalを保持する。
使われ方：矩形の実際の行の完全性を元の全複体へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
local notation "up" => ComplexShape.up ℕ
variable (E : CosimplicialObject.Augmented (CochainComplex (ModuleCat.{u} ℤ) ℕ))

set_option backward.isDefEq.respectTransparency false in
/-- 同じ縦次数の評価は、B1の同じ増大複体の各行との標準同型を与える。 -/
def cechAugmentedDoubleRowIso (b : ℕ) :
    SerrePositivity.HomologicalAlgebra.bicomplexRow
        (SerrePositivity.Cech.augmentedCochain.obj E) b ≅
      SerrePositivity.Cech.augmentedCochain.obj
        ((CosimplicialObject.Augmented.whiskeringObj _ _
          (HomologicalComplex.eval (ModuleCat.{u} ℤ) up b)).obj E) :=
  SerrePositivity.Cech.mapAugmentedCochainIso
    (HomologicalComplex.eval (ModuleCat.{u} ℤ) up b) E

set_option backward.isDefEq.respectTransparency false in
/-- 元の各行の完全性を、既存の行の判定で同じtotalの完全性へ渡す。 -/
theorem cechIntegerAugmentedDouble_acyclic_of_rows
    (h : ∀ b, (SerrePositivity.Cech.augmentedCochain.obj
      ((CosimplicialObject.Augmented.whiskeringObj _ _
        (HomologicalComplex.eval (ModuleCat.{u} ℤ) up b)).obj E)).Acyclic) :
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (SerrePositivity.Cech.augmentedCochain.obj E) up).Acyclic := by
  apply cechIntegerLiftTotal_acyclic_of_rows
  intro a b
  exact (h b a).of_iso (cechAugmentedDoubleRowIso E b).symm

end SerrePositivity.AlgebraicGeometry
