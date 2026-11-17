module

public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotalComponents
public import SerrePositivity.HomologicalAlgebra.BicomplexRowQuasiIso

/-!
概要：同じ整数係数の全複体を保って、既存の行の完全性のAPIへ渡す。
方針：元の直和入射と符号付き微分で標準比較を照合する。
規約：元の全複体と準同型の関数を保ち、基礎の宇宙は変更しない。
使われ方：平坦な二重 Čech の行の完全性から元の全複体へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits Preadditive
universe u
local notation "up" => ComplexShape.up ℕ
variable (K : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up)
variable [K.HasTotal up] [(cechIntegerLiftBicomplex K).HasTotal up]

set_option backward.isDefEq.respectTransparency false in
/-- 同じ直和の標準比較は、元の二方向の符号付き微分と可換。 -/
theorem cechIntegerLiftTotalComponentIso_d (n : ℕ) :
    (cechIntegerLiftTotalComponentIso K n).hom ≫
        cechIntegerLiftFunctor.map ((K.total up).d n (n + 1)) =
      ((cechIntegerLiftBicomplex K).total up).d n (n + 1) ≫
        (cechIntegerLiftTotalComponentIso K (n + 1)).hom := by
  let L := cechIntegerLiftBicomplex K
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  change a + b = n at h
  rw [← Category.assoc, cechIntegerLiftTotalComponentIso_ι, ← CategoryTheory.Functor.map_comp,
    ← Category.assoc]
  change cechIntegerLiftFunctor.map (K.ιTotal up a b n h ≫
      (K.D₁ up n (n + 1) + K.D₂ up n (n + 1))) =
    (L.ιTotal up a b n h ≫ (L.D₁ up n (n + 1) + L.D₂ up n (n + 1))) ≫
      (cechIntegerLiftTotalComponentIso K (n + 1)).hom
  rw [comp_add, K.ι_D₁, K.ι_D₂,
    K.d₁_eq up (show (ComplexShape.up ℕ).Rel a (a + 1) by rfl) b (n + 1) (by change a + 1 + b = n + 1; omega),
    K.d₂_eq up a (show (ComplexShape.up ℕ).Rel b (b + 1) by rfl) (n + 1) (by change a + (b + 1) = n + 1; omega),
    comp_add, L.ι_D₁, L.ι_D₂,
    L.d₁_eq up (show (ComplexShape.up ℕ).Rel a (a + 1) by rfl) b (n + 1) (by change a + 1 + b = n + 1; omega),
    L.d₂_eq up a (show (ComplexShape.up ℕ).Rel b (b + 1) by rfl) (n + 1) (by change a + (b + 1) = n + 1; omega)]
  simp only [CategoryTheory.Functor.map_add, Units.smul_def, CategoryTheory.Functor.map_zsmul,
    CategoryTheory.Functor.map_comp, add_comp, zsmul_comp, Category.assoc,
    cechIntegerLiftTotalComponentIso_ι]
  dsimp only [L]
  simp only [cechIntegerLiftTotalComponentIso_ι]
  rfl

/-- 元の全複体を、同じ整数係数の同値関手で移した全複体との標準同型。 -/
def cechIntegerLiftTotalIso :
    (cechIntegerLiftBicomplex K).total up ≅
      (cechIntegerLiftFunctor.mapHomologicalComplex up).obj (K.total up) :=
  HomologicalComplex.Hom.isoOfComponents (cechIntegerLiftTotalComponentIso K) (fun i j h ↦ by
    have hj : i + 1 = j := h
    subst j
    exact cechIntegerLiftTotalComponentIso_d K i)

/-- 同じ整数係数の移送は、元の全複体の完全性を保ち反映する。 -/
theorem cechIntegerLiftTotal_acyclic_iff :
    ((cechIntegerLiftBicomplex K).total up).Acyclic ↔ (K.total up).Acyclic := by
  constructor
  · intro h i
    exact (cechIntegerLiftComplex_exactAt_iff (K.total up) i).mp
      ((h i).of_iso (cechIntegerLiftTotalIso K))
  · intro h i
    exact ((cechIntegerLiftComplex_exactAt_iff (K.total up) i).mpr (h i)).of_iso
      (cechIntegerLiftTotalIso K).symm

/-- 元の整数係数の行が完全なら、既存のHAの判定により元の全複体も完全。 -/
theorem cechIntegerLiftTotal_acyclic_of_rows
    (h : ∀ a b, (SerrePositivity.HomologicalAlgebra.bicomplexRow K b).ExactAt a) :
    (K.total up).Acyclic := by
  apply (cechIntegerLiftTotal_acyclic_iff K).mp
  intro i
  apply SerrePositivity.HomologicalAlgebra.bicomplexTotal_exactAt_of_rows
    (cechIntegerLiftBicomplex K) ?_ i
  intro a b
  have he := (cechIntegerLiftComplex_exactAt_iff
    (SerrePositivity.HomologicalAlgebra.bicomplexRow K b) a).mpr (h a b)
  exact he

end SerrePositivity.AlgebraicGeometry
