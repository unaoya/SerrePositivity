module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.TotalComplex
public import SerrePositivity.HomologicalAlgebra.BicomplexProjection
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
概要：元の整数係数を同型な大きい整数環へ移し、同じ全複体の直和項を比較する。
方針：Mathlib のスカラー制限の同値と、同じ余積を保つ標準比較を使う。
規約：元の加群と準同型の関数、直和の各入射を保持する。
使われ方：既存のHAの全複体APIへ、係数の宇宙を狭めずに渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
local notation "up" => ComplexShape.up ℕ

/-- 同じ整数係数を、同型な大きい整数環によるスカラー制限で移す同値関手。 -/
def cechIntegerLiftFunctor : ModuleCat.{u} ℤ ⥤ ModuleCat.{u} (ULift.{u} ℤ) :=
  ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom

/-- 同じスカラー制限の正逆と単位を、整数環の異なる宇宙を保って明示した同値。 -/
def cechIntegerLiftEquivalence : ModuleCat.{u} ℤ ≌ ModuleCat.{u} (ULift.{u} ℤ) := by
  let e : ULift.{u} ℤ ≃+* ℤ := ULift.ringEquiv
  exact
    { functor := cechIntegerLiftFunctor
      inverse := ModuleCat.restrictScalars e.symm.toRingHom
      unitIso := (ModuleCat.restrictScalarsId ℤ).symm ≪≫
        ModuleCat.restrictScalarsComp' e.symm.toRingHom e.toRingHom (RingHom.id ℤ)
          (by ext x; rfl)
      counitIso := (ModuleCat.restrictScalarsComp' e.toRingHom e.symm.toRingHom
        (RingHom.id (ULift.{u} ℤ)) (by ext x; rfl)).symm ≪≫
          ModuleCat.restrictScalarsId (ULift.{u} ℤ) }

instance : (cechIntegerLiftFunctor.{u}).IsEquivalence :=
  (cechIntegerLiftEquivalence.{u}).isEquivalence_functor

instance : (cechIntegerLiftFunctor.{u}).Additive := by
  unfold cechIntegerLiftFunctor
  infer_instance

/-- 同じスカラー制限は、元の準同型の関数を変えない。 -/
theorem cechIntegerLiftFunctor_map_apply {M N : ModuleCat.{u} ℤ} (g : M ⟶ N) (x : M) :
    (cechIntegerLiftFunctor.map g).hom x = g.hom x := rfl

/-- 同じスカラー制限は、元の複体の各次数の完全性を保ち、反映する。 -/
theorem cechIntegerLiftComplex_exactAt_iff (C : CochainComplex (ModuleCat.{u} ℤ) ℕ) (i : ℕ) :
    ((cechIntegerLiftFunctor.mapHomologicalComplex up).obj C).ExactAt i ↔ C.ExactAt i := by
  simp only [HomologicalComplex.exactAt_iff,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  rfl

/-- 元の二重複体に、同じ既存の係数関手を二方向へ適用した値。 -/
abbrev cechIntegerLiftBicomplex (K : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up) :
    HomologicalComplex₂ (ModuleCat.{u} (ULift.{u} ℤ)) up up :=
  ((cechIntegerLiftFunctor.mapHomologicalComplex up).mapHomologicalComplex up).obj K

variable (K : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up)
variable [K.HasTotal up] [(cechIntegerLiftBicomplex K).HasTotal up]

/-- 同じ全複体の各直和と係数移送との、元の余積を保つ標準同型。 -/
def cechIntegerLiftTotalComponentIso (n : ℕ) :
    ((cechIntegerLiftBicomplex K).total up).X n ≅
      cechIntegerLiftFunctor.obj ((K.total up).X n) :=
  (PreservesCoproduct.iso cechIntegerLiftFunctor
    (K.toGradedObject.mapObjFun (ComplexShape.π up up up) n)).symm

set_option backward.isDefEq.respectTransparency false in
/-- 同じ直和の標準比較は、元の全複体の各入射を保つ。 -/
theorem cechIntegerLiftTotalComponentIso_ι (a b n : ℕ)
    (h : ComplexShape.π up up up (a, b) = n) :
    (cechIntegerLiftBicomplex K).ιTotal up a b n h ≫
        (cechIntegerLiftTotalComponentIso K n).hom =
      cechIntegerLiftFunctor.map (K.ιTotal up a b n h) := by
  let V := K.toGradedObject.mapObjFun (ComplexShape.π up up up) n
  change Sigma.ι (fun j ↦ cechIntegerLiftFunctor.obj (V j)) ⟨(a, b), h⟩ ≫
    (PreservesCoproduct.iso cechIntegerLiftFunctor V).inv = _
  rw [PreservesCoproduct.inv_hom]
  exact ι_comp_sigmaComparison cechIntegerLiftFunctor V ⟨(a, b), h⟩

end SerrePositivity.AlgebraicGeometry
