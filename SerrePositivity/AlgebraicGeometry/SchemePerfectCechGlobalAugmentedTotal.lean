module

public import SerrePositivity.AlgebraicGeometry.CechIntegerTotalToRowZeroIso
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleAugmentedGlobal

/-!
概要：元の増大Γ複体と、singleを入れた同じtotalの標準比較。
方針：元の軸射影と既存のsingleの評価の標準同型を合成する。
規約：基底の増大を含め、同じ各項・射・次数を保つČech版。
使われ方：元のアフィン環の増大conerveの完全性への出口。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
local notation "up" => ComplexShape.up ℕ

set_option backward.isDefEq.respectTransparency false in
/-- 元の増大図式のsingleのtotalは、元の増大複体そのものと標準同型。 -/
def cechSingleAugmentedTotalIso
    (X : CosimplicialObject.Augmented (ModuleCat.{u} ℤ)) :
    HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (SerrePositivity.Cech.augmentedCochain.obj
        ((CosimplicialObject.Augmented.whiskeringObj _ _
          (HomologicalComplex.single (ModuleCat.{u} ℤ) up 0)).obj X)) up ≅
      SerrePositivity.Cech.augmentedCochain.obj X := by
  let S := HomologicalComplex.single (ModuleCat.{u} ℤ) up 0
  let E := HomologicalComplex.eval (ModuleCat.{u} ℤ) up 0
  let K : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up :=
    SerrePositivity.Cech.augmentedCochain.obj
      ((CosimplicialObject.Augmented.whiskeringObj _ _ S).obj X)
  have hz : ∀ a b, b ≠ 0 → IsZero ((K.X a).X b) := by
    intro a b hb
    cases a with
    | zero => exact HomologicalComplex.isZero_single_obj_X up 0 X.left b hb
    | succ a =>
      exact HomologicalComplex.isZero_single_obj_X up 0
        (X.right.obj (SimplexCategory.mk a)) b hb
  let e₁ := SerrePositivity.Cech.mapAugmentedCochainIso S X
  let e₂ := (E.mapHomologicalComplex up).mapIso e₁.symm
  let e₃ := (Functor.mapHomologicalComplexCompIso
    (HomologicalComplex.singleCompEvalIsoSelf (ModuleCat.{u} ℤ) up 0) up).app
      (SerrePositivity.Cech.augmentedCochain.obj X)
  let e₄ := (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} ℤ) up).app
    (SerrePositivity.Cech.augmentedCochain.obj X)
  exact cechIntegerTotalToRowZeroIso K hz ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

variable {R : Type u} [CommRing R] {Y : Scheme.{u}}
variable (f : Y ⟶ Spec (CommRingCat.of R)) {ι : Type} [Fintype ι] [DecidableEq ι]
variable (U : ι → Y.Opens) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)

/-- 実際のΓのsingleのtotalと、同じ元のΓ増大複体の比較。 -/
def schemePerfectCechGlobalAugmentedTotalIso :
    (schemePerfectCechGlobalAugmentedDouble f p hp hR).total up ≅
      SerrePositivity.Cech.augmentedCochain.obj (schemePerfectCechGlobalAugmented f p hp hR) :=
  cechSingleAugmentedTotalIso (schemePerfectCechGlobalAugmented f p hp hR)

set_option backward.isDefEq.respectTransparency false in
/-- 元のアフィンnerveのタプルtotalの完全性と、増大Γ複体の完全性の一致のČech版。
Stacks 30.2.6 に対応する各列の比較を使う。
分離的なスキームの準連接層ではアフィン被覆のČechと一致する
（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem affineCechNerveTupleAugmentedGlobal_acyclic_iff [IsAffine Y]
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤) :
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (schemePerfectCechTupleDouble f U p hp hR) up).Acyclic ↔
      (SerrePositivity.Cech.augmentedCochain.obj
        (schemePerfectCechGlobalAugmented f p hp hR)).Acyclic := by
  let φ := HomologicalComplex₂.total.map
    (schemePerfectCechTupleAugmentedGlobalDoubleMap f U p hp hR) up
  haveI : QuasiIso φ := affineCechNerveTupleAugmentedGlobalTotal_quasiIso f U p hp hR hU hcU
  let e := schemePerfectCechGlobalAugmentedTotalIso f p hp hR
  constructor
  · intro h n
    exact ((_root_.exactAt_iff_of_quasiIsoAt φ n).mpr (h n)).of_iso e
  · intro h n
    exact (_root_.exactAt_iff_of_quasiIsoAt φ n).mp ((h n).of_iso e.symm)

end SerrePositivity.AlgebraicGeometry
