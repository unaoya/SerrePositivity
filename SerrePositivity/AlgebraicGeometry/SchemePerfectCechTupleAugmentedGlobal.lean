module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechGlobalAugmented
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleAugmentationFactor
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleDouble
public import SerrePositivity.AlgebraicGeometry.AffineCechNerveTupleGlobalTotal

/-!
概要：元の基底環の増大を保つ、ΓのsingleとタプルČechの比較。
方針：既存の増大の因子分解と各列の単射な擬同型を代入する。
規約：元の同じ増大二重複体と実際の全写像を保つČech版。
使われ方：アフィン環の元の増大conerveへの出口。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
local notation "up" => ComplexShape.up ℕ
variable {R : Type u} [CommRing R] {Y : Scheme.{u}}
variable (f : Y ⟶ Spec (CommRingCat.of R)) {ι : Type} [Fintype ι] [DecidableEq ι]
variable (U : ι → Y.Opens) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ基底項の恒等射と実際のΓ増大からなる増大図式の射。 -/
def schemePerfectCechTupleAugmentedGlobalMap :
    schemePerfectCechGlobalSingleAugmented f p hp hR ⟶
      schemePerfectCechTupleAugmented f U p hp hR where
  left := 𝟙 _
  right := schemePerfectCechTupleGlobalAugmentation f U p hp
    (schemeCechNervePresheaf_primeCast f p hR)
  w := by
    apply NatTrans.ext
    funext n
    change 𝟙 _ ≫ schemePerfectCechTupleAugmentationHom f U p hp hR n =
      (HomologicalComplex.single (ModuleCat.{u} ℤ) up 0).map
        (schemePerfectCechGlobalScalar f p hp hR n) ≫
      schemePerfectCechTupleGlobalAugmentationHom f U p hp
        (schemeCechNervePresheaf_primeCast f p hR) n
    rw [Category.id_comp]
    exact schemePerfectCechTupleAugmentationHom_factor_global f U p hp hR n

/-- 同じΓの増大図式にB1の既存の複体関手を代入した値。 -/
def schemePerfectCechGlobalAugmentedDouble :
    HomologicalComplex₂ (ModuleCat.{u} ℤ) up up :=
  SerrePositivity.Cech.augmentedCochain.obj (schemePerfectCechGlobalSingleAugmented f p hp hR)

/-- 元の基底の増大を含む、同じ二重複体の実際の比較射。 -/
def schemePerfectCechTupleAugmentedGlobalDoubleMap :
    schemePerfectCechGlobalAugmentedDouble f p hp hR ⟶
      schemePerfectCechTupleDouble f U p hp hR :=
  SerrePositivity.Cech.augmentedCochain.map (schemePerfectCechTupleAugmentedGlobalMap f U p hp hR)

/-- 元の基底項での比較は恒等射。 -/
theorem schemePerfectCechTupleAugmentedGlobalDoubleMap_zero :
    (schemePerfectCechTupleAugmentedGlobalDoubleMap f U p hp hR).f 0 = 𝟙 _ := rfl

/-- 元の各nerve項での比較は同じ実際のΓ増大。 -/
theorem schemePerfectCechTupleAugmentedGlobalDoubleMap_succ (n : ℕ) :
    (schemePerfectCechTupleAugmentedGlobalDoubleMap f U p hp hR).f (n + 1) =
      schemePerfectCechTupleGlobalAugmentationHom f U p hp
        (schemeCechNervePresheaf_primeCast f p hR) ⦋n⦌ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- 同じ基底の増大を含むΓとタプルČechのtotal比較は擬同型であるČech版。
Stacks 30.2.6 に対応する各列の比較を使う。
分離的なスキームの準連接層ではアフィン被覆のČechと一致する
（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem affineCechNerveTupleAugmentedGlobalTotal_quasiIso [IsAffine Y]
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤) :
    QuasiIso (HomologicalComplex₂.total.map
      (schemePerfectCechTupleAugmentedGlobalDoubleMap f U p hp hR) up) := by
  apply cechIntegerLiftTotal_quasiIso_of_mono_columns
  · intro a
    cases a with
    | zero => exact inferInstanceAs (QuasiIso (𝟙 _))
    | succ a =>
      exact affineCechNerveTupleGlobalAugmentation_quasiIso f U p hp
        (schemeCechNervePresheaf_primeCast f p hR) hU hcU ⦋a⦌
  · intro a b
    cases a with
    | zero => exact Function.injective_id
    | succ a =>
      exact (ModuleCat.mono_iff_injective _).mp
        (affineCechNerveTupleGlobalAugmentation_mono_f f U p hp
          (schemeCechNervePresheaf_primeCast f p hR) hU hcU ⦋a⦌ b)

end SerrePositivity.AlgebraicGeometry
