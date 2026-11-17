module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleConstantAugmentation
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleDouble
public import SerrePositivity.AlgebraicGeometry.CechConstantTotalRetraction

/-!
概要：元の全次数の増大から、同じsingleのタプル二重Čechの完全性へ戻す。
方針：元の増大の一致を左右恒等の同型にまとめ、既存のtotalとretractを使う。
規約：元の二重複体・同じ係数・選択したtotalを変更しない。
使われ方：行の完全性から、元の増大されたタプル複体の完全性を得る。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
local notation "up" => ComplexShape.up ℕ
variable {R : Type u} [CommRing R] {Y : Scheme.{u}}
variable (f : Y ⟶ Spec (CommRingCat.of R)) {ι : Type} [Fintype ι] [DecidableEq ι]
variable (U : ι → Y.Opens) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 左右の恒等と、元の同じsingleの増大の一致による増大図式の同型。 -/
def schemePerfectCechTupleSingleAugmentedIso :
    cechSingleAugmentedObject (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))
      (schemePerfectCechTupleFunctor f U p hp (schemeCechNervePresheaf_primeCast f p hR))
      (schemePerfectCechTupleConstantAugmentationHom f U p hp hR) ≅
        schemePerfectCechTupleAugmented f U p hp hR :=
  Comma.isoMk (Iso.refl _) (Iso.refl _) (by
    apply NatTrans.ext
    funext n
    change schemePerfectCechTupleAugmentationHom f U p hp hR n =
      cechConstantSingleAugmentation (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR)) ≫
        schemePerfectCechTupleConstantAugmentation f U p hp hR n
    exact (schemePerfectCechTupleConstantAugmentation_single f U p hp hR n).symm)

/-- 元の全次数の増大を、B1の同じ二重複体の関手に代入したもの。 -/
def schemePerfectCechTupleConstantDouble :
    CochainComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ) ℕ :=
  SerrePositivity.Cech.augmentedCochain.obj
    (cechConstantAugmentedObject (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))
      (schemePerfectCechTupleFunctor f U p hp (schemeCechNervePresheaf_primeCast f p hR))
      (schemePerfectCechTupleConstantAugmentationHom f U p hp hR))

set_option backward.isDefEq.respectTransparency false in
/-- 同じ定数増大列のtotalの完全性を、元のsingleのタプル複体へ戻す。 -/
theorem schemePerfectCechTupleDouble_acyclic_of_constant
    (h : (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (schemePerfectCechTupleConstantDouble f U p hp hR) up).Acyclic) :
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (schemePerfectCechTupleDouble f U p hp hR) up).Acyclic := by
  have hs := cechSingleTotal_acyclic_of_constant
    (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))
    (schemePerfectCechTupleFunctor f U p hp (schemeCechNervePresheaf_primeCast f p hR))
    (schemePerfectCechTupleConstantAugmentationHom f U p hp hR) h
  let e := SerrePositivity.Cech.augmentedCochain.mapIso
    (schemePerfectCechTupleSingleAugmentedIso f U p hp hR)
  intro n
  exact (hs n).of_iso (HomologicalComplex₂.total.mapIso e up)

end SerrePositivity.AlgebraicGeometry
