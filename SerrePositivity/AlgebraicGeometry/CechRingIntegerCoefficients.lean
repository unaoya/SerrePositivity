module

public import SerrePositivity.HomologicalAlgebra.Cech.Basic
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
概要：元の環の増大Čech完全性を、同じ整数加群の複体へ移す。
方針：加法群への忘却の同値と、B1の既存の比較を使う。
規約：係数の元と関数を保ち、AugmentedRingCechExactの定義を変えない。
使われ方：元の環の平坦降下の完全性を、矩形の行の係数へ供給する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u

/-- 元の環と環準同型を、同じ整数加群と準同型に見る係数移送。 -/
def ringToCechIntegerModule : CommRingCat.{u} ⥤ ModuleCat.{u} ℤ where
  obj R := ModuleCat.of ℤ R
  map f := ModuleCat.ofHom f.hom.toAddMonoidHom.toIntLinearMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 元の加法群の係数図式との、恒等成分による同じ比較。 -/
def ringToCechIntegerModuleForgetIso :
    ringToCechIntegerModule ⋙ forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u} ≅
      SerrePositivity.Cech.ringToAb :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ整数加群の増大複体の完全性は、加法群への忘却で保ち反映する。 -/
theorem cechIntegerAugmented_acyclic_iff (E : CosimplicialObject.Augmented (ModuleCat.{u} ℤ)) :
    (SerrePositivity.Cech.augmentedCochain.obj E).Acyclic ↔
      (SerrePositivity.Cech.augmentedCochain.obj
        ((CosimplicialObject.Augmented.whiskeringObj _ _
          (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})).obj E)).Acyclic := by
  let F := forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}
  let e := SerrePositivity.Cech.mapAugmentedCochainIso F E
  have h := SerrePositivity.Cech.acyclic_map_iff_of_exact F
    (SerrePositivity.Cech.augmentedCochain.obj E)
    (fun S ↦ S.exact_map_iff_of_faithful F)
  constructor
  · intro he n
    exact ((h.mpr he) n).of_iso e
  · intro he
    apply h.mp
    intro n
    exact (he n).of_iso e.symm

set_option backward.isDefEq.respectTransparency false in
/-- 元の環の増大Čech完全性は、同じ整数加群の増大複体の完全性と同値。 -/
theorem ringCechExact_iff_integer_acyclic (E : CosimplicialObject.Augmented CommRingCat.{u}) :
    SerrePositivity.Cech.AugmentedRingCechExact E ↔
      (SerrePositivity.Cech.augmentedCochain.obj
        ((CosimplicialObject.Augmented.whiskeringObj _ _ ringToCechIntegerModule).obj E)).Acyclic := by
  rw [cechIntegerAugmented_acyclic_iff, SerrePositivity.Cech.ringCechExact_iff_acyclic]
  let e := (CosimplicialObject.Augmented.whiskering _ _).mapIso ringToCechIntegerModuleForgetIso
  let ee := (e.app E)
  let ec := SerrePositivity.Cech.augmentedCochain.mapIso ee
  constructor
  · intro h n
    exact (h n).of_iso ec.symm
  · intro h n
    exact (h n).of_iso ec

end SerrePositivity.AlgebraicGeometry
