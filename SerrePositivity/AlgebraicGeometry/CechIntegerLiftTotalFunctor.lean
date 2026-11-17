module

public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotalShortExact

/-!
概要：元の整数係数の同じtotalを、加法的な関手として使う。
方針：各直和入射で加法性を照合し、既存の短完全性を渡す。
規約：同じ各項・微分・totalの選択を保持する。
使われ方：F8の核のtotalと元の増大複体の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits Preadditive
universe u
local notation "up" => ComplexShape.up ℕ

/-- 元の整数係数の二重複体を、同じMathlibのtotalへ送る関手。 -/
def cechIntegerLiftTotalFunctor : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up ⥤
    CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  HomologicalComplex₂.totalFunctor (ModuleCat.{u} ℤ) up up up

instance cechIntegerLiftTotalFunctor_additive :
    (cechIntegerLiftTotalFunctor : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up ⥤
      CochainComplex (ModuleCat.{u} ℤ) ℕ).Additive where
  map_add {K L f g} := by
    apply HomologicalComplex.Hom.ext
    funext n
    change (HomologicalComplex₂.total.map (f + g) up).f n =
      (HomologicalComplex₂.total.map f up).f n + (HomologicalComplex₂.total.map g up).f n
    apply HomologicalComplex₂.total.hom_ext
    intro a b h
    simp only [Preadditive.comp_add, HomologicalComplex₂.ιTotal_map,
      HomologicalComplex.add_f_apply, Preadditive.add_comp]

set_option backward.isDefEq.respectTransparency false in
/-- 元の同じ短完全性を、そのまま同じtotalの関手へ渡す。 -/
theorem cechIntegerLiftTotalFunctor_shortExact
    (S : ShortComplex (HomologicalComplex₂ (ModuleCat.{u} ℤ) up up)) (hS : S.ShortExact) :
    (S.map cechIntegerLiftTotalFunctor).ShortExact := by
  have h := cechIntegerLiftTotal_shortExact S hS
  exact h

end SerrePositivity.AlgebraicGeometry
