module

public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotalNaturality
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import all SerrePositivity.HomologicalAlgebra.BicomplexColumnQuasiIso

/-!
概要：元の整数係数の二重複体の短完全性を同じtotalへ渡す。
方針：既存HAの短完全性と、自然な同じ係数移送を使う。
規約：元の各項・射・totalの選択と係数の宇宙を保つ。
使われ方：F8の全複体の同じ有限coneと基底項の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
local notation "up" => ComplexShape.up ℕ
variable (S : ShortComplex (HomologicalComplex₂ (ModuleCat.{u} ℤ) up up))

/-- 同じ三項と同じ二つの射にtotalを取った短複体。 -/
def cechIntegerLiftTotalShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ) where
  X₁ := S.X₁.total up
  X₂ := S.X₂.total up
  X₃ := S.X₃.total up
  f := HomologicalComplex₂.total.map S.f up
  g := HomologicalComplex₂.total.map S.g up
  zero := by
    rw [← HomologicalComplex₂.total.map_comp, S.zero]
    ext n : 1
    apply HomologicalComplex₂.total.hom_ext
    intro a b h
    rw [HomologicalComplex₂.ιTotal_map]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- 元の短完全な二重複体の同じtotalも短完全。 -/
theorem cechIntegerLiftTotal_shortExact (hS : S.ShortExact) :
    (cechIntegerLiftTotalShortComplex S).ShortExact := by
  let F₂ := (cechIntegerLiftFunctor.mapHomologicalComplex up).mapHomologicalComplex up
  let F₁ := cechIntegerLiftFunctor.mapHomologicalComplex up
  have hhat := SerrePositivity.HomologicalAlgebra.totalShortExact
    (S.map F₂) (hS.map_of_exact F₂)
  let e : SerrePositivity.HomologicalAlgebra.totalShortComplex (S.map F₂) ≅
      (cechIntegerLiftTotalShortComplex S).map F₁ :=
    ShortComplex.isoMk (cechIntegerLiftTotalIso S.X₁) (cechIntegerLiftTotalIso S.X₂)
      (cechIntegerLiftTotalIso S.X₃)
      (by exact cechIntegerLiftTotalIso_naturality S.f)
      (by exact cechIntegerLiftTotalIso_naturality S.g)
  have hF := ShortComplex.shortExact_of_iso e hhat
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let D := ((cechIntegerLiftTotalShortComplex S).map F₁).map
    (HomologicalComplex.eval (ModuleCat.{u} (ULift.{u} ℤ)) up n)
  have hn : D.ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp hF n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact D).mp hn.exact
    exact he
  · apply (ModuleCat.mono_iff_injective _).mpr
    have he := (ModuleCat.mono_iff_injective D.f).mp hn.mono_f
    exact he
  · apply (ModuleCat.epi_iff_surjective _).mpr
    have he := (ModuleCat.epi_iff_surjective D.g).mp hn.epi_g
    exact he

end SerrePositivity.AlgebraicGeometry
