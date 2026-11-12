module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Tactic.Abel

/-!
概要：サイクルの前像と境界の反映から、加群の短複体の H の同型を得る。
方針：H の元をサイクルで表し、opcycles への単射で境界の差を判定する。
規約：層の導来関手の H との比較は使わない。Čech 複体の各次数へ適用する加群の計算。
使われ方：共通アフィン細分の cone の完全性から、実際の Čech H の同型を作る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R : Type u} [CommRing R]
variable (S T : ShortComplex (ModuleCat.{u} R))

/-- 元で与えたサイクルを、短複体の抽象的な cycles の元にする。 -/
def cechCyclesOf (x : S.X₂) (hx : S.g.hom x = 0) : S.cycles :=
  S.cyclesMk x hx

/-- 元で与えたサイクルの値は、元の元に戻る。 -/
theorem cechCyclesOf_value (x : S.X₂) (hx : S.g.hom x = 0) :
    S.iCycles.hom (cechCyclesOf S x hx) = x := by
  exact S.i_cyclesMk x hx

/-- cycles の元の値は、微分で零になる。 -/
theorem cechCyclesValue_isCycle (x : S.cycles) : S.g.hom (S.iCycles.hom x) = 0 := by
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using congrArg (fun f ↦ f.hom x) S.iCycles_g

/-- サイクルの H の類を opcycles に写すと、その値の類になる。 -/
theorem cechHomologyCycleValue (x : S.cycles) :
    S.homologyι.hom (S.homologyπ.hom x) = S.pOpcycles.hom (S.iCycles.hom x) := by
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
    congrArg (fun f ↦ f.hom x) S.homology_π_ι

/-- 短複体の射の H 上の写像は、サイクルの値に元の射を適用する。 -/
theorem cechHomologyMapCycleValue (φ : S ⟶ T) (x : S.cycles) :
    T.homologyι.hom ((ShortComplex.homologyMap φ).hom (S.homologyπ.hom x)) =
      T.pOpcycles.hom (φ.τ₂.hom (S.iCycles.hom x)) := by
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
    congrArg (fun f ↦ f.hom x) (ShortComplex.π_homologyMap_ι φ)

/-- 目標の各サイクルが境界を除いて持ち上がれば、H の射は全射。 -/
theorem cechHomologyMap_surjective_of_cycles (φ : S ⟶ T)
    (hsurj : ∀ y : T.X₂, T.g.hom y = 0 →
      ∃ (x : S.X₂) (b : T.X₁), S.g.hom x = 0 ∧ φ.τ₂.hom x = y + T.f.hom b) :
    Function.Surjective (ShortComplex.homologyMap φ).hom := by
  intro y
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective T.homologyπ).mp inferInstance y
  obtain ⟨x, b, hx, he⟩ := hsurj (T.iCycles.hom z) (cechCyclesValue_isCycle T z)
  refine ⟨S.homologyπ.hom (cechCyclesOf S x hx), ?_⟩
  apply (ModuleCat.mono_iff_injective T.homologyι).mp inferInstance
  rw [cechHomologyMapCycleValue, cechHomologyCycleValue, cechCyclesOf_value]
  apply (T.moduleCat_pOpcycles_eq_iff _ _).mpr
  refine ⟨b, ?_⟩
  rw [he]
  abel

/-- 境界への写像を元の境界へ戻せれば、H の射は単射。 -/
theorem cechHomologyMap_injective_of_cycles (φ : S ⟶ T)
    (hinj : ∀ x : S.X₂, S.g.hom x = 0 →
      (∃ b : T.X₁, T.f.hom b = φ.τ₂.hom x) → ∃ a : S.X₁, S.f.hom a = x) :
    Function.Injective (ShortComplex.homologyMap φ).hom := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro y hy
  change (ShortComplex.homologyMap φ).hom y = 0 at hy
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance y
  have hp : T.pOpcycles.hom (φ.τ₂.hom (S.iCycles.hom z)) = 0 := by
    have h := congrArg T.homologyι.hom hy
    rw [cechHomologyMapCycleValue, map_zero] at h
    exact h
  obtain ⟨b, hb⟩ := (T.moduleCat_pOpcycles_eq_zero_iff _).mp hp
  obtain ⟨a, ha⟩ := hinj (S.iCycles.hom z) (cechCyclesValue_isCycle S z) ⟨b, hb⟩
  apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
  rw [cechHomologyCycleValue, map_zero]
  exact (S.moduleCat_pOpcycles_eq_zero_iff _).mpr ⟨a, ha⟩

/-- サイクルの持ち上げと境界の反映から、各次数の H の同型性を得る。 -/
theorem cechHomologyMap_isIso_of_cycles (φ : S ⟶ T)
    (hsurj : ∀ y : T.X₂, T.g.hom y = 0 →
      ∃ (x : S.X₂) (b : T.X₁), S.g.hom x = 0 ∧ φ.τ₂.hom x = y + T.f.hom b)
    (hinj : ∀ x : S.X₂, S.g.hom x = 0 →
      (∃ b : T.X₁, T.f.hom b = φ.τ₂.hom x) → ∃ a : S.X₁, S.f.hom a = x) :
    IsIso (ShortComplex.homologyMap φ) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ⟨cechHomologyMap_injective_of_cycles S T φ hinj,
    cechHomologyMap_surjective_of_cycles S T φ hsurj⟩

end SerrePositivity.AlgebraicGeometry
