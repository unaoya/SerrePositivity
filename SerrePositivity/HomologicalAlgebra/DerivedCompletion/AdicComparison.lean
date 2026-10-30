module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Localization
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Module
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # 古典的主イデアル進完備性と導来完備性の比較

局所化の自由分解の双対を列作用へ同定し、実導来圏の消滅条件と比較する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Abelian
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 自由telescopeのExt⁰を、基底上の値の列へ同定する。 -/
def telescopeExtZeroEquiv (M : ModuleCat.{u} R) :
    Ext (ModuleCat.of R (LocalizationTelescopeFree R)) M 0 ≃ (ℕ → M) :=
  Ext.homEquiv₀.trans (ModuleCat.homEquiv.trans
    (localizationTelescopeHomEquiv R M).toEquiv)

/-- Ext⁰の差分写像は、列の差分作用に対応する。 -/
theorem telescopeExtZeroEquiv_precomp (f : R) (M : ModuleCat.{u} R)
    (e : Ext (ModuleCat.of R (LocalizationTelescopeFree R)) M 0) :
    telescopeExtZeroEquiv R M
      ((Ext.mk₀ (ModuleCat.ofHom (localizationTelescopeMap R f))).precomp M (add_zero 0) e) =
        adicRecurrenceMap f (telescopeExtZeroEquiv R M e) := by
  obtain ⟨g, rfl⟩ := Ext.mk₀_bijective _ _ |>.surjective e
  change telescopeExtZeroEquiv R M
    ((Ext.mk₀ (ModuleCat.ofHom (localizationTelescopeMap R f))).comp (Ext.mk₀ g) (zero_add 0)) = _
  rw [Ext.mk₀_comp_mk₀]
  have he {X Y : ModuleCat.{u} R} (h : X ⟶ Y) : Ext.homEquiv₀ (Ext.mk₀ h) = h :=
    Ext.homEquiv₀.apply_symm_apply h
  change localizationTelescopeHomEquiv R M
    (Ext.homEquiv₀ (Ext.mk₀ (ModuleCat.ofHom (localizationTelescopeMap R f) ≫ g))).hom =
      adicRecurrenceMap f (localizationTelescopeHomEquiv R M (Ext.homEquiv₀ (Ext.mk₀ g)).hom)
  rw [he, he]
  exact localizationTelescopeHomEquiv_comp R f M g.hom

/-- Ext¹の消滅は、列の差分作用の全射性と同値。 -/
theorem localization_ext_one_iff_recurrence_surjective (f : R) (M : ModuleCat.{u} R) :
    Subsingleton (Ext (ModuleCat.of R (Localization.Away f)) M 1) ↔
      Function.Surjective (adicRecurrenceMap f : (ℕ → M) →ₗ[R] (ℕ → M)) := by
  rw [localization_ext_one_subsingleton_iff]
  change Function.Surjective ((Ext.mk₀ (ModuleCat.ofHom
    (localizationTelescopeMap R f))).precomp M (add_zero 0)) ↔ _
  let e := telescopeExtZeroEquiv R M
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h (e.symm y)
    refine ⟨e x, ?_⟩
    change adicRecurrenceMap f (telescopeExtZeroEquiv R M x) = y
    rw [← telescopeExtZeroEquiv_precomp R f M]
    change e (((Ext.mk₀ (ModuleCat.ofHom
      (localizationTelescopeMap R f))).precomp M (add_zero 0)) x) = y
    rw [hx]
    exact e.apply_symm_apply y
  · intro h y
    obtain ⟨x, hx⟩ := h (e y)
    refine ⟨e.symm x, e.injective ?_⟩
    dsimp only [e]
    rw [telescopeExtZeroEquiv_precomp R f M]
    change adicRecurrenceMap f (e (e.symm x)) = e y
    simpa only [Equiv.apply_symm_apply] using hx

/-- Ext⁰の消滅は、自由分解の双対の単射性と同値。 -/
theorem localization_ext_zero_iff_precomp_injective (f : R) (M : ModuleCat.{u} R) :
    Subsingleton (Ext (ModuleCat.of R (Localization.Away f)) M 0) ↔
      Function.Injective ((Ext.mk₀ (ModuleCat.ofHom (localizationTelescopeMap R f))).precomp M
        (add_zero 0)) := by
  let S := localizationPresentation R f
  have hS : S.ShortExact := localizationPresentation_shortExact R f
  change Subsingleton (Ext S.X₃ M 0) ↔
    Function.Injective ((Ext.mk₀ S.f).precomp M (add_zero 0))
  rw [injective_iff_map_eq_zero]
  constructor
  · intro h x hx
    obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₂ hS M x hx
    rw [← hz, Subsingleton.elim z 0]
    simp
  · intro h
    apply subsingleton_of_forall_eq 0
    intro z
    let := hS.epi_g
    apply Ext.precomp_mk₀_injective_of_epi M S.g
    change (Ext.mk₀ S.g).comp z (zero_add 0) = _
    rw [map_zero]
    apply h
    change (Ext.mk₀ S.f).comp ((Ext.mk₀ S.g).comp z (zero_add 0)) (zero_add 0) = 0
    rw [Ext.mk₀_comp_mk₀_assoc, S.zero]
    simp

/-- Ext⁰の消滅は、列の差分作用の単射性と同値。 -/
theorem localization_ext_zero_iff_recurrence_injective (f : R) (M : ModuleCat.{u} R) :
    Subsingleton (Ext (ModuleCat.of R (Localization.Away f)) M 0) ↔
      Function.Injective (adicRecurrenceMap f : (ℕ → M) →ₗ[R] (ℕ → M)) := by
  rw [localization_ext_zero_iff_precomp_injective]
  let e := telescopeExtZeroEquiv R M
  constructor
  · intro h x y hxy
    apply e.symm.injective
    apply h
    apply e.injective
    dsimp only [e]
    rw [telescopeExtZeroEquiv_precomp, telescopeExtZeroEquiv_precomp]
    simpa only [Equiv.apply_symm_apply] using hxy
  · intro h x y hxy
    apply e.injective
    apply h
    rw [← telescopeExtZeroEquiv_precomp R f M, ← telescopeExtZeroEquiv_precomp R f M, hxy]

/-- 零次数に置いた二つの加群の負次数の導来射は零。 -/
theorem module_shiftedHom_eq_zero_of_neg (X Y : ModuleCat.{u} R) (n : ℤ) (hn : n < 0)
    (a : ShiftedHom ((moduleObjectFunctor R).obj X) ((moduleObjectFunctor R).obj Y) n) :
    a = 0 := by
  change ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj X ⟶
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Y)⟦n⟧) at a
  apply DerivedCategory.TStructure.t.zero_of_isLE_of_isGE a 0 (-n) (by omega)
  · infer_instance
  · exact DerivedCategory.TStructure.t.isGE_shift _ 0 n (-n) (by omega)

/-- 導来主元完備性は、局所化からのExt⁰とExt¹の消滅だけで判定できる。 -/
theorem isModuleComplete_iff_ext_zero_one (f : R) (M : ModuleCat.{u} R) :
    IsModuleComplete R f M ↔
      Subsingleton (Ext (ModuleCat.of R (Localization.Away f)) M 0) ∧
        Subsingleton (Ext (ModuleCat.of R (Localization.Away f)) M 1) := by
  constructor
  · intro h
    have hz (n : ℕ) (e : Ext (ModuleCat.of R (Localization.Away f)) M n) : e = 0 := by
      apply Ext.homEquiv.injective
      have h' := h n e.hom
      dsimp only [localizationObject, moduleObjectFunctor] at h'
      change e.hom = (0 : Ext (ModuleCat.of R (Localization.Away f)) M n).hom
      rw [Ext.zero_hom]
      exact h'
    exact ⟨subsingleton_of_forall_eq 0 (hz 0), subsingleton_of_forall_eq 0 (hz 1)⟩
  · rintro ⟨h0, h1⟩ n a
    dsimp only [localizationObject, moduleObjectFunctor] at a ⊢
    by_cases hn : 0 ≤ n
    · lift n to ℕ using hn
      change ShiftedHom
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R (Localization.Away f)))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) (n : ℤ) at a
      obtain ⟨e, rfl⟩ := Ext.homEquiv.surjective a
      have he : e = 0 := by
        cases n with
        | zero => exact h0.elim _ _
        | succ n =>
          cases n with
          | zero => exact h1.elim _ _
          | succ k => exact localization_ext_eq_zero R f M k e
      change e.hom = 0
      rw [he, Ext.zero_hom]
    · exact module_shiftedHom_eq_zero_of_neg R _ M n (by omega) a

/-- 導来主元完備性は、列の差分作用の全単射性と同値。 -/
theorem isModuleComplete_iff_recurrence_bijective (f : R) (M : ModuleCat.{u} R) :
    IsModuleComplete R f M ↔
      Function.Bijective (adicRecurrenceMap f : (ℕ → M) →ₗ[R] (ℕ → M)) := by
  rw [isModuleComplete_iff_ext_zero_one, localization_ext_zero_iff_recurrence_injective,
    localization_ext_one_iff_recurrence_surjective]
  rfl

/-- 古典的主元進完備な加群は導来完備。正則性は不要。 -/
theorem isModuleComplete_of_isAdicComplete (f : R) (M : ModuleCat.{u} R)
    [IsAdicComplete (Ideal.span {f}) M] : IsModuleComplete R f M :=
  (isModuleComplete_iff_recurrence_bijective R f M).mpr (adicRecurrenceMap_bijective f)

/-- fが単射に作用する加群では、導来完備性と古典的f進完備性が同値。 -/
theorem isModuleComplete_iff_isAdicComplete_of_regular (f : R) (M : ModuleCat.{u} R)
    (hreg : Function.Injective (fun x : M ↦ f • x)) :
    IsModuleComplete R f M ↔ IsAdicComplete (Ideal.span {f}) M := by
  rw [isModuleComplete_iff_recurrence_bijective,
    isAdicComplete_iff_adicRecurrenceMap_bijective_of_regular f hreg]

/-- pが零因子でない環での、導来p完備性と古典的p進完備性の比較。
素数性は必要ない。 -/
theorem isRingModuleComplete_iff_isAdicComplete_natCast (p : ℕ)
    (hp : Function.Injective (fun x : R ↦ (p : R) * x)) :
    IsModuleComplete R (p : R) (ModuleCat.of R R) ↔
      IsAdicComplete (Ideal.span {(p : R)}) R :=
  isModuleComplete_iff_isAdicComplete_of_regular R (p : R) (ModuleCat.of R R) hp

end SerrePositivity.DerivedCompletion
