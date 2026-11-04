module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericVanishing
public import Mathlib.RingTheory.Etale.Kaehler

/-!
# 局所化後のエタール性の延長

## 概要
有限表示有限代数が分母系での局所化後に形式的エタールなら、一つの分母でエタールになる。

## 方針
微分加群と余接複体の第一ホモロジーの有限性を使い、両者の消滅の分母を払う。

## 規約
全商環に限らず基底の任意の分母系を扱う。

## 使われ方
一般点での分離部分の有限モデルを主開集合上で有限エタールにする。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

/-- Noetherian な有限表示代数の第一余接ホモロジーは有限加群。 -/
theorem finite_h1Cotangent_of_noetherian (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [IsNoetherianRing A]
    [Algebra.FinitePresentation R A] : Module.Finite A (Algebra.H1Cotangent R A) := by
  let P := Algebra.Presentation.ofFinitePresentation R A
  let : Module.Finite A P.toExtension.Cotangent := Algebra.Extension.Cotangent.finite P.fg_ker
  let : Module.Finite A P.toExtension.H1Cotangent :=
    inferInstanceAs (Module.Finite A (LinearMap.ker P.toExtension.cotangentComplex))
  exact Module.Finite.of_surjective P.equivH1Cotangent.toLinearMap P.equivH1Cotangent.surjective

/-- さらに別の元を反転しても、加群の消滅は保たれる。 -/
theorem subsingleton_localizedModuleAway_mul {R M : Type u}
    [CommRing R] [AddCommGroup M] [Module R M] (r s : R)
    (h : Subsingleton (LocalizedModule.Away r M)) :
    Subsingleton (LocalizedModule.Away (r * s) M) := by
  apply LocalizedModule.subsingleton_iff.mpr
  intro x
  obtain ⟨_, ⟨n, rfl⟩, hx⟩ := LocalizedModule.subsingleton_iff.mp h x
  refine ⟨(r * s) ^ n, ⟨n, rfl⟩, ?_⟩
  rw [mul_pow, mul_smul, smul_comm, hx, smul_zero]

/-- 局所化後に形式的エタールなら、一つの分母でエタールになる。 -/
theorem exists_away_etale_of_localized_formallyEtale
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsNoetherianRing A] [Module.Finite R A] [Algebra.FinitePresentation R A]
    (M : Submonoid R) [IsLocalization (Algebra.algebraMapSubmonoid A M) B]
    [Algebra.FormallyEtale R B] :
    ∃ g : M, Algebra.Etale R (Localization.Away (algebraMap R A g)) := by
  let : Module.Finite A (Algebra.H1Cotangent R A) := finite_h1Cotangent_of_noetherian R A
  let : Module.Finite R Ω[A⁄R] := Module.Finite.trans A Ω[A⁄R]
  let : Module.Finite R (Algebra.H1Cotangent R A) :=
    Module.Finite.trans A (Algebra.H1Cotangent R A)
  let f := (KaehlerDifferential.map R R A B).restrictScalars R
  let h := (Algebra.H1Cotangent.map R R A B).restrictScalars R
  let : IsLocalizedModule M f := IsLocalizedModule.restrictScalars M _
  let : IsLocalizedModule M h := IsLocalizedModule.restrictScalars M _
  obtain ⟨g₁, hg₁⟩ := exists_away_subsingleton_of_localized_subsingleton M Ω[A⁄R]
    ((IsLocalizedModule.iso M f).subsingleton_congr.mpr inferInstance)
  obtain ⟨g₂, hg₂⟩ := exists_away_subsingleton_of_localized_subsingleton M
    (Algebra.H1Cotangent R A) ((IsLocalizedModule.iso M h).subsingleton_congr.mpr inferInstance)
  let g : M := g₁ * g₂
  let A' := Localization.Away (algebraMap R A g)
  let : IsLocalization (Algebra.algebraMapSubmonoid A (Submonoid.powers (g : R))) A' := by
    rw [Algebra.algebraMapSubmonoid_powers]
    infer_instance
  let f' := (KaehlerDifferential.map R R A A').restrictScalars R
  let h' := (Algebra.H1Cotangent.map R R A A').restrictScalars R
  let : IsLocalizedModule (Submonoid.powers (g : R)) f' :=
    IsLocalizedModule.restrictScalars _ _
  let : IsLocalizedModule (Submonoid.powers (g : R)) h' :=
    IsLocalizedModule.restrictScalars _ _
  have hfzero : Subsingleton (LocalizedModule.Away (g : R) Ω[A⁄R]) :=
    subsingleton_localizedModuleAway_mul g₁ g₂ hg₁
  have hhzero : Subsingleton (LocalizedModule.Away (g : R) (Algebra.H1Cotangent R A)) := by
    simpa [g, mul_comm] using subsingleton_localizedModuleAway_mul (g₂ : R) (g₁ : R) hg₂
  let : Subsingleton Ω[A'⁄R] :=
    (IsLocalizedModule.iso (Submonoid.powers (g : R)) f').subsingleton_congr.mp hfzero
  let : Subsingleton (Algebra.H1Cotangent R A') :=
    (IsLocalizedModule.iso (Submonoid.powers (g : R)) h').subsingleton_congr.mp hhzero
  exact ⟨g, ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩⟩

end SerrePositivity.CommutativeAlgebra
