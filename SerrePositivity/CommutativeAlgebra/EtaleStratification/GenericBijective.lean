module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericEtale

/-!
# 局所化後の同型の延長

## 概要
有限加群の射が局所化後に同型なら、一つの分母を反転した段階で同型になる。

## 方針
核・余核の局所化を使い、その有限加群としての消滅の分母を払う。

## 規約
核の有限性のために基底の noetherian 性を仮定する。

## 使われ方
一般点で p 反転後に得られた逆射を主開集合へ延ばす。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

/-- 局所化された射の単射性は、核の局所化の消滅に等しい。 -/
theorem localizedMap_injective_iff_subsingleton_localized_ker
    {R M N : Type u} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (S : Submonoid R) (f : M →ₗ[R] N) :
    Function.Injective (LocalizedModule.map S f) ↔
      Subsingleton (LocalizedModule S (LinearMap.ker f)) := by
  let lM := LocalizedModule.mkLinearMap S M
  let lN := LocalizedModule.mkLinearMap S N
  let k := LinearMap.toKerIsLocalized S lM lN f
  let : IsLocalizedModule S k :=
    LinearMap.toKerLocalized_isLocalizedModule (Localization S) S lM lN f
  change Function.Injective (IsLocalizedModule.map S lM lN f) ↔ _
  rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
  exact (IsLocalizedModule.iso S k).subsingleton_congr.symm

/-- 局所化で同型になる有限加群の射は、一つの分母を反転すれば同型。 -/
theorem exists_away_bijective_of_localized_bijective
    {R M N : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (S : Submonoid R) (f : M →ₗ[R] N) (hf : Function.Bijective (LocalizedModule.map S f)) :
    ∃ g : S, Function.Bijective (LocalizedModule.map (Submonoid.powers (g : R)) f) := by
  have hk := (localizedMap_injective_iff_subsingleton_localized_ker S f).mp hf.injective
  have hc := (f.localizedMap_surjective_iff_subsingleton_localized_coker S).mp hf.surjective
  obtain ⟨g₁, hg₁⟩ := exists_away_subsingleton_of_localized_subsingleton S (LinearMap.ker f) hk
  obtain ⟨g₂, hg₂⟩ := exists_away_subsingleton_of_localized_subsingleton S (N ⧸ LinearMap.range f) hc
  refine ⟨g₁ * g₂, ?_, ?_⟩
  · apply (localizedMap_injective_iff_subsingleton_localized_ker _ f).mpr
    exact subsingleton_localizedModuleAway_mul (g₁ : R) (g₂ : R) hg₁
  · apply (f.localizedMap_surjective_iff_subsingleton_localized_coker _).mpr
    simpa [mul_comm] using subsingleton_localizedModuleAway_mul (g₂ : R) (g₁ : R) hg₂

end SerrePositivity.CommutativeAlgebra
