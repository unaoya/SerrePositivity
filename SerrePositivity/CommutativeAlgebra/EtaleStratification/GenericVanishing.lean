module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericPoints
public import Mathlib.RingTheory.Support

/-!
# 有限加群の一般点での消滅を主開集合に延ばす

## 概要
全極小点で消える有限加群は、全極小点を残す一つの主開集合で消える。

## 方針
有限加群の台は零化イデアルの零点集合であり、素イデアル回避で共通の元を選ぶ。

## 規約
加群の局所化には `LocalizedModule` を使う。

## 使われ方
一般点での有限個の関係と逆射の等式を主開集合へ延ばす。
-/

@[expose] public section
noncomputable section
universe u v

namespace SerrePositivity.CommutativeAlgebra

/-- 有限加群が全極小点で消えるなら、全極小点を残す主開集合で消える。 -/
theorem exists_away_subsingleton_of_generic_vanishing
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : ∀ P : GenericPoint R, Subsingleton (LocalizedModule P.val.asIdeal.primeCompl M)) :
    ∃ g : R, (∀ P : GenericPoint R, g ∉ P.val.asIdeal) ∧
      Subsingleton (LocalizedModule.Away g M) := by
  obtain ⟨g, hg, havoid⟩ := exists_mem_ideal_avoiding_genericPoints
    (Module.annihilator R M) (fun P hP ↦
      (Module.notMem_support_iff.mpr (hM P)) (Module.mem_support_iff_of_finite.mpr hP))
  exact ⟨g, havoid, LocalizedModule.subsingleton_iff.mpr
    fun m ↦ ⟨g, Submonoid.mem_powers g, Module.mem_annihilator.mp hg m⟩⟩

/-- 有限加群の射が全極小点で全射なら、全極小点を残す主開集合で全射。 -/
theorem exists_away_surjective_of_generic_surjective
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Finite R N] (f : M →ₗ[R] N)
    (hf : ∀ P : GenericPoint R, Function.Surjective
      (LocalizedModule.map P.val.asIdeal.primeCompl f)) :
    ∃ g : R, (∀ P : GenericPoint R, g ∉ P.val.asIdeal) ∧
      Function.Surjective (LocalizedModule.map (Submonoid.powers g) f) := by
  simp_rw [f.localizedMap_surjective_iff_subsingleton_localized_coker] at hf ⊢
  exact exists_away_subsingleton_of_generic_vanishing (N ⧸ LinearMap.range f) hf

end SerrePositivity.CommutativeAlgebra
