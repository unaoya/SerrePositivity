module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericPrimeVanishing
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.Factorization
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-!
# p 反転後の同型を主開集合へ広げる

## 概要
有限代数の単射が一般点で p 反転後に全射なら、一つの主開集合で同じ性質を持つ。

## 方針
有限余核の p 冪 torsion の分母を払い、加群の局所化と環の局所化を同定する。

## 規約
単射性は元のモデルの包含から与える。一般点での全射性は元ごとの p 冪倍で記述。

## 使われ方
Lemma 10.12 の p 反転後の同型という結論を延長する。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

/-- 加群として局所化した代数射が全射なら、対応する環の主局所化の射も全射。 -/
theorem awayMap_surjective_of_localizedModuleMap_surjective
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (g : R)
    (hf : Function.Surjective (LocalizedModule.map (Submonoid.powers g) f.toLinearMap)) :
    Function.Surjective (Localization.awayMap f.toRingHom (algebraMap R A g)) := by
  let S := Submonoid.powers g
  let A' := Localization.Away (algebraMap R A g)
  let B' := Localization.Away (f (algebraMap R A g))
  let : IsLocalization (Algebra.algebraMapSubmonoid B S) B' := by
    dsimp [S, B']
    rw [f.commutes]
    infer_instance
  let a := (IsScalarTower.toAlgHom R A A').toLinearMap
  let b := (IsScalarTower.toAlgHom R B B').toLinearMap
  let F := IsLocalization.Away.mapₐ A' B' f (algebraMap R A g)
  have he : F.toLinearMap = IsLocalizedModule.map S a b f.toLinearMap := by
    apply IsLocalizedModule.linearMap_ext S a b
    rw [IsLocalizedModule.map_comp]
    ext x
    exact IsLocalization.map_eq _ _ _ x
  change Function.Surjective F
  intro y
  obtain ⟨x, hx⟩ := hf ((IsLocalizedModule.iso S b).symm y)
  refine ⟨IsLocalizedModule.iso S a x, ?_⟩
  change F.toLinearMap (IsLocalizedModule.iso S a x) = y
  rw [he]
  have hc := LinearMap.congr_fun (IsLocalizedModule.map_iso_commute S a b f.toLinearMap) x
  change IsLocalizedModule.map S a b f.toLinearMap (IsLocalizedModule.iso S a x) =
    IsLocalizedModule.iso S b (LocalizedModule.map S f.toLinearMap x) at hc
  rw [hc, hx, LinearEquiv.apply_symm_apply]

/-- 一般点で p 冪倍が像に入る有限代数の射は、一つの分母と p の反転で全射。 -/
theorem exists_away_mul_surjective
    {R A B A' B' : Type u} [CommRing R] [CommRing A] [CommRing B]
    [CommRing A'] [CommRing B'] [Algebra R A] [Algebra R B]
    [Algebra R A'] [Algebra R B'] [Module.Finite R B]
    (S : Submonoid R) (p : ℕ) (a : A →ₐ[R] A') (b : B →ₐ[R] B')
    [IsLocalizedModule S a.toLinearMap] [IsLocalizedModule S b.toLinearMap]
    (f : A →ₐ[R] B) (f' : A' →ₐ[R] B') (hcomm : f'.comp a = b.comp f)
    (hp : ∀ y : B', ∃ x : A', ∃ n : ℕ, f' x = (p : B') ^ n * y) :
    ∃ g : S, Function.Surjective
      (Localization.awayMap f.toRingHom (algebraMap R A g * p)) := by
  have hpower : ∀ y : B', ∃ x : A', ∃ n : ℕ, f'.toLinearMap x = (p : R) ^ n • y := by
    simpa only [Algebra.smul_def, map_pow, map_natCast] using hp
  obtain ⟨g, hg⟩ := exists_away_mul_surjective_of_localized_power_surjective S (p : R)
    a.toLinearMap b.toLinearMap f.toLinearMap f'.toLinearMap
    (congrArg AlgHom.toLinearMap hcomm) hpower
  refine ⟨g, ?_⟩
  have h := awayMap_surjective_of_localizedModuleMap_surjective f ((g : R) * p) hg
  simpa only [map_mul, map_natCast] using h

/-- 一般点で p 冪倍が像に入る有限代数の単射は、一つの主開集合で p 反転後に同型。 -/
theorem exists_away_invertPrimeMap_bijective
    {R A B A' B' : Type u} [CommRing R] [CommRing A] [CommRing B]
    [CommRing A'] [CommRing B'] [Algebra R A] [Algebra R B]
    [Algebra R A'] [Algebra R B'] [Module.Finite R B]
    (S : Submonoid R) (p : ℕ) (a : A →ₐ[R] A') (b : B →ₐ[R] B')
    [IsLocalizedModule S a.toLinearMap] [IsLocalizedModule S b.toLinearMap]
    (f : A →ₐ[R] B) (f' : A' →ₐ[R] B') (hcomm : f'.comp a = b.comp f)
    (hi : Function.Injective f)
    (hp : ∀ y : B', ∃ x : A', ∃ n : ℕ, f' x = (p : B') ^ n * y) :
    ∃ g : S, Function.Bijective
      (invertPrimeMap p (Localization.awayMap f.toRingHom (algebraMap R A g))) := by
  obtain ⟨g, hg⟩ := exists_away_mul_surjective S p a b f f' hcomm hp
  exact ⟨g, invertPrimeMap_awayMap_bijective p f.toRingHom (algebraMap R A g) hi hg⟩

end SerrePositivity.CommutativeAlgebra
