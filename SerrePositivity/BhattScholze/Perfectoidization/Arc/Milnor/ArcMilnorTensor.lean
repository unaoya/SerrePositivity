module

public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Valuations.ArcValuationMilnor
public import SerrePositivity.CommutativeAlgebra.PerfectTorIndependence.Basic
public import SerrePositivity.HomologicalAlgebra.TorLES
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
## 概要
完全代数を係数とした付値環の Milnor 短完全列（BS17 Lemma 6.3）。
## 方針
既存の Milnor 列を加群の列にし、Tor₁ の消滅とテンソルの右完全性を使う。
## 規約
係数側は p が零の完全代数とし、零環も許す。
## 使われ方
BM18 Lemma 4.4 の、完全環上の構造層での適用。
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

set_option backward.isDefEq.respectTransparency false

/-- Tor₁ の消滅により、短完全列のテンソル積は左端でも完全になる。 -/
theorem shortExact_tensorLeft_of_tor {V : Type u} [CommRing V] (M : Type u)
    [AddCommGroup M] [Module V M] (S : ShortComplex (ModuleCat.{u} V)) (hS : S.ShortExact)
    (hTor : Subsingleton (TorModule V 1 M S.X₃)) :
    (S.map (tensorLeft (ModuleCat.of V M))).ShortExact := by
  let F := tensorLeft (ModuleCat.of V M)
  have hf : Function.Injective S.f := (ModuleCat.mono_iff_injective _).mp hS.mono_f
  have hg : Function.Surjective S.g := (ModuleCat.epi_iff_surjective _).mp hS.epi_g
  have he : Function.Exact S.f S.g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact
  have h := LeftDerivedLES.exact_δα F S.f.hom S.g.hom hf hg he 0
  rw [LeftDerivedLES.α_eq_map] at h
  let I := (F.leftDerived 0).map (ModuleCat.ofHom S.f.hom)
  have hker (x : (F.leftDerived 0).obj (ModuleCat.of V S.X₁)) : I x = 0 → x = 0 := by
    intro hx
    obtain ⟨y, hy⟩ := (h x).mp hx
    have hy0 : y = 0 := hTor.elim _ _
    rw [hy0, map_zero] at hy
    exact hy.symm
  have hinj : Function.Injective I := by
    intro x y heq
    apply sub_eq_zero.mp
    apply hker
    change I.hom (x - y) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr heq
  have hmono : Mono I := (ModuleCat.mono_iff_injective _).mpr hinj
  have hmap : Mono (F.map S.f) := by
    let e := F.leftDerivedZeroIsoSelf
    exact mono_of_mono_fac (e.inv.naturality S.f)
  apply ModuleCat.shortComplex_shortExact
  · exact lTensor_exact M he hg
  · exact (ModuleCat.mono_iff_injective _).mp hmap
  · exact LinearMap.lTensor_surjective M hg

variable {V : Type u} [CommRing V]
variable (P : Ideal V) [P.IsPrime]

/-- Milnor 列の前半の V 線形写像（BS17 Lemma 6.3）。 -/
def milnorInclusion : V →ₗ[V] Localization.AtPrime P × (V ⧸ P) :=
  (Algebra.linearMap V (Localization.AtPrime P)).prod (Algebra.linearMap V (V ⧸ P))

/-- Milnor 列の後半の V 線形写像は二つの剰余の差（BS17 Lemma 6.3）。 -/
def milnorDifference : (Localization.AtPrime P × (V ⧸ P)) →ₗ[V] P.ResidueField :=
  ((IsScalarTower.toAlgHom V (Localization.AtPrime P) P.ResidueField).toLinearMap.comp
    (LinearMap.fst V _ _)) -
  ((IsScalarTower.toAlgHom V (V ⧸ P) P.ResidueField).toLinearMap.comp
    (LinearMap.snd V _ _))

/-- 付値環の Milnor 列を V 加群の短複体として取る（BS17 Lemma 6.3）。 -/
def milnorModuleComplex : ShortComplex (ModuleCat.{u} V) :=
  ShortComplex.moduleCatMk (milnorInclusion P) (milnorDifference P) (by
    apply LinearMap.ext
    intro x
    exact sub_self (algebraMap V P.ResidueField x))

/-- 既存の Milnor 短完全列の加群版（BS17 Lemma 6.3）。 -/
theorem milnorModuleComplex_shortExact [IsDomain V] [ValuationRing V] :
    (milnorModuleComplex P).ShortExact := by
  obtain ⟨hi, he, hs⟩ := valuationRing_milnorSquare P
  exact ModuleCat.shortComplex_shortExact _ he hi hs

/-- 完全標数 p 環の素点の剰余体は完全。 -/
theorem perfectRing_primeResidue (p : ℕ) [Fact p.Prime] [PerfectRing V p]
    (hp : (p : V) = 0) : PerfectRing P.ResidueField p := by
  have hpQ : (p : V ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P), hp, map_zero]
  let : CharP (V ⧸ P) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpQ
  let : PerfectRing (V ⧸ P) p := PerfectRing.ofSurjective _ _ (by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := (PerfectRing.bijective_frobenius (R := V) (p := p)).2 x
    change r ^ p = x at hr
    exact ⟨Ideal.Quotient.mk P r, by
      change (Ideal.Quotient.mk P r) ^ p = _
      rw [← map_pow, hr]⟩)
  have hpK : (p : P.ResidueField) = 0 := by
    rw [← map_natCast (algebraMap V P.ResidueField), hp, map_zero]
  let : CharP P.ResidueField p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpK
  apply PerfectRing.ofSurjective
  intro x
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (V ⧸ P) x
  obtain ⟨r, hr⟩ := (PerfectRing.bijective_frobenius (R := V ⧸ P) (p := p)).2 a
  obtain ⟨s, hs⟩ := (PerfectRing.bijective_frobenius (R := V ⧸ P) (p := p)).2 b
  refine ⟨algebraMap (V ⧸ P) P.ResidueField r / algebraMap (V ⧸ P) P.ResidueField s, ?_⟩
  change r ^ p = a at hr
  change s ^ p = b at hs
  rw [frobenius_def, div_pow, ← map_pow, ← map_pow, hr, hs]

/-- 完全な V 代数とのテンソル積は Milnor 短完全列を保つ
（BM18 Lemma 4.4 の、完全環上の構造層に用いる形）。 -/
theorem milnorModuleComplex_tensor_shortExact
    [IsDomain V] [ValuationRing V] (D : Type u) [CommRing D] [Algebra V D]
    (p : ℕ) [Fact p.Prime] [PerfectRing V p] [PerfectRing D p]
    (hp : (p : V) = 0) :
    ((milnorModuleComplex P).map (tensorLeft (ModuleCat.of V D))).ShortExact := by
  let := perfectRing_primeResidue P p hp
  apply shortExact_tensorLeft_of_tor D _ (milnorModuleComplex_shortExact P)
  exact perfectRing_tor_subsingleton_of_char_eq_zero p V hp D P.ResidueField 1 (by decide)

end SerrePositivity.BhattScholze.Perfectoidization.Derived
