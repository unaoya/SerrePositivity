module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.RingTheory.Valuation.ValuationRing

/-! # 主開集合の外で同型な整写像から整閉整域への一意延長

付値環に限らず任意の整閉整域を終域としてよい。
主開集合を定める元の像が零でないとき、元の環写像は一意に延長する。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 整写像 R→S が g の外で同型なら、g を零にしない整閉整域への写像は一意に S へ延長する。
終域の付値・rank・完備性や、R→S の有限性・単射性は要求しない。 -/
theorem existsUnique_extension_of_integral_away_bijective
    (R : Type u) (S : Type v) (V : Type w)
    [CommRing R] [CommRing S] [CommRing V] [IsDomain V] [IsIntegrallyClosed V]
    [Algebra R S] [Algebra R V] [Algebra.IsIntegral R S]
    (g : R) (hg : algebraMap R V g ≠ 0)
    (hiso : Function.Bijective (Localization.awayMap (algebraMap R S) g)) :
    ∃! l : S →+* V, l.comp (algebraMap R S) = algebraMap R V := by
  let K := FractionRing V
  have hgK : algebraMap R K g ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R V K]
    exact fun h => hg ((IsFractionRing.injective V K) (h.trans (map_zero _).symm))
  let a : Localization.Away g →ₐ[R] K :=
    IsLocalization.Away.liftAlgHom g (f := Algebra.ofId R K) (isUnit_iff_ne_zero.mpr hgK)
  letI : IsLocalization.Away ((Algebra.ofId R S) g)
      (Localization.Away (algebraMap R S g)) := by
    change IsLocalization.Away (algebraMap R S g) (Localization.Away (algebraMap R S g))
    infer_instance
  let e := AlgEquiv.ofBijective
    (IsLocalization.Away.mapₐ (Localization.Away g)
      (Localization.Away (algebraMap R S g)) (Algebra.ofId R S) g) hiso
  let k : S →ₐ[R] K := a.comp (e.symm.toAlgHom.comp
    (IsScalarTower.toAlgHom R S (Localization.Away (algebraMap R S g))))
  let v : V →ₐ[R] K := IsScalarTower.toAlgHom R V K
  have hmem (s : S) : k s ∈ v.range := by
    have hi : IsIntegral V (k s) :=
      (IsIntegral.map k (Algebra.IsIntegral.isIntegral (R := R) s)).tower_top
    exact IsIntegrallyClosed.isIntegral_iff.mp hi
  let ev := AlgEquiv.ofInjective v (IsFractionRing.injective V K)
  let l : S →ₐ[R] V := ev.symm.toAlgHom.comp (k.codRestrict v.range hmem)
  refine ⟨l.toRingHom, l.comp_algebraMap, ?_⟩
  intro m hm
  have hm' (r : R) : m (algebraMap R S r) = algebraMap R V r := RingHom.congr_fun hm r
  apply RingHom.ext
  intro s
  obtain ⟨r, n, hr⟩ := Localization.awayMap_surjective_iff.mp hiso.2 s
  have h1 := congrArg m hr
  have h2 := congrArg l hr
  simp only [map_mul, map_pow, hm'] at h1
  simp only [map_mul, map_pow, l.commutes] at h2
  exact mul_left_cancel₀ (pow_ne_zero n hg) (h1.symm.trans h2)

/-- 同じ一意延長を任意の付値環に適用する。離散性・rank 1・p 完備性は要求しないので、
原典の p 完備 rank 1 付値環条件にもそのまま適用できる。 -/
theorem existsUnique_valuation_extension_of_integral_away_bijective
    (R : Type u) (S : Type v) (V : Type w)
    [CommRing R] [CommRing S] [CommRing V] [IsDomain V] [ValuationRing V]
    [Algebra R S] [Algebra R V] [Algebra.IsIntegral R S]
    (g : R) (hg : algebraMap R V g ≠ 0)
    (hiso : Function.Bijective (Localization.awayMap (algebraMap R S) g)) :
    ∃! l : S →+* V, l.comp (algebraMap R S) = algebraMap R V := by
  letI : IsIntegrallyClosed V := (ValuationRing.integers V (FractionRing V)).isIntegrallyClosed
  exact existsUnique_extension_of_integral_away_bijective R S V g hg hiso

end SerrePositivity
