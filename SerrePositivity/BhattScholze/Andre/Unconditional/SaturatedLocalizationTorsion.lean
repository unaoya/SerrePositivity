module

public import SerrePositivity.BhattScholze.Andre.Unconditional.SourceUnitDenominator
public import SerrePositivity.BhattScholze.Andre.Unconditional.CompletionTorsionDetection
public import SerrePositivity.HomologicalAlgebra.DerivedScalarConeBaseChange

/-!
# 安定局所化の核と mod p の分母冪ねじれ

## 概要
BS Rem 7.15（著者版 p.62）の局所化側の消滅を、元の p 錐の分母冪ねじれへ移す。

## 方針
通常局所化の核判定と平坦導来ホモロジー比較を使う。
mod p で安定分母の像は元の分母の冪集合に等しい。

## 規約
指数は各元ごとに異なってよい。対象の完備性や有界ねじれは不要。

## 使われ方
元の raw 源の p 錐の完備化純性と合流する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard

/-- 概要：局所化後に零の通常加群では、各元が一つの分母で零になる。
方針：標準係数拡大を加群局所化へ比較し、その核判定を使う。
規約：分母集合は任意の乗法集合。
使われ方：BS Rem 7.15（著者版 p.62）の局所化側の実ホモロジー。 -/
theorem unconditionalModule_submonoid_torsion_of_localization_isZero
    {R : Type u} [CommRing R] (T : Submonoid R)
    (B : Type u) [CommRing B] [Algebra R B] [IsLocalization T B]
    (M : ModuleCat.{u} R)
    (h : IsZero ((ModuleCat.extendScalars (algebraMap R B)).obj M)) (x : M) :
    ∃ s : T, (s : R) • x = 0 := by
  have hz : TensorProduct.mk R B M 1 x = 0 := by
    let e := extendScalarsObjEquivTensor R B M
    have := ModuleCat.isZero_iff_subsingleton.mp h
    have hs : Subsingleton (TensorProduct R B M) := e.symm.injective.subsingleton
    exact hs.elim _ _
  exact (IsLocalizedModule.eq_zero_iff T (TensorProduct.mk R B M 1)).mp hz

/-- 概要：実導来局所化後のホモロジー消滅は、元の各元を一つの分母で零にする。
方針：平坦導来係数拡大の実ホモロジー比較を通常の局所化核判定へ渡す。
規約：元の上に有界な実導来対象を用いる。
使われ方：BS Rem 7.15（著者版 p.62）の元の raw 源の局所化核。 -/
theorem unconditionalHomology_submonoid_torsion_of_localization_isZero
    {R : Type u} [CommRing R] (T : Submonoid R)
    (B : Type u) [CommRing B] [Algebra R B] [IsLocalization T B]
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat B) i).obj
      ((boundedAboveDerivedBaseChange (algebraMap R B)).obj X).obj))
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj) :
    ∃ s : T, (s : R) • x = 0 := by
  let hφ : (algebraMap R B).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B T)
  let e := (DerivedCategory.homologyFunctor (ModuleCat B) i).mapIso
      ((boundedAboveFlatDerivedBaseChangeIso (algebraMap R B) hφ).app X) ≪≫
    (flatDerivedBaseChangeHomologyNatIso (algebraMap R B) hφ i).app X.obj
  exact unconditionalModule_submonoid_torsion_of_localization_isZero T B _
    (h.of_iso e.symm) x

/-- 概要：p で零になる加群では、安定分母で零になる各元は元の分母の冪で零になる。
方針：安定分母の mod p 像を冪集合へ同定し、差が p の倍であることを使う。
規約：係数環の p 正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の元の実 p 錐の分母冪ねじれ。 -/
theorem unconditionalSaturatedTorsion_power_torsion_mod_prime
    {p : ℕ} [Fact p.Prime] {A R : Type u} [CommRing A] [CommRing R]
    (D : DeltaStructure p A) (d : A) (c : A →+* R)
    (M : ModuleCat.{u} R) (hp : ∀ x : M, (p : R) • x = 0) (x : M)
    (ht : ∃ s : (D.frobeniusDenominators (Submonoid.powers d)).map c.toMonoidHom,
      (s : R) • x = 0) : ∃ n : ℕ, (c d) ^ n • x = 0 := by
  obtain ⟨s, hs⟩ := ht
  obtain ⟨r, hr, hrs⟩ := s.property
  change c r = (s : R) at hrs
  rw [← hrs] at hs
  let q := Ideal.Quotient.mk (Ideal.span {(p : R)})
  have hpc : (q.comp c) (p : A) = 0 := by
    rw [RingHom.comp_apply, map_natCast]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hm : q (c r) ∈ Submonoid.powers (q (c d)) := by
    change (q.comp c) r ∈ Submonoid.powers ((q.comp c) d)
    rw [← unconditionalFrobeniusDenominators_map_mod_prime D d (q.comp c) hpc]
    exact ⟨r, hr, rfl⟩
  obtain ⟨n, hn⟩ := hm
  change (q (c d)) ^ n = q (c r) at hn
  have hdiff : (c d) ^ n - c r ∈ Ideal.span {(p : R)} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q ((c d) ^ n - c r) = 0
    rw [map_sub, map_pow, hn, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hdiff
  have hz : ((c d) ^ n - c r) • x = 0 := by
    rw [ht, mul_smul, smul_comm (p : R) t x, hp x, smul_zero]
  exact ⟨n, by simpa only [sub_smul, hs, sub_zero] using hz⟩

/-- 概要：実 p 錐が安定局所化後の指定次数で消えるなら、元の各元は分母冪ねじれ。
方針：局所化核と p 錐の p 零化を合成する。
規約：元の上に有界な実対象と標準係数射を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の具体的源の局所化検出。 -/
theorem unconditionalSaturatedScalarCone_homology_power_torsion
    {p : ℕ} [Fact p.Prime] {A R : Type u} [CommRing A] [CommRing R]
    (D : DeltaStructure p A) (d : A) (c : A →+* R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (B : Type u) [CommRing B] [Algebra R B]
    [IsLocalization ((D.frobeniusDenominators (Submonoid.powers d)).map c.toMonoidHom) B]
    (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat B) i).obj
      ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
        ((boundedAboveDerivedScalarCone R (p : R)).obj X)).obj))
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((derivedScalarConeFunctor R (p : R)).obj X.obj)) :
    ∃ n : ℕ, (c d) ^ n • x = 0 := by
  let Y := (boundedAboveDerivedScalarCone R (p : R)).obj X
  have ht := unconditionalHomology_submonoid_torsion_of_localization_isZero
    ((D.frobeniusDenominators (Submonoid.powers d)).map c.toMonoidHom) B Y i h x
  exact unconditionalSaturatedTorsion_power_torsion_mod_prime D d c
    ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj Y.obj)
    (derivedScalarCone_homology_annihilated R (p : R) X.obj i) x ht

end SerrePositivity.BhattScholze.Andre
