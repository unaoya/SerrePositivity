module

public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.PowerTorsion
public import SerrePositivity.HomologicalAlgebra.RestrictedBaseChangeComplex
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Frobenius の主元剰余の忠実平坦性

## 概要
x 完全平坦な Frobenius は R/(x) から R/(x^p) への忠実平坦な射を与える。

## 方針
完全平坦性から通常商の平坦性を取り出し、素イデアルの p 乗の判定で忠実性を得る。

## 規約
BS 著者版 Construction 6.1 の式 (6)。Frobenius は p 乗として指定する。

## 使われ方
D77 の完全平坦性入力から結晶被覆の剰余への帰着。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity

open CategoryTheory

variable {R S : Type u} [CommRing R] [CommRing S]

/-- 概要：通常の平坦な環射は任意のイデアルについて完全平坦。
方針：平坦な係数環との高次 Tor は消える。
規約：制限スカラー加群に対する既存の完全平坦性を使う。
使われ方：BS 著者版 Construction 6.1 の原典の仮定から D77 の入力を得る。 -/
theorem RingHom.completelyFlat_scalarModule_of_flat (f : R →+* S) (hf : f.Flat)
    (I : Ideal R) : IsCompletelyFlat I (baseChangeScalarModule f) := by
  letI := f.toAlgebra
  letI : Module.Flat R S := hf
  let e : baseChangeScalarModule f ≃ₗ[R] S :=
    { AddEquiv.refl S with map_smul' := fun _ _ => rfl }
  have hS : IsCompletelyFlat I S := by
    intro N _ _ hN
    apply (isConcentratedInDegreeZero_derivedTensor_iff S N).mpr
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact torModule_subsingleton_of_flat S N k
  exact isCompletelyFlat_of_linearEquiv I e.symm hS

/-- 概要：完全平坦な環射の通常のイデアル商は平坦。
方針：制限スカラー加群の完全平坦性を標準代数構造へ移して、既存の剰余判定を使う。
規約：始域のイデアルを像で割った通常の環射。
使われ方：BS 著者版 Construction 6.1 の Frobenius 剰余。 -/
theorem RingHom.quotientMap_flat_of_completelyFlat (f : R →+* S) (I : Ideal R)
    (h : IsCompletelyFlat I (baseChangeScalarModule f)) :
    (Ideal.quotientMap (I := I) (I.map f) f Ideal.le_comap_map).Flat := by
  letI := f.toAlgebra
  let e : baseChangeScalarModule f ≃ₗ[R] S :=
    { AddEquiv.refl S with map_smul' := fun _ _ => rfl }
  have hS : IsCompletelyFlat I S := isCompletelyFlat_of_linearEquiv I e h
  letI := adicQuotientAlgebra I S
  have hq : (algebraMap (R ⧸ I) (S ⧸ I.map f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (flat_algebraQuotient_of_completelyFlat I S hS)
  exact hq

namespace Frobenius

variable {p : ℕ} [Fact p.Prime] (F : R →+* R) (hF : ∀ a, F a = a ^ p) (x : R)

/-- 概要：p 乗射が誘導する x と x^p の商の間の環射。
方針：F(x)=x^p を商への降下条件に使う。
規約：BS 著者版 Construction 6.1 の式 (6) の中央の射。
使われ方：剰余の忠実平坦性と被覆の分解。 -/
@[expose] def principalQuotientMap : (R ⧸ Ideal.span {x}) →+* R ⧸ Ideal.span {x ^ p} :=
  Ideal.quotientMap (I := Ideal.span {x}) (Ideal.span {x ^ p}) F (by
    rw [Ideal.span_le]
    intro a ha
    have ha' : a = x := Set.mem_singleton_iff.mp ha
    subst a
    change F x ∈ Ideal.span {x ^ p}
    rw [hF]
    exact Ideal.mem_span_singleton_self _)

/-- 商への標準射上での Frobenius 剰余の値。 -/
@[simp] theorem principalQuotientMap_mk (a : R) :
    principalQuotientMap F hF x (Ideal.Quotient.mk (Ideal.span {x}) a) =
      Ideal.Quotient.mk (Ideal.span {x ^ p}) (F a) := rfl

/-- 概要：Frobenius 剰余の素イデアルの逆像写像は全射。
方針：自然な R/(x^p)→R/(x) で素イデアルを引き戻し、p 乗の所属判定を使う。
規約：BS 著者版 Construction 6.1 の忠実性の部分。
使われ方：完全平坦性から完全忠実平坦性を得る。 -/
theorem principalQuotientMap_comap_surjective :
    Function.Surjective (PrimeSpectrum.comap (principalQuotientMap F hF x)) := by
  let g : (R ⧸ Ideal.span {x ^ p}) →+* R ⧸ Ideal.span {x} :=
    Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self x
      (Nat.ne_of_gt (Fact.out : p.Prime).pos)))
  intro P
  refine ⟨P.comap g, ?_⟩
  apply PrimeSpectrum.ext
  ext a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change g (principalQuotientMap F hF x (Ideal.Quotient.mk _ a)) ∈ P.asIdeal ↔
    Ideal.Quotient.mk (Ideal.span {x}) a ∈ P.asIdeal
  rw [principalQuotientMap_mk, hF]
  change (Ideal.Quotient.mk (Ideal.span {x}) (a ^ p)) ∈ P.asIdeal ↔ _
  rw [map_pow]
  exact P.isPrime.pow_mem_iff_mem p (Fact.out : p.Prime).pos

/-- 概要：x 完全平坦な Frobenius は主元剰余の間の忠実平坦な射を与える。
方針：完全平坦性から通常商の平坦性を移し、素イデアルの全射性を加える。
規約：BS 著者版 Construction 6.1 の式 (6) の中央の射。
使われ方：D77 の仮定の下での結晶被覆の保存性と Tor 振幅。 -/
theorem principalQuotientMap_faithfullyFlat
    (hflat : IsCompletelyFlat (Ideal.span {x}) (baseChangeScalarModule F)) :
    (principalQuotientMap F hF x).FaithfullyFlat := by
  let I : Ideal R := Ideal.span {x}
  let q₀ := Ideal.quotientMap (I := I) (I.map F) F Ideal.le_comap_map
  have hI : I.map F = Ideal.span {x ^ p} := by
    rw [Ideal.map_span, Set.image_singleton, hF]
  let e := Ideal.quotEquivOfEq hI
  have hq : principalQuotientMap F hF x = e.toRingHom.comp q₀ := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro a
    exact (Ideal.quotEquivOfEq_mk hI (F a)).symm
  apply RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
  refine ⟨?_, principalQuotientMap_comap_surjective F hF x⟩
  rw [hq]
  exact (RingHom.quotientMap_flat_of_completelyFlat F I hflat).comp
    (RingHom.Flat.of_bijective e.bijective)

end Frobenius
end SerrePositivity
