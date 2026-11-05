module

public import SerrePositivity.CommutativeAlgebra.UniversalHomeomorphism.Basic
public import Mathlib.RingTheory.Localization.Ideal

/-!
# 被約化の射と局所化

## 概要
被約化で誘導される射を定義し、普遍同相と局所化との両立を示す。

## 方針
nilradical の像を調べ、商の普遍性と局所化の商に関する補題を使う。

## 規約
被約化は nilradical による商。

## 使われ方
層の被約構造と全商環上の分解の接続。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

/-- 環の射が被約化に誘導する射。 -/
def reductionMap {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    A ⧸ nilradical A →+* B ⧸ nilradical B :=
  Ideal.quotientMap (nilradical B) f (fun _ hx ↦
    mem_nilradical.mpr ((mem_nilradical.mp hx).map f))

@[simp]
theorem reductionMap_mk {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (x : A) :
    reductionMap f (Ideal.Quotient.mk (nilradical A) x) =
      Ideal.Quotient.mk (nilradical B) (f x) := rfl

/-- 核が nil な射の被約化は単射。 -/
theorem reductionMap_injective {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hk : RingHom.ker f ≤ nilradical A) :
    Function.Injective (reductionMap f) := by
  apply (injective_iff_map_eq_zero (reductionMap f)).mpr
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  intro hx
  have hnil : IsNilpotent (f x) :=
    mem_nilradical.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx)
  obtain ⟨n, hn⟩ := hnil
  have hpow : x ^ n ∈ RingHom.ker f := by
    simpa only [RingHom.mem_ker, map_pow] using hn
  obtain ⟨m, hm⟩ := mem_nilradical.mp (hk hpow)
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact mem_nilradical.mpr ⟨n * m, by simpa only [pow_mul] using hm⟩

/-- 普遍同相は両環の被約化後にも普遍同相。 -/
theorem isUniversalHomeomorphism_reductionMap {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : IsUniversalHomeomorphism f) :
    IsUniversalHomeomorphism (reductionMap f) := by
  have hq : IsUniversalHomeomorphism (Ideal.Quotient.mk (nilradical B)) :=
    isUniversalHomeomorphism_of_nil_kernel _ Ideal.Quotient.mk_surjective (by simp)
  have hc := isUniversalHomeomorphism_comp f _ hf hq
  have he : (Ideal.Quotient.mk (nilradical B)).comp f =
      (reductionMap f).comp (Ideal.Quotient.mk (nilradical A)) := by ext; rfl
  rw [he] at hc
  apply isUniversalHomeomorphism_tower_top _ _ hc
  apply reductionMap_injective
  exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).mp hf.surjective_spec.denseRange

/-- 被約化と局所化は両立する。 -/
theorem isLocalization_reduction (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] :
    letI : Algebra (A ⧸ nilradical A) (B ⧸ nilradical B) :=
      (reductionMap (algebraMap A B)).toAlgebra
    IsLocalization (M.map (Ideal.Quotient.mk (nilradical A))) (B ⧸ nilradical B) := by
  let : Algebra (A ⧸ nilradical A) (B ⧸ nilradical B) :=
    (reductionMap (algebraMap A B)).toAlgebra
  have hn : (nilradical A).map (algebraMap A B) = nilradical B := by
    change (⊥ : Ideal A).radical.map (algebraMap A B) = (⊥ : Ideal B).radical
    simpa only [Ideal.map_bot] using IsLocalization.map_radical M B (⊥ : Ideal A)
  apply IsLocalization.of_surjective M B
    (Ideal.Quotient.mk (nilradical A)) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (nilradical B)) Ideal.Quotient.mk_surjective
  · ext; rfl
  · simpa only [Ideal.mk_ker] using hn.ge

end SerrePositivity.CommutativeAlgebra
