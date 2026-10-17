module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# André E1・E2：冪零核を持つ商に沿う忠実平坦性

## 概要

平坦な環射の可換四角形で、基底の商射が全射かつ核の各元が冪零なら、
商側の忠実平坦性から元の環射の忠実平坦性が従う。
BS Rem 7.15（著者版 p.62）の ϖ 冪剰余の忠実性への一般環計算。

## 方針

全ての素イデアルが冪零核を含むため基底商から持ち上がり、
商側の忠実平坦性によるスペクトル全射性を可換四角形で戻す。

## 規約

核に一様な冪零指数を要求しない。完備性・Noether 性も不要。

## 使われ方

主元の冪による剰余の忠実平坦性を、第一剰余から得る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre

/-- 概要：平坦な可換四角形の基底商が冪零核の全射なら、下辺の忠実平坦性は上辺へ戻る。
方針：素スペクトルの全射性を冪零核の基底商と下辺に沿って合成する。
規約：右辺の射は全射でなくてもよい。
使われ方：BS Rem 7.15（著者版 p.62）の主冪剰余の忠実性。 -/
theorem faithfullyFlat_of_flat_of_nilpotent_square
    {R S B C : Type u} [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra B C] [Module.Flat R S] [Module.FaithfullyFlat B C]
    (qR : R →+* B) (qS : S →+* C) (hqR : Function.Surjective qR)
    (hnil : ∀ x ∈ RingHom.ker qR, IsNilpotent x)
    (hsq : qS.comp (algebraMap R S) = (algebraMap B C).comp qR) :
    Module.FaithfullyFlat R S := by
  apply Module.FaithfullyFlat.of_comap_surjective
  intro P
  have hker : RingHom.ker qR ≤ P.asIdeal := by
    intro x hx
    obtain ⟨n, hn⟩ := hnil x hx
    exact P.isPrime.mem_of_pow_mem n (hn.symm ▸ P.asIdeal.zero_mem)
  have hP : P ∈ Set.range (PrimeSpectrum.comap qR) := by
    rw [range_comap_of_surjective B qR hqR]
    exact hker
  obtain ⟨P', hP'⟩ := hP
  obtain ⟨Q', hQ'⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := B) (B := C) P'
  refine ⟨PrimeSpectrum.comap qS Q', ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply, hsq, PrimeSpectrum.comap_comp_apply, hQ', hP']

end SerrePositivity.BhattScholze.Andre
