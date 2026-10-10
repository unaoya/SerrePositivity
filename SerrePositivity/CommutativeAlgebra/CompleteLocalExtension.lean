module

public import SerrePositivity.CommutativeAlgebra.AdicCompleteness
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# 完備局所環の有限整域拡大

## 概要

完備ネーター局所環上の有限な整域が局所環であることを示す。
有限加群の完備性と Hensel の補題で、閉ファイバーの冪等元を持ち上げる。
整域の冪等元は零か一なので、Artin 環である閉ファイバーには極大イデアルが一つしかない。
さらに、基底の剰余体が代数閉なら有限な局所拡大で剰余体は変わらない。

## 使われ方

§5 のガロア閉包内の整閉包について、有限性を得た後の局所性・完備性・剰余体を供給する。
正則性、正規性、長さ代数、K 理論の引用には依存しない。
-/

public section

namespace SerrePositivity

open IsLocalRing Polynomial

/-- Hensel 環では商の冪等元が持ち上がる。
多項式 `X² - X` の微分は冪等元の上で単元となるため、単根の持ち上げを適用できる。 -/
theorem exists_idempotent_lift_of_henselian
    {S : Type*} [CommRing S] (I : Ideal S) [HenselianRing S I]
    (x : S ⧸ I) (hx : IsIdempotentElem x) :
    ∃ y : S, IsIdempotentElem y ∧ Ideal.Quotient.mk I y = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk I a * Ideal.Quotient.mk I a = Ideal.Quotient.mk I a at hx
  have ha : a ^ 2 - a ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_sub, map_pow, sub_eq_zero, pow_two, map_mul] using hx
  have hu : IsUnit (2 * Ideal.Quotient.mk I a - 1) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨2 * Ideal.Quotient.mk I a - 1, ?_⟩
    calc
      (2 * Ideal.Quotient.mk I a - 1) * (2 * Ideal.Quotient.mk I a - 1) =
          4 * (Ideal.Quotient.mk I a * Ideal.Quotient.mk I a - Ideal.Quotient.mk I a) + 1 := by ring
      _ = 1 := by rw [hx]; ring
  obtain ⟨y, hy, hya⟩ := HenselianRing.is_henselian
    (R := S) (I := I) (X ^ 2 - X)
    (monic_X_pow_sub (degree_X_le.trans_lt (by decide))) a
    (by simpa using ha) (by simpa [one_add_one_eq_two, map_ofNat] using hu)
  refine ⟨y, ?_, ?_⟩
  · change y * y = y
    simpa [Polynomial.IsRoot, pow_two, sub_eq_zero] using hy
  · exact Ideal.Quotient.eq.mpr hya

/-- 非自明な Artin 環で冪等元が零と一だけなら、その環は局所環である。
異なる極大イデアルを分離する冪等元の存在を使う。 -/
theorem isLocalRing_of_artinian_of_idempotents
    (S : Type*) [CommRing S] [Nontrivial S] [IsArtinianRing S]
    (h : ∀ x : S, IsIdempotentElem x → x = 0 ∨ x = 1) : IsLocalRing S := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  let := hm
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨m, hm, fun n hn ↦ ?_⟩
  by_contra hnm
  obtain ⟨x, hxm, hx, hxn⟩ := IsArtinianRing.exists_notMem_forall_mem_of_ne m
  rcases h x hx with rfl | rfl
  · exact hxm (m.zero_mem)
  · exact hn.ne_top (Ideal.eq_top_of_isUnit_mem n (hxn n hn.isPrime hnm) isUnit_one)

/-- 完備ネーター局所環上の有限な整域は局所環である。
閉ファイバーの Artin 性と Hensel の冪等元持ち上げから、まず閉ファイバーの局所性を得る。
完備性によりその商写像は局所準同型なので、元の環も局所となる。 -/
theorem isLocalRing_finite_domain_of_complete
    (R S : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] : IsLocalRing S := by
  let I := (maximalIdeal R).map (algebraMap R S)
  let : IsAdicComplete (maximalIdeal R) S := isAdicComplete_finite S
  let : IsAdicComplete I S := (IsAdicComplete.map_algebraMap_iff _ _).mpr inferInstance
  have hI : I ≠ ⊤ := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal S
    let := hm
    have hc : m.comap (algebraMap R S) = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap R S)
          (fun x ↦ Algebra.IsIntegral.isIntegral x) m)
    have hi : I ≤ m := Ideal.map_le_iff_le_comap.mpr hc.ge
    exact ne_top_of_le_ne_top hm.ne_top hi
  let : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  let : Algebra (ResidueField R) (S ⧸ I) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map : maximalIdeal R ≤
      I.comap (algebraMap R S))
  let : IsScalarTower R (ResidueField R) (S ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Module.Finite (ResidueField R) (S ⧸ I) :=
    Module.Finite.of_restrictScalars_finite R _ _
  let : IsArtinianRing (S ⧸ I) := IsArtinianRing.of_finite (ResidueField R) (S ⧸ I)
  let : IsLocalRing (S ⧸ I) := isLocalRing_of_artinian_of_idempotents (S ⧸ I) (by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := exists_idempotent_lift_of_henselian I x hx
    have hy' : y = 0 ∨ y = 1 := by
      have hmul : y * (y - 1) = 0 := by
        rw [mul_sub, mul_one, hy, sub_self]
      exact (mul_eq_zero.mp hmul).imp id sub_eq_zero.mp
    rcases hy' with rfl | rfl
    · exact Or.inl (map_zero _)
    · exact Or.inr (map_one _))
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
  exact (Ideal.Quotient.mk I).domain_isLocalRing

/-- 有限な局所環拡大で、基底の剰余体が代数閉なら剰余写像の合成は全射。
剰余体拡大の有限性と、代数閉体が非自明な代数拡大を持たないことを使う。 -/
theorem residue_surjective_of_finite_of_isAlgClosed
    (R S : Type*) [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Finite R S]
    [IsAlgClosed (ResidueField R)] :
    Function.Surjective ((residue S).comp (algebraMap R S)) := by
  let : IsLocalHom (algebraMap R S) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R S)).out 5 1).mp
      (IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap R S)
          (fun x ↦ Algebra.IsIntegral.isIntegral x) (maximalIdeal S)))
  intro x
  obtain ⟨y, rfl⟩ :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral
      (k := ResidueField R) (K := ResidueField S)).surjective x
  obtain ⟨r, rfl⟩ := residue_surjective y
  exact ⟨r, rfl⟩

end SerrePositivity
