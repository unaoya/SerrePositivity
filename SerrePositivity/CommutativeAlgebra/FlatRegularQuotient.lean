module

public import Mathlib.RingTheory.Regular.Flat
public import SerrePositivity.CommutativeAlgebra.Adic.Principal

/-! # 平坦基底変更によるmod aの正則性の移送 -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open scoped Pointwise
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

/-- aとmod aで正則なgは平坦基底変更後も同じ正則性を持つ。 -/
theorem isSMulRegular_mod_of_flat (a g : R) (ha : IsSMulRegular R a)
    (hg : IsSMulRegular (R ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) g)) :
    IsSMulRegular (S ⧸ Ideal.span {algebraMap R S a})
      (Ideal.Quotient.mk (Ideal.span {algebraMap R S a}) (algebraMap R S g)) := by
  open RingTheory.Sequence in
  have hpair : IsWeaklyRegular R [a, g] := by
    rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
    refine ⟨ha, ?_⟩
    have htop : a • (⊤ : Submodule R R) = Ideal.span {a} := by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
    have hh : IsSMulRegular (R ⧸ Ideal.span {a}) g :=
      (isSMulRegular_algebraMap_iff (R := R) (A := R ⧸ Ideal.span {a})).mp hg
    let e := Submodule.quotEquivOfEq (a • (⊤ : Submodule R R)) (Ideal.span {a}) htop
    exact (e.isSMulRegular_congr g).mpr hh
  have hpairS : RingTheory.Sequence.IsWeaklyRegular S
      [algebraMap R S a, algebraMap R S g] := by
    simpa using hpair.of_flat (S := S)
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hpairS
  have htop : algebraMap R S a • (⊤ : Submodule S S) =
      Ideal.span {algebraMap R S a} := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  have hh : IsSMulRegular (S ⧸ Ideal.span {algebraMap R S a}) (algebraMap R S g) := by
    let e := Submodule.quotEquivOfEq
      (algebraMap R S a • (⊤ : Submodule S S)) (Ideal.span {algebraMap R S a}) htop
    exact (e.isSMulRegular_congr (algebraMap R S g)).mp hpairS.2
  exact (isSMulRegular_algebraMap_iff (R := S)
    (A := S ⧸ Ideal.span {algebraMap R S a})).mpr hh

end SerrePositivity
