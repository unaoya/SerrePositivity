module

public import SerrePositivity.BhattScholze.Andre.Variants.FaithfullyFlatNilpotentSquare
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatPowerTorsion

/-!
# André E1・E2：代数の主元完全忠実平坦性と正冪

## 概要

a 完全忠実平坦な可換代数は、全ての正冪 aⁿ に関しても完全忠実平坦。
BS Rem 7.15（著者版 p.62）の ϖ から p への移送に用いる。

## 方針

既存の冪ねじれ Tor 消滅から冪剰余の平坦性を得る。
第一剰余への全射の核が各元冪零であることを使い、剰余の忠実性も戻す。

## 規約

主元の正則性・完備性・Noether 性は不要。正冪指数を明示する。

## 使われ方

(ϖ^p)=(p) により自然な Hodge–Tate 候補の p 完全忠実平坦性を得る。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped TensorProduct
attribute [local instance] adicQuotientAlgebra

/-- 概要：a 完全忠実平坦な代数の各正冪剰余は忠実平坦。
方針：冪剰余の平坦性と第一剰余への冪零核の可換四角形を使う。
規約：正則性も完備性も不要。
使われ方：BS Rem 7.15（著者版 p.62）の p 剰余の忠実性。 -/
theorem faithfullyFlat_power_algebraQuotient_of_completelyFaithfullyFlat
    {R : Type u} [CommRing R] (a : R) (S : Type u) [CommRing S] [Algebra R S]
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) S) (n : ℕ) (hn : 0 < n) :
    Module.FaithfullyFlat (R ⧸ Ideal.span {a ^ n})
      (S ⧸ Ideal.map (algebraMap R S) (Ideal.span {a ^ n})) := by
  let I : Ideal R := Ideal.span {a}
  let In : Ideal R := Ideal.span {a ^ n}
  let c := algebraMap R S
  let J := Ideal.map c I
  let Jn := Ideal.map c In
  have hle : In ≤ I := Ideal.span_le.mpr (by
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Ideal.mem_span_singleton.mpr (dvd_pow_self a (Nat.ne_of_gt hn)))
  let qR : (R ⧸ In) →+* R ⧸ I := Ideal.Quotient.factor hle
  let qS : (S ⧸ Jn) →+* S ⧸ J := Ideal.Quotient.factor (Ideal.map_mono hle)
  let : Module.Flat (R ⧸ In) (S ⧸ Jn) :=
    flat_power_algebraQuotient_of_completelyFlat a S hS.1 n
  let : Module.FaithfullyFlat (R ⧸ I) ((R ⧸ I) ⊗[R] S) := hS.2
  let : Module.FaithfullyFlat (R ⧸ I) (S ⧸ J) :=
    Module.FaithfullyFlat.of_linearEquiv (R ⧸ I) ((R ⧸ I) ⊗[R] S)
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv
  apply faithfullyFlat_of_flat_of_nilpotent_square qR qS (Ideal.Quotient.factor_surjective hle)
  · intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hr : r ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hx
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hr
    refine ⟨n, ?_⟩
    rw [← map_pow]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hz, mul_pow]
    exact Ideal.mem_span_singleton.mpr ⟨z ^ n, rfl⟩
  · apply Ideal.Quotient.ringHom_ext
    ext r
    rfl

/-- 概要：主元完全忠実平坦性は全ての正冪に保存される。
方針：既存の完全平坦性の冪保存と、環商の忠実平坦性を剰余テンソルへ移す比較を結ぶ。
規約：可換代数を対象とし、正則性を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の (ϖ^p)=(p) に沿う移送。 -/
theorem completelyFaithfullyFlat_principal_power_algebra
    {R : Type u} [CommRing R] (a : R) (S : Type u) [CommRing S] [Algebra R S]
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) S) (n : ℕ) (hn : 0 < n) :
    IsCompletelyFaithfullyFlat (Ideal.span {a ^ n}) S := by
  refine ⟨isCompletelyFlat_principal_power a S hS.1 n, ?_⟩
  let I : Ideal R := Ideal.span {a ^ n}
  let : Module.FaithfullyFlat (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I) :=
    faithfullyFlat_power_algebraQuotient_of_completelyFaithfullyFlat a S hS n hn
  exact Module.FaithfullyFlat.of_linearEquiv (R ⧸ I)
    (S ⧸ Ideal.map (algebraMap R S) I)
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm.toLinearEquiv

end SerrePositivity.BhattScholze.Andre
