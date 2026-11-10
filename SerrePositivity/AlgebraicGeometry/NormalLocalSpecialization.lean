module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
概要：素点の特殊化を整閉局所整域の生成点と閉点で表す。
方針：生成点で割った整域を正規化し、lying over で閉点の上に素点を取り局所化する。
規約：Noether 性や離散付値環の存在は仮定しない。
使われ方：滑らかな族の切断を通るファイバー成分が生成化で保たれることを示す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped nonZeroDivisors

/--
概要：可換環の素イデアルの包含は、整閉局所整域への写像の核と極大イデアルの縮約で表される。
方針：生成点の閉包を正規化し、指定点の上で局所化する。
規約：正規化は分数体の中で取る。
使われ方：Stacks 055Q の滑らかな場合における二つの切断の比較。
-/
theorem exists_normalLocalDomain_of_prime_le
    {B : Type u} [CommRing B] (p q : Ideal B) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) :
    ∃ (V : Type u) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V)
      (_ : IsIntegrallyClosed V) (f : B →+* V),
      RingHom.ker f = p ∧ (IsLocalRing.maximalIdeal V).comap f = q := by
  let R := B ⧸ p
  let π : B →+* R := Ideal.Quotient.mk p
  let Q := q.map π
  let : Q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (Ideal.mk_ker.trans_le hpq)
  let K := FractionRing R
  let N := integralClosure R K
  have hi : Function.Injective (algebraMap R N) := by
    intro x y h
    exact IsFractionRing.injective R K (congrArg Subtype.val h)
  let : IsIntegrallyClosed N := integralClosure.isIntegrallyClosedOfFiniteExtension K
  obtain ⟨m, hm, hmQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := N) Q
    (((RingHom.injective_iff_ker_eq_bot _).mp hi).le.trans bot_le)
  let V := Localization.AtPrime m
  have hm₀ : m.primeCompl ≤ N⁰ := by
    intro x hx
    exact mem_nonZeroDivisors_iff_ne_zero.mpr fun h => hx (h ▸ m.zero_mem)
  let : IsDomain V := IsLocalization.isDomain_of_le_nonZeroDivisors V hm₀
  let : IsIntegrallyClosed V := isIntegrallyClosed_of_isLocalization V m.primeCompl hm₀
  let j := algebraMap R N
  let k := algebraMap N V
  let f := (k.comp j).comp π
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, f, ?_, ?_⟩
  · change RingHom.ker ((k.comp j).comp π) = p
    rw [RingHom.ker_comp_of_injective π ((IsLocalization.injective V hm₀).comp hi)]
    exact Ideal.mk_ker
  · change (IsLocalRing.maximalIdeal V).comap ((k.comp j).comp π) = q
    rw [← Ideal.comap_comap, ← Ideal.comap_comap]
    change (((IsLocalRing.maximalIdeal V).under N).under R).comap π = q
    rw [Localization.AtPrime.under_maximalIdeal, hmQ]
    change (q.map π).comap π = q
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker,
      sup_eq_left.mpr hpq]

end SerrePositivity.AlgebraicGeometry
