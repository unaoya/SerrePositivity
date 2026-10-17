module

public import SerrePositivity.BhattScholze.Andre.PrincipalDPRingEquiv

/-!
# André E1・E2：自由一元分冪代数の係数主イデアル商

## 概要

自由一元分冪代数を係数元 c で割ると、A/(c) 上の自由一元分冪代数と環同型。
BS Rem 7.15(1)（著者版 p.62）の実分冪表示の係数変更。

## 方針

任意係数上の標準分冪基底で係数変更射の全射性と核を計算し、第一同型定理を使う。

## 規約

係数環の標数・非零性・c の正則性を要求しない。環同型を構成する段階である。

## 使われ方

一次関係 γ₁=y をさらに商にして、実 pd 包自体の係数変更を比較する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {B : Type v} [CommRing B]

/-- 概要：自由分冪の係数変更は標準基底座標を係数環射で送る。
方針：両座標射を係数線形写像として束ね、標準基底上で比較する。
規約：任意の係数環射を扱う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数商射の核の計算。 -/
theorem rankOneDPRingMap_repr (φ : A →+* B) (t : DividedPowerAlgebra A A) (n : ℕ) :
    (rankOneDPAnyBasis B).repr (rankOneDPRingMap φ t) n =
      φ ((rankOneDPAnyBasis A).repr t n) := by
  classical
  let := φ.toAlgebra
  let F : DividedPowerAlgebra A A →ₐ[A] DividedPowerAlgebra B B :=
    { rankOneDPRingMap φ with commutes' := rankOneDPRingMap_coeff φ }
  let L := ((rankOneDPAnyBasis B).coord n).restrictScalars A
  have he : L.comp F.toLinearMap =
      (Algebra.linearMap A B).comp ((rankOneDPAnyBasis A).coord n) := by
    apply (rankOneDPAnyBasis A).ext
    intro i
    simp only [LinearMap.comp_apply, L, LinearMap.restrictScalars_apply,
      Module.Basis.coord_apply, AlgHom.toLinearMap_apply]
    change (rankOneDPAnyBasis B).repr
      (rankOneDPRingMap φ (rankOneDPAnyBasis A i)) n = _
    rw [rankOneDPAnyBasis_apply, rankOneDPRingMap_dp, ← rankOneDPAnyBasis_apply B i]
    rw [← rankOneDPAnyBasis_apply A i]
    simp [Module.Basis.repr_self, Finsupp.single_apply, Algebra.linearMap_apply]
  exact congrArg (fun l : DividedPowerAlgebra A A →ₗ[A] B => l t) he

/-- 概要：全射な係数環射は自由分冪代数の全射を誘導する。
方針：標準基底展開の各係数を持ち上げ、像部分環で有限和を取る。
規約：係数環の非零性を仮定しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数変更後の環同型。 -/
theorem rankOneDPRingMap_surjective (φ : A →+* B) (hφ : Function.Surjective φ) :
    Function.Surjective (rankOneDPRingMap φ) := by
  classical
  intro t
  change t ∈ (rankOneDPRingMap φ).range
  rw [← (rankOneDPAnyBasis B).linearCombination_repr t,
    Finsupp.linearCombination_apply, Finsupp.sum]
  apply (rankOneDPRingMap φ).range.sum_mem
  intro n _
  obtain ⟨b, hb⟩ := hφ ((rankOneDPAnyBasis B).repr t n)
  refine ⟨algebraMap A _ b * DividedPowerAlgebra.dp A n (1 : A), ?_⟩
  rw [map_mul, rankOneDPRingMap_coeff, rankOneDPRingMap_dp, hb,
    Algebra.smul_def, rankOneDPAnyBasis_apply]

variable (c : A)
local notation "DA" => DividedPowerAlgebra A A
local notation "R" => A ⧸ Ideal.span {(c : A)}
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(c : A)})

/-- 概要：係数商へ送る自由分冪環射の核は係数元 c の主イデアル。
方針：標準基底座標の c 可除性から各基底項を主イデアル内に足し戻す。
規約：c が零因子でもよい。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実台環の係数商比較。 -/
theorem rankOneDPCoefficientQuotient_ker :
    RingHom.ker (rankOneDPRingMap bar) = Ideal.span {algebraMap A DA c} := by
  classical
  apply le_antisymm
  · intro t ht
    have hzero : rankOneDPRingMap bar t = 0 := ht
    rw [← (rankOneDPAnyBasis A).linearCombination_repr t,
      Finsupp.linearCombination_apply, Finsupp.sum]
    apply (Ideal.span {algebraMap A DA c}).sum_mem
    intro n _
    have hc : bar ((rankOneDPAnyBasis A).repr t n) = 0 := by
      rw [← rankOneDPRingMap_repr, hzero]
      simp
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hc)
    rw [hb, Algebra.smul_def, map_mul, mul_assoc]
    exact (Ideal.span {algebraMap A DA c}).mul_mem_right _ (Ideal.mem_span_singleton_self _)
  · apply Ideal.span_le.mpr
    intro t ht
    have ht' : t = algebraMap A DA c := Set.mem_singleton_iff.mp ht
    subst t
    change rankOneDPRingMap bar (algebraMap A DA c) = 0
    rw [rankOneDPRingMap_coeff,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self c), map_zero]

/-- 概要：自由分冪代数の係数主イデアル商は係数商上の自由分冪代数と環同型。
方針：核の同定と全射性に第一同型定理を適用する。
規約：標準係数射と全次数の標準分冪を保つ同型。
使われ方：BS Rem 7.15(1)（著者版 p.62）の一次関係商の係数変更。 -/
def rankOneDPCoefficientQuotientEquiv :
    (DA ⧸ Ideal.span {algebraMap A DA c}) ≃+* DividedPowerAlgebra R R :=
  (Ideal.quotEquivOfEq (rankOneDPCoefficientQuotient_ker c).symm).trans
    ((rankOneDPRingMap bar).quotientKerEquivOfSurjective
      (rankOneDPRingMap_surjective bar Ideal.Quotient.mk_surjective))

/-- 概要：係数商同型は代表元を元の係数変更射で送る。
方針：第一同型定理の代表元公式を使う。
規約：自由分冪代数の全ての元を扱う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の関係元の照合。 -/
theorem rankOneDPCoefficientQuotientEquiv_mk (t : DA) :
    rankOneDPCoefficientQuotientEquiv c (Ideal.Quotient.mk _ t) =
      rankOneDPRingMap bar t := rfl

end SerrePositivity.BhattScholze.Andre
