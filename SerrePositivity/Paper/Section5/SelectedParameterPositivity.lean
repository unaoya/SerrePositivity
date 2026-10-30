module

public import SerrePositivity.Paper.Section5.CoreLengthPositivity
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Avoidance

/-! # パラメータを内部で選ぶ核心の正値性

素イデアル商の次元と `P + Q` の根基から (5.4) のパラメータを選び、有限拡大へ移す。
`R/(x) → E′` とその有限性・係数環の両立も内部で構成する。
正規化基底・群作用・長さ代数の構成とは分離した、本文の具体的な適用である。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section5

open CategoryTheory IsLocalRing
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000 in
-- 選んだパラメータ商の代数構造を、正値性の入口と同じ構造として渡す。
/-- 次元条件と `P + Q` の根基からパラメータを選んで、長さ代数による核心の正値性を導く。
正則列、有限拡大上のパラメータ系、`R/(x)` 上の有限代数構造は入力しない。 -/
theorem core_of_lengthAlgebras_with_parameter_choice
    {R D C₀ : Type u} [CommRing R] [IsRegularLocalRing R]
    [CommRing D] [IsLocalRing D] [CommRing C₀] [Algebra D C₀]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    [Algebra R D] [Algebra (R ⧸ P) D] [IsScalarTower R (R ⧸ P) D]
    [Module.Finite (R ⧸ P) D] (G₀ : Type u) [Group G₀] [Finite G₀] [MulSemiringAction G₀ D]
    {h : ℕ}
    (hresR : Function.Surjective ((residue D).comp (algebraMap R D)))
    (A₀ : Type u) [CommRing A₀] [IsRegularLocalRing A₀]
    [Algebra A₀ D] [Module.Finite A₀ D] [SMulCommClass G₀ A₀ D]
    (hinj : Function.Injective (algebraMap A₀ D))
    (hresD : Function.Surjective ((residue D).comp (algebraMap A₀ D)))
    (t : Fin h → A₀) (ht : Ideal.span (Set.range t) = maximalIdeal A₀)
    (p₀ : ℕ) [Fact p₀.Prime]
    [Algebra A₀ C₀] [Algebra (Section2.Tower A₀ t p₀) C₀]
    [IsScalarTower A₀ D C₀] [IsScalarTower A₀ (Section2.Tower A₀ t p₀) C₀]
    (hzeroD : ∀ (z : Fin h → D), IsSystemOfParameters D z →
      ∀ v : ℕ, 0 < v → ∀ q : ℕ, 0 < q →
      (Section2.towerLengthOn A₀ D hinj t p₀
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) C₀).len
        (koszulHomologySelf (fun j ↦ algebraMap D C₀ (z j ^ v)) q) = 0)
    (hquotD : ∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v →
      (Section2.towerLengthOn A₀ D hinj t p₀
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) C₀).len
        (C₀ ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C₀ (z j ^ v))) =
      ENNReal.ofReal ((v : ℝ) ^ h *
        (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ)))
    (A T C : Type u) [CommRing A] [IsRegularLocalRing A]
    [HasDerivedCategory (ModuleCat.{u} A)]
    [CommRing T] [IsLocalRing T] [IsDomain T] [Algebra A T] [Module.Finite A T]
    [Algebra R T] [Algebra (R ⧸ Q) T] [IsScalarTower R (R ⧸ Q) T]
    [Module.Finite (R ⧸ Q) T]
    [CommRing C] [Nontrivial C] [Algebra T C]
    (G : Type u) [Group G] [Finite G] [MulSemiringAction G T] [SMulCommClass G A T]
    (lam : NormalizedLength C ((maximalIdeal T).map (algebraMap T C)))
    {e : ℕ} (a : Fin e → A) (ha : Ideal.span (Set.range a) = maximalIdeal A)
    (hdim : ringKrullDim A = e) (hd : ringKrullDim R = (e + h : ℕ))
    (hresA : Function.Surjective ((residue T).comp (algebraMap A T)))
    (hresRT : Function.Surjective ((residue T).comp (algebraMap R T)))
    (hzeroC : ∀ v : ℕ, 0 < v → ∀ i : ℕ, 0 < i → lam.len
      (koszulHomologySelf (fun j ↦ algebraMap T C (algebraMap A T (a j) ^ v)) i) = 0)
    (hquotC : ∀ v : ℕ, 0 < v → lam.len
      (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap T C (algebraMap A T (a j) ^ v))) =
        ((v ^ e * Module.finrank A T : ℕ) : ℝ≥0∞))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A T)))
    (htrans : IsGeometricallyTransitive A T G)
    (hh : 0 < h) (hdimA₀ : ringKrullDim A₀ = h)
    (hsop : IsSystemOfParameters D (algebraMap A₀ D ∘ t))
    (hsurjD : Function.Surjective (PrimeSpectrum.comap (algebraMap A₀ D)))
    (htransD : IsGeometricallyTransitive A₀ D G₀)
    (rankD : 0 < Module.finrank (R ⧸ P) D) (rankT : 0 < Module.finrank (R ⧸ Q) T)
    (hPdim : ringKrullDim (R ⧸ P) = h) (hQdim : ringKrullDim (R ⧸ Q) = e)
    (hprimary : (P ⊔ Q).radical = maximalIdeal R)
    (pR : ℕ) [Fact pR.Prime] [CharP (ResidueField R) pR] :
    0 < chi R (R ⧸ P) (R ⧸ Q) := by
  let : FaithfulSMul (R ⧸ P) D := by
    by_contra hn
    exact rankD.ne' (Module.finrank_eq_zero_of_not_faithfulSMul hn)
  obtain ⟨x, hxQ, hreg, hx⟩ := exists_regular_parameters_for_finite_extension P Q D
    (FaithfulSMul.algebraMap_injective (R ⧸ P) D) hd hPdim hQdim hprimary
  have hxQ' : Ideal.span (Set.range x) ≤ Q := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hxQ i
  obtain ⟨bAlg, bTower, bFinite⟩ := exists_finite_quotientAlgebra
    (Ideal.span (Set.range x)) Q hxQ' T
  let := bAlg
  have := bTower
  have := bFinite
  exact core_of_lengthAlgebras P Q G₀ x hx hreg hresR A₀ hinj hresD t ht p₀
    hzeroD hquotD A T C G lam a ha hdim hd hresA hresRT hzeroC hquotC p hsurj htrans
    hh hdimA₀ hsop hsurjD htransD rankD rankT hPdim hQdim hprimary pR

end SerrePositivity.Section5
