module

public import SerrePositivity.LengthAlgebra.Flat
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Finite

/-! # λ-CM 性と有限な正則部分環への制限

任意のパラメータ系についての消滅と有限性を別々の引数で受け取る。
パラメータ系の正の冪もパラメータ系なので、共通理論への入力が従う。
有限な単射 `A → D` では `A` のパラメータ系を `D` に移せるため、
剰余体の Koszul 分解があれば `A` 上の λ-平坦性と有限ランクを得る。
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.LengthAlgebra

open IsLocalRing

variable {D C : Type u} [CommRing D] [IsLocalRing D] [CommRing C]
  (ψ : D →+* C) {J : Ideal C} (lam : NormalizedLength C J)
  (hzero : ∀ {h : ℕ} (x : Fin h → D), IsSystemOfParameters D x →
    ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (ψ ∘ x) i) = 0)
  (hfinite : ∀ {h : ℕ} (x : Fin h → D), IsSystemOfParameters D x →
    lam.len (C ⧸ Ideal.span (Set.range (ψ ∘ x))) ≠ ⊤)
  {h : ℕ} (x : Fin h → D) (hx : IsSystemOfParameters D x)

include hzero hx in
/-- λ-CM 消滅から、一つのパラメータ系の全ての正の冪での消滅を得る。 -/
theorem koszulAcyclic_of_cm : KoszulAcyclic lam (ψ ∘ x) := by
  intro v hv i hi
  have hh := hzero (fun j ↦ x j ^ v) (IsSystemOfParameters.pow D hx v hv) i hi
  rw [show ψ ∘ (fun j ↦ x j ^ v) = (fun j ↦ ψ (x j) ^ v) from
    funext fun j ↦ map_pow ψ (x j) v] at hh
  exact hh

include hzero hfinite hx in
/-- λ-CM の有限性と消滅から、共通 Euler 理論の Koszul 有限性を得る。 -/
theorem koszulFinite_of_cm : KoszulFinite lam (ψ ∘ x) := by
  intro v hv q
  apply koszul_finite_of_zero_positive lam _ (koszulAcyclic_of_cm ψ lam hzero x hx v hv)
  have hh := hfinite (fun j ↦ x j ^ v) (IsSystemOfParameters.pow D hx v hv)
  rw [show ψ ∘ (fun j ↦ x j ^ v) = (fun j ↦ ψ (x j) ^ v) from
    funext fun j ↦ map_pow ψ (x j) v] at hh
  exact hh

include hzero hx in
/-- λ-CM 代数の Koszul Euler 数はパラメータ商の長さ。 -/
theorem koszulEuler_of_cm :
    koszulEuler lam (ψ ∘ x) = (lam.len (C ⧸ Ideal.span (Set.range (ψ ∘ x)))).toReal :=
  koszulEuler_eq_length_quotient lam _ (hzero x hx)

section base

variable {A : Type u} [CommRing A] [IsLocalRing A] [Algebra A D] [Module.Finite A D]
  [Algebra A C] [Algebra D C] [IsScalarTower A D C]
  (hinj : Function.Injective (algebraMap A D))
  (nu : NormalizedLength C ((maximalIdeal D).map (algebraMap D C)))
  (hcm : ∀ {h : ℕ} (x : Fin h → D), IsSystemOfParameters D x →
    ∀ i : ℕ, 0 < i → nu.len (koszulHomologySelf (algebraMap D C ∘ x) i) = 0)
  (hcmfin : ∀ {h : ℕ} (x : Fin h → D), IsSystemOfParameters D x →
    nu.len (C ⧸ Ideal.span (Set.range (algebraMap D C ∘ x))) ≠ ⊤)
  {e : ℕ} (z : Fin e → A) (hz : Ideal.span (Set.range z) = maximalIdeal A)
  (hdim : ringKrullDim A = e) (hK : IsKoszulResolution z)

include hinj hz hdim in
private lemma parameters_map : IsSystemOfParameters D (algebraMap A D ∘ z) :=
  IsSystemOfParameters.map_finite D hinj
    ⟨hdim, by rw [hz]; exact (maximalIdeal.isMaximal A).isPrime.radical⟩

include hinj hcm hz hdim hK in
/-- 有限な単射基底上では、λ-CM 性から λ-平坦性が従う。 -/
theorem flat_of_cm :
    ∀ (V : Type u) [AddCommGroup V] [Module A V], IsFiniteLength A V →
      ∀ i : ℕ, 0 < i →
        (nu.restrictToBase A D).len (TorAlg (algebraMap A C) i V) = 0 := by
  apply (flat_iff_koszul (algebraMap A C) (nu.restrictToBase A D) z hz hK).mpr
  intro i hi
  have hh := hcm _ (parameters_map hinj z hz hdim) i hi
  rw [show algebraMap D C ∘ (algebraMap A D ∘ z) = algebraMap A C ∘ z from
    funext fun j ↦ (IsScalarTower.algebraMap_apply A D C (z j)).symm] at hh
  exact hh

include hinj hcm hcmfin hz hdim hK in
/-- λ-CM 代数の基底上のランクは、基底パラメータ商の有限な長さ。
有限長加群の Tor の全公式を与える。 -/
theorem tor_length_of_cm
    (V : Type u) [AddCommGroup V] [Module A V] (hV : IsFiniteLength A V) :
    (∀ i : ℕ, 0 < i → (nu.restrictToBase A D).len (TorAlg (algebraMap A C) i V) = 0) ∧
      (nu.restrictToBase A D).len (TorAlg (algebraMap A C) 0 V) =
        nu.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ z))) *
          ENat.toENNReal (Module.length A V) ∧
      (∀ i : ℕ, (nu.restrictToBase A D).len (TorAlg (algebraMap A C) i V) ≠ ⊤) := by
  apply tor_length_of_koszul (algebraMap A C) (nu.restrictToBase A D) z hz hK
  · exact (flat_iff_koszul (algebraMap A C) (nu.restrictToBase A D) z hz hK).mp
      (flat_of_cm hinj nu hcm z hz hdim hK)
  · have hh := hcmfin _ (parameters_map hinj z hz hdim)
    rw [show algebraMap D C ∘ (algebraMap A D ∘ z) = algebraMap A C ∘ z from
      funext fun j ↦ (IsScalarTower.algebraMap_apply A D C (z j)).symm] at hh
    exact hh
  · rfl
  · exact hV

end base

end SerrePositivity.LengthAlgebra
