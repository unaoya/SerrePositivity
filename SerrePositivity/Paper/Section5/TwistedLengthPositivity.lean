module

public import SerrePositivity.Paper.Section5.ParameterLengthPositivity
public import SerrePositivity.Paper.Section5.FirstComparison

/-! # 本文の全ての共役 Euler 数 `c_σ` の正値性

一つのパラメータ系と定理2.5の公式から、第一比較に現れる `twistedEuler` を正とする。
パラメータ系と剰余体条件は自己同型に沿って移す。長さの群不変性や、長さ代数への群作用は
仮定しない。パラメータ商・塔の作用・有限近似・第二比較は内部で構成される。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section5

open CategoryTheory IsLocalRing ParamQuot
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000 in
-- 自己同型で移したパラメータ系を同じ長さ代数の公式に代入する。
/-- 本文 (5.2) の各 `c_σ > 0`。定理2.5の公式はひねる前の長さ代数について一度与える。 -/
theorem twistedEuler_pos_of_lengthAlgebras
    {R D C₀ : Type u} [CommRing R] [IsRegularLocalRing R]
    [CommRing D] [IsLocalRing D] [CommRing C₀] [Algebra D C₀]
    [Algebra R D] (G₀ : Type u) [Group G₀] [MulSemiringAction G₀ D]
    {h : ℕ} (x : Fin h → R)
    (hx : IsSystemOfParameters D (algebraMap R D ∘ x))
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x))
    (hresR : Function.Surjective ((residue D).comp (algebraMap R D)))
    (A₀ : Type u) [CommRing A₀] [IsLocalRing A₀] [IsNoetherianRing A₀]
    [Algebra A₀ D] [Module.Finite A₀ D]
    (hinj : Function.Injective (algebraMap A₀ D))
    (hresD : Function.Surjective ((residue D).comp (algebraMap A₀ D)))
    {h₀ : ℕ} (t : Fin h₀ → A₀) (ht : Ideal.span (Set.range t) = maximalIdeal A₀)
    (p₀ : ℕ) [Fact p₀.Prime]
    [Algebra A₀ C₀] [Algebra (Section2.Tower A₀ t p₀) C₀]
    [IsScalarTower A₀ D C₀] [IsScalarTower A₀ (Section2.Tower A₀ t p₀) C₀]
    (hzeroD : ∀ (z : Fin h → D), IsSystemOfParameters D z →
      ∀ v : ℕ, 0 < v → ∀ q : ℕ, 0 < q →
      (Section2.towerLengthOn A₀ D hinj t p₀ C₀).len
        (koszulHomologySelf (fun j ↦ algebraMap D C₀ (z j ^ v)) q) = 0)
    (hquotD : ∀ (z : Fin h → D), IsSystemOfParameters D z →
      (Section2.towerLengthOn A₀ D hinj t p₀ C₀).len
        (C₀ ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C₀ (z j ^ 1))) =
      ENNReal.ofReal ((1 : ℝ) ^ h *
        (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ)))
    (A T C : Type u) [CommRing A] [IsRegularLocalRing A]
    [HasDerivedCategory (ModuleCat.{u} A)]
    [CommRing T] [IsLocalRing T] [IsDomain T] [Algebra A T] [Module.Finite A T]
    [Algebra R T] [Algebra (B x) T] [IsScalarTower R (B x) T] [Module.Finite (B x) T]
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
    (htrans : IsGeometricallyTransitive A T G) :
    ∀ σ : G₀, 0 < twistedEuler R D T C₀ G₀
      (Section2.towerLengthOn A₀ D hinj t p₀ C₀) σ := by
  intro σ
  let τ := MulSemiringAction.toRingEquiv G₀ D σ
  let ι := τ.toRingHom.comp (algebraMap R D)
  have hxσ : IsSystemOfParameters D (ι ∘ x) := hx.map_aut D τ
  have hresσ : Function.Surjective ((residue D).comp ι) :=
    residue_surjective_comp_of_surjective (algebraMap R D) τ.toRingHom hresR τ.surjective
  have hw (v : ℕ) : (fun j ↦ (algebraMap T C (algebraMap A T (a j))) ^ v) =
      (fun j ↦ algebraMap T C (algebraMap A T (a j) ^ v)) := by
    ext j
    exact (map_pow _ _ _).symm
  unfold twistedEuler twistedAlgebraMap
  apply lambdaChi_pos_of_parameter_lengthAlgebras ι x hxσ hreg hresσ
    A₀ hinj hresD t ht p₀ (hzeroD (ι ∘ x) hxσ) (hquotD (ι ∘ x) hxσ)
    A T C G lam a ha hdim hd hresA hresRT ?_ ?_ p hsurj htrans
  · intro v hv i hi
    rw [hw]
    exact hzeroC v hv i hi
  · intro v hv
    rw [hw]
    exact hquotC v hv

end SerrePositivity.Section5
