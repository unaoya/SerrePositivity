module

public import SerrePositivity.Paper.Section5.TwistedLengthPositivity
public import SerrePositivity.Paper.Section5.Positivity
public import SerrePositivity.Paper.Section2.LengthAlgebraConsequences

/-! # 長さ代数の具体的な公式から核心の正値性へ

同じ環・群作用・長さ代数について、全ての `c_σ > 0` と第一比較を接続する。
第二比較の中間値・近似列・商の正値性は入力しない。必要な長さの公式は定理2.5の
(2.4)・(2.5) と比較先の (2.6) であり、比較元の (2.6) は重複度の階数公式から得る。
正規化基底や群作用などを `core_statement` の仮定から選ぶ存在構成は別途必要である。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section5

open CategoryTheory IsLocalRing ParamQuot
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000 in
-- 二つの比較で使う長さ代数と環構造を同じものにそろえる。
/-- 本文の有限拡大・パラメータ・長さ代数の公式から核心の交点数は正。
有限近似と第二比較を構成し、各 `c_σ > 0` を第一比較に渡す。 -/
theorem core_of_lengthAlgebras
    {R D C₀ : Type u} [CommRing R] [IsRegularLocalRing R]
    [CommRing D] [IsLocalRing D] [CommRing C₀] [Algebra D C₀]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    [Algebra R D] [Algebra (R ⧸ P) D] [IsScalarTower R (R ⧸ P) D]
    [Module.Finite (R ⧸ P) D] (G₀ : Type u) [Group G₀] [Finite G₀] [MulSemiringAction G₀ D]
    {h : ℕ} (x : Fin h → R)
    (hx : IsSystemOfParameters D (algebraMap R D ∘ x))
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x))
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
    [Module.Finite (R ⧸ Q) T] [Algebra (B x) T] [IsScalarTower R (B x) T] [Module.Finite (B x) T]
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
  have : IsNoetherianRing D := IsNoetherianRing.of_finite A₀ D
  let mu := Section2.towerLengthOn A₀ D hinj t p₀
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) C₀
  have hc := twistedEuler_pos_of_lengthAlgebras G₀ x hx hreg hresR A₀ hinj hresD t ht p₀
    hzeroD (fun z hz ↦ by simpa only [Nat.cast_one] using hquotD z hz 1 one_pos)
    A T C G lam a ha hdim hd
    hresA hresRT hzeroC hquotC p hsurj htrans
  have hquot := Section2.base_parameter_values_of_multiplicity A₀ D C₀ hinj hresD
    t ht hdimA₀ hsop mu hquotD
  have hsum : ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) = ringKrullDim R := by
    rw [hPdim, hQdim, hd, Nat.cast_add, add_comm]
  have hw (v : ℕ) : (fun j ↦ algebraMap A₀ C₀ (t j ^ v)) =
      (fun j ↦ algebraMap D C₀ (algebraMap A₀ D (t j) ^ v)) := by
    ext j
    rw [IsScalarTower.algebraMap_apply A₀ D C₀, map_pow]
  apply core_of_twistedEuler_pos P Q A₀ D T C₀ G₀ t hh ht hdimA₀ hsop.2
    hresD hresR hsurjD htransD rankD rankT hPdim hQdim mu ?_ ?_ pR hsum hprimary hc
  · intro v hv i hi
    rw [hw]
    exact hzeroD (algebraMap A₀ D ∘ t) hsop v hv i hi
  · intro v hv
    rw [hw]
    exact hquot v hv

end SerrePositivity.Section5
