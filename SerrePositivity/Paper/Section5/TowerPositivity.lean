module

public import SerrePositivity.Paper.Section5.RegularLengthAlgebraPositivity
public import SerrePositivity.Paper.Section5.ParameterQuotient

/-! # パラメータ商の塔から通常 Euler 数の正値性を導く

Lemma 5.4 により同じ近似列と全ての Tor 極限を構成し、Lemma 5.3 で極限の有限性・
高次消滅を確認する。その列を長さ代数への抽象比較の適用へ渡す。
近似列・複体・比較等式・Euler 正値性を入力として要求しない。
塔の長さの加法性と正則パラメータの正則性は証明済み。
未証明入力への依存は、不変 K₀ 類の降下に残る。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section5

open CategoryTheory Filter Topology IsLocalRing ParamQuot
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000 in
-- 二つの基底とパラメータ商の加群構造を、同じ近似列の構成に照合する。
/-- 塔の近似と長さ代数の公式から `lambdaChi > 0`。
論文では `φ = ι_σ`、`T = E′` として `c_σ > 0` を与える。
塔の作用の両立と商の正の長さは具体的な環の側に残し、有限近似は内部で構成する。 -/
theorem lambdaChi_pos_of_parameter_tower
    {R D : Type u} [CommRing R] [IsRegularLocalRing R] [CommRing D]
    (φ : R →+* D) {h : ℕ} (x : Fin h → R) [IsLocalRing (B x)]
    {J : Ideal D} (mu : NormalizedLength D J)
    (A₀ : Type u) [CommRing A₀] [IsLocalRing A₀] [IsNoetherianRing A₀]
    {h₀ : ℕ} (t : Fin h₀ → A₀) (p₀ : ℕ) [Fact p₀.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A₀)
    (Z : Type u) [CommRing Z] [IsLocalRing Z] [Algebra A₀ Z] [Module.Finite A₀ Z]
    {v₀ : ℕ} (hZa : ∀ r ∈ maximalIdeal A₀ ^ v₀, algebraMap A₀ Z r = 0)
    (hresZ : Function.Surjective ((residue Z).comp (algebraMap A₀ Z)))
    [Algebra (B x) Z]
    (hresBZ : Function.Surjective ((residue Z).comp (algebraMap (B x) Z)))
    [Algebra (Section2.Tower A₀ t p₀) D]
    (hJ' : (Section2.towerMaxIdeal A₀ t p₀).map (algebraMap (Section2.Tower A₀ t p₀) D) ≤ J)
    (hmu : mu = (Section2.towerLength A₀ t p₀ ht).comap
      (algebraMap (Section2.Tower A₀ t p₀) D) J hJ')
    (θ : Section2.TS A₀ t p₀ Z →+* U φ x)
    (hθΛ : θ.comp (algebraMap (Section2.Tower A₀ t p₀) (Section2.TS A₀ t p₀ Z)) =
      (Ideal.Quotient.mk (IC φ x)).comp (algebraMap (Section2.Tower A₀ t p₀) D))
    (hθB : θ.comp (Section2.ψU A₀ t p₀ Z (B x)) = ψ φ x)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x))
    (hfg : J.FG) {b : ℕ} (hJ : J ^ b ≤ IC φ x)
    (hJrad : J ≤ (Ideal.span (Set.range (φ ∘ x))).radical)
    (hzeroD : ∀ v : ℕ, 0 < v → ∀ q : ℕ, 0 < q →
      mu.len (koszulHomologySelf (fun j ↦ φ (x j ^ v)) q) = 0)
    (hUfin : mu.len (U φ x) ≠ ⊤) (hUpos : 0 < mu.len (U φ x))
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
    (hresBT : Function.Surjective ((residue T).comp (algebraMap (B x) T)))
    (hzeroC : ∀ v : ℕ, 0 < v → ∀ i : ℕ, 0 < i → lam.len
      (koszulHomologySelf (fun j ↦ (algebraMap T C (algebraMap A T (a j))) ^ v) i) = 0)
    (hquot : ∀ v : ℕ, 0 < v → lam.len
      (C ⧸ Ideal.span (Set.range fun j ↦ (algebraMap T C (algebraMap A T (a j))) ^ v)) =
        ((v ^ e * Module.finrank A T : ℕ) : ℝ≥0∞))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A T)))
    (htrans : IsGeometricallyTransitive A T G) : 0 < lambdaChi mu φ T := by
  let := Fintype.ofFinite G
  let : IsArtinianRing Z := isArtinianRing_of_finite_killed_maximal_pow A₀ Z hZa
  let I₀ := RingHom.ker (algebraMap (B x) Z)
  have hI₀ : ∀ r ∈ I₀, algebraMap (B x) Z r = 0 := fun _ hr ↦ hr
  have hI₀fin := length_quotient_ker_ne_top_of_common_residue hresBZ
  obtain ⟨M, s, hMfl, hs, _, hann, hlen, htor, hk, _⟩ := lemma_5_4 φ x mu
    A₀ t p₀ ht Z hZa hresZ hresBZ hJ' hmu θ hθΛ hθB hd hreg hfg hJ hJrad hzeroD hUfin
    (fun _ : Unit ↦ T)
  let MF (n : ℕ) : FGModuleCat.{u} (B x) := ⟨M n, by
    have := (isFiniteLength_iff_isNoetherian_isArtinian.mp (hMfl n)).1
    exact Module.IsNoetherian.finite _ _⟩
  have hkTor (i : ℕ) := lemma_5_3 φ x mu hd hreg hfg hJ hJrad hzeroD hUfin
    (B x ⧸ maximalIdeal (B x)) i
  have hTTor (i : ℕ) := lemma_5_3 φ x mu hd hreg hfg hJ hJrad hzeroD hUfin T i
  obtain ⟨X, _, _, hpos⟩ := exists_secondComparison_pos_of_regular (G := G)
    lam a ha hresA hresBT hzeroC hquot (Ultrafilter.of atTop) (Ultrafilter.of_le atTop) hs MF
    (fun i ↦ mu.len (TorAlg φ i (B x ⧸ maximalIdeal (B x))))
    (fun i ↦ (hkTor i).2.1) (fun i hi ↦ (hkTor i).2.2 (by omega)) hk
    I₀ (hann I₀ hI₀) hI₀fin hUfin hUpos hlen mu φ (fun i ↦ (hTTor i).2.1) (htor ())
    hdim p hsurj htrans
  exact hpos

end SerrePositivity.Section5
