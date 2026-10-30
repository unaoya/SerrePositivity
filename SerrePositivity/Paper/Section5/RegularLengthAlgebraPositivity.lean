module

public import SerrePositivity.Paper.Section5.LengthAlgebraPositivity
public import SerrePositivity.Paper.Section4.SupportedDescent
public import SerrePositivity.Paper.Section4.LengthHypotheses
public import SerrePositivity.CommutativeAlgebra.Koszul.RegularEuler

/-! # 正則基底と幾何的群作用における長さ代数の正値性

正則パラメータの正則性は証明済み。不変 K₀ 類の降下について、既存の引用を適用する。
比較・下界・正値性の証明は `LengthAlgebraPositivity` の構成定理による。
このファイルの結論には、引用した未証明入力による `sorryAx` 依存が残る。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section5

open CategoryTheory Filter Topology IsLocalRing Asymptotic Section4
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {A B T C R D : Type u}
  [CommRing A] [IsRegularLocalRing A] [HasDerivedCategory (ModuleCat.{u} A)]
  [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [CommRing T] [IsLocalRing T] [IsDomain T] [Algebra A T] [Module.Finite A T]
  [Algebra B T] [Module.Finite B T]
  [CommRing C] [Nontrivial C] [Algebra T C] [CommRing R] [CommRing D] [Module R T]
  {G : Type u} [Group G] [Fintype G] [MulSemiringAction G T] [SMulCommClass G A T]
  (lam : NormalizedLength C ((maximalIdeal T).map (algebraMap T C)))
  {e : ℕ} (a : Fin e → A) (ha : Ideal.span (Set.range a) = maximalIdeal A)
  (hresA : Function.Surjective ((residue T).comp (algebraMap A T)))
  (hresB : Function.Surjective ((residue T).comp (algebraMap B T)))
  (hzero : ∀ v : ℕ, 0 < v → ∀ i : ℕ, 0 < i → lam.len
    (koszulHomologySelf (fun j ↦ (algebraMap T C (algebraMap A T (a j))) ^ v) i) = 0)
  (hquot : ∀ v : ℕ, 0 < v → lam.len
    (C ⧸ Ideal.span (Set.range fun j ↦ (algebraMap T C (algebraMap A T (a j))) ^ v)) =
      ((v ^ e * Module.finrank A T : ℕ) : ℝ≥0∞))
  {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
  (M : ℕ → FGModuleCat.{u} B)
  (τ : ℕ → ℝ≥0∞) (hτfin : ∀ i, τ i ≠ ⊤) (hτzero : ∀ i, e < i → τ i = 0)
  (hτlim : ∀ i, Tendsto (fun n ↦
    (Module.length B (TorModule B i (M n) (B ⧸ maximalIdeal B)) : ℝ≥0∞) / (s n : ℝ≥0∞))
    atTop (𝓝 (τ i)))
  (I₀ : Ideal B) (hI₀ : ∀ n, ∀ r ∈ I₀, ∀ m : M n, r • m = 0)
  (hI₀fin : Module.length B (B ⧸ I₀) ≠ ⊤)
  {L₀ : ℝ≥0∞} (hL₀fin : L₀ ≠ ⊤) (hL₀pos : 0 < L₀)
  (hlen : Tendsto (fun n ↦ (Module.length B (M n) : ℝ≥0∞) / (s n : ℝ≥0∞)) atTop (𝓝 L₀))
  {I : Ideal D} (mu : NormalizedLength D I) (ι : R →+* D)
  (hfinite : ∀ i, mu.len (TorAlg ι i T) ≠ ⊤)
  (hlim : ∀ i, Tendsto (fun n ↦
    (Module.length B (TorModule B i (M n) T) : ℝ≥0∞) / (s n : ℝ≥0∞))
    atTop (𝓝 (mu.len (TorAlg ι i T))))

set_option maxHeartbeats 1800000 in
-- 証明済みの正則性と不変 K₀ 類の降下の引用を、長さ代数への適用へ接続する。
include hresA hresB hτfin hτzero hτlim hI₀ hI₀fin hL₀fin hL₀pos hlen hfinite hlim in
/-- 正則基底と幾何的群作用の下での有限近似の正値性。
証明済みの正則パラメータの正則性と、補題4.6・定理3.1による
`supportedRankK0_descent` の引用を使う。
比較と正値性を新たな未証明入力にはしない。 -/
theorem exists_secondComparison_pos_of_regular
    (hdim : ringKrullDim A = e) (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A T)))
    (htrans : IsGeometricallyTransitive A T G) :
    let hfg := finite_lengthAlgebra_ideal_fg A (algebraMap T C)
    let hJ := finite_lengthAlgebra_support (algebraMap T C) a ha
    let hfin := koszulFinite_of_lengthAlgebra_values lam
      (algebraMap T C ∘ algebraMap A T ∘ a) (Module.finrank A T) hzero hquot
    ∃ X : (paperSupportedRank (s := s) (algebraMap A T ∘ a)).FullSubcategory,
      (Fintype.card G : ℝ) * lambdaChi mu ι T =
        ∑ g : G, paperBaseChangeEulerK0 (algebraMap T C) (algebraMap A T ∘ a)
          lam hfg hJ hfin U hU hs (g • TriangulatedK0.mk X) ∧
      (∀ g : G, 0 < paperBaseChangeEulerK0 (algebraMap T C) (algebraMap A T ∘ a)
        lam hfg hJ hfin U hU hs (g • TriangulatedK0.mk X)) ∧
      0 < lambdaChi mu ι T := by
  let : IsDomain A := isDomain_of_isRegularLocalRing A
  let : Module.IsTorsionFree A T :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr
      (algebraMap_injective_of_spectrum_surjective A T hsurj)
  exact exists_secondComparison_pos_of_lengthAlgebra lam a ha hresA hresB hzero hquot
    U hU hs M τ hτfin hτzero hτlim I₀ hI₀ hI₀fin hL₀fin hL₀pos hlen mu ι hfinite hlim
    (isKoszulResolution_of_isWeaklyRegular a
      (isWeaklyRegular_of_span_eq_maximalIdeal A a ha hdim))
    (koszulEulerChar_eq_finrank A T a ha hdim) Module.finrank_pos
    (supportedRankK0_descent A T p a ha s hs G hsurj htrans)

end SerrePositivity.Section5
