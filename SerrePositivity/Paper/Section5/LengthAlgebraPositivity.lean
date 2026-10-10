module

public import SerrePositivity.Paper.Section5.ApproximationPositivity
public import SerrePositivity.Paper.Section4.LengthAlgebraRealization

/-! # 長さ代数の具体的な公式から第二比較と正値性へ

有限局所代数、共通剰余体、Koszul 消滅・商の階数公式を抽象層へ渡す。
近似側の支持の生成元・消去冪、両写像の局所性、Koszul 有限性・Euler 数の一致、
下界の商の正値性は内部で確認する。
Koszul 分解・通常階数公式・不変類の降下を個別に受け取る。
正則・幾何的な仮定からの引用の適用は `RegularLengthAlgebraPositivity` に分離する。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section5

open CategoryTheory Filter Topology IsLocalRing Asymptotic Section4
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {A B T C R D : Type u}
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [HasDerivedCategory (ModuleCat.{u} A)]
  [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [CommRing T] [IsLocalRing T] [Algebra A T] [Module.Finite A T]
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
-- 有限性の証明と同じ支持部分圏の評価を構成定理へ渡す。
include hresA hresB hτfin hτzero hτlim hI₀ hI₀fin hL₀fin hL₀pos hlen hfinite hlim in
/-- 長さ代数の具体的な二つの公式から、第二比較の対象と正値性を構成する。
近似列は指定するが、支持のパラメータ・消去冪・各種有限性・商の正値性は内部で導く。 -/
theorem exists_secondComparison_pos_of_lengthAlgebra
    (hKos : IsKoszulResolution a) (hχ : koszulEulerChar A T a = Module.finrank A T)
    (hrank : 0 < Module.finrank A T)
    (hdesc : ∀ y : TriangulatedK0
        (paperSupportedRank (s := s) (algebraMap A T ∘ a)).FullSubcategory,
      (∀ g : G, g • y = y) → ∃ (n : ℕ)
        (x : TriangulatedK0 (paperSupportedRank (s := s) a).FullSubcategory),
        0 < n ∧ n • y = TriangulatedK0.map (paperSupportedChangeRing (algebraMap A T) a) x) :
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
  let : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  let := isLocalHom_of_residue_surjective (algebraMap A T) hresA
  let := isLocalHom_of_residue_surjective (algebraMap B T) hresB
  obtain ⟨f, z, N, hz, hN, hpow⟩ := exists_maximal_generators_pow_mem I₀ hI₀fin
  exact exists_secondComparison_pos_of_primary (algebraMap T C) lam
    (finite_lengthAlgebra_ideal_fg A (algebraMap T C)) a
    (finite_lengthAlgebra_support (algebraMap T C) a ha)
    (koszulFinite_of_lengthAlgebra_values lam _ (Module.finrank A T) hzero hquot)
    ha hKos U hU hs (koszulEuler_eq_of_lengthAlgebra_values a lam hquot hresA hχ hzero)
    hdesc M τ hτfin hτzero hτlim I₀ hI₀ hI₀fin hL₀fin hL₀pos hlen z N hN hpow
    hresB mu ι hfinite hlim hzero (maximalIdeal_le_radical_span_of_finite T a ha)
    (maximalIdeal_le_radical_span_of_finite T z hz)
    (residue_length_pos_of_lengthAlgebra_values a ha lam hquot hrank)

end SerrePositivity.Section5
