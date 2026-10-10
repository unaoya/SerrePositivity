module

public import SerrePositivity.Paper.Section5.ApproximationSecondComparison
public import SerrePositivity.Asymptotic.LocalBaseChangeBounds
public import SerrePositivity.LengthAlgebra.QuotientBounds

/-! # 有限近似から第二比較の対象と正値性を同時に構成する

同じ近似列の極小分解を切り詰め、係数変更した対象に第二比較と共通下界を適用する。
複体・振幅・極小性・正の零次階数・支持・各共役の正値性は内部で導く。
残す入力は近似極限、環準同型の局所性、支持の根基条件、Koszul 条件、不変類の降下、
および係数環の商の正の長さである。近似先の写像をひねると `c_σ > 0` の形になる。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section5

open CategoryTheory CategoryTheory.Limits Filter Topology IsLocalRing Asymptotic
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {A B T C R D : Type u}
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [HasDerivedCategory (ModuleCat.{u} A)]
  [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [CommRing T] [IsLocalRing T] [Algebra A T] [Algebra B T]
  [IsLocalHom (algebraMap A T)] [IsLocalHom (algebraMap B T)]
  [CommRing C] [Nontrivial C] [CommRing R] [CommRing D] [Module R T]
  {G : Type u} [Group G] [Fintype G] [MulSemiringAction G T] [SMulCommClass G A T]
  (ψ : T →+* C) {J : Ideal C} (lam : NormalizedLength C J) (hfg : J.FG)
  {e : ℕ} (a : Fin e → A)
  (hJ : J ≤ (Ideal.span (Set.range (ψ ∘ algebraMap A T ∘ a))).radical)
  (hfin : LengthAlgebra.KoszulFinite lam (ψ ∘ algebraMap A T ∘ a))
  (hord : LengthAlgebra.KoszulFinite (NormalizedLength.ordinary T) (algebraMap A T ∘ a))
  (ha : Ideal.span (Set.range a) = maximalIdeal A) (hKos : IsKoszulResolution a)
  {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
  (hc : LengthAlgebra.koszulEuler (NormalizedLength.ordinary T) (algebraMap A T ∘ a) =
    LengthAlgebra.koszulEuler lam (ψ ∘ algebraMap A T ∘ a))
  (hdesc : ∀ y : TriangulatedK0 (paperSupportedRank (s := s) (algebraMap A T ∘ a)).FullSubcategory,
    (∀ g : G, g • y = y) → ∃ (n : ℕ)
      (x : TriangulatedK0 (paperSupportedRank (s := s) a).FullSubcategory),
      0 < n ∧ n • y = TriangulatedK0.map (paperSupportedChangeRing (algebraMap A T) a) x)
  (M : ℕ → FGModuleCat.{u} B)
  (τ : ℕ → ℝ≥0∞) (hτfin : ∀ i, τ i ≠ ⊤) (hτzero : ∀ i, e < i → τ i = 0)
  (hτlim : ∀ i, Tendsto (fun n ↦
    (Module.length B (TorModule B i (M n) (B ⧸ maximalIdeal B)) : ℝ≥0∞) / (s n : ℝ≥0∞))
    atTop (𝓝 (τ i)))
  (I₀ : Ideal B) (hI₀ : ∀ n, ∀ r ∈ I₀, ∀ m : M n, r • m = 0)
  (hI₀fin : Module.length B (B ⧸ I₀) ≠ ⊤)
  {L₀ : ℝ≥0∞} (hL₀fin : L₀ ≠ ⊤) (hL₀pos : 0 < L₀)
  (hlen : Tendsto (fun n ↦ (Module.length B (M n) : ℝ≥0∞) / (s n : ℝ≥0∞)) atTop (𝓝 L₀))
  {f : ℕ} (z : Fin f → B) (N : ℕ) (hN : 0 < N) (hz : ∀ j, z j ^ N ∈ I₀)
  (hordB : LengthAlgebra.KoszulFinite (NormalizedLength.ordinary T) (algebraMap B T ∘ z))
  (hspan : Ideal.span (Set.range (algebraMap A T ∘ a)) ≤
    (Ideal.span (Set.range (algebraMap B T ∘ z))).radical)
  (hres : Function.Surjective ((residue T).comp (algebraMap B T)))
  {I : Ideal D} (mu : NormalizedLength D I) (ι : R →+* D)
  (hfinite : ∀ i, mu.len (TorAlg ι i T) ≠ ⊤)
  (hlim : ∀ i, Tendsto (fun n ↦
    (Module.length B (TorModule B i (M n) T) : ℝ≥0∞) / (s n : ℝ≥0∞))
    atTop (𝓝 (mu.len (TorAlg ι i T))))
  (hzero : ∀ v : ℕ, 0 < v → ∀ i : ℕ, 0 < i →
    lam.len (koszulHomologySelf (fun j ↦ ψ (algebraMap A T (a j)) ^ v) i) = 0)
  (Q : Ideal C) (hQmap : ∀ r ∈ maximalIdeal T, ψ r ∈ Q)
  (hQ : IsPowTorsion J (C ⧸ Q)) (hQpos : 0 < (lam.len (C ⧸ Q)).toReal)

set_option maxHeartbeats 2400000 in
-- 近似複体の構成、二つの支持の移送、実際の K₀ 群作用の型の比較に必要。
include ha hKos hc hdesc hτfin hτzero hτlim hI₀ hI₀fin hL₀fin hL₀pos hlen hN hz
  hordB hspan hres hfinite hlim hzero hQmap hQ hQpos in
/-- 有限近似から、第二比較と全共役の正値性を満たす同じ対象を構成する。
通常評価の正値性も結論であり、複体や評価の正値性を入力にしない。 -/
theorem exists_secondComparison_pos_of_approximation :
    ∃ X : (paperSupportedRank (s := s) (algebraMap A T ∘ a)).FullSubcategory,
      (∀ g : G, paperRankEulerK0 (NormalizedLength.ordinary T) Submodule.fg_bot
        (algebraMap A T ∘ a) bot_le hord U hU hs (g • TriangulatedK0.mk X) = lambdaChi mu ι T) ∧
      (Fintype.card G : ℝ) * lambdaChi mu ι T =
        ∑ g : G, paperBaseChangeEulerK0 ψ (algebraMap A T ∘ a) lam hfg hJ hfin U hU hs
          (g • TriangulatedK0.mk X) ∧
      (∀ g : G, 0 < paperBaseChangeEulerK0 ψ (algebraMap A T ∘ a) lam hfg hJ hfin U hU hs
        (g • TriangulatedK0.mk X)) ∧
      0 < lambdaChi mu ι T := by
  obtain ⟨hO, ho⟩ := betti_growth_of_approximation_limits M e hs τ hτfin hτzero hτlim
  obtain ⟨F, hb, he, _, hm, hp, hF, _⟩ := exists_supported_minimal_approximation
    (fun n ↦ (M n).obj) (fun _ ↦ inferInstance) e s hs hO (ho (e + 1) (by omega))
      I₀ hI₀ hI₀fin hL₀fin hL₀pos hlen U hU z N hN hz
  let hFbound : strictlyBoundedComplex _ F := ⟨-(e : ℤ), 0, hb.1, hb.2⟩
  have hM (n : ℕ) (j : Fin f) : z j ^ N • 𝟙 (M n).obj = 0 := by
    ext m
    exact hI₀ n _ (hz j) m
  obtain ⟨hT, heval, hsecond⟩ := secondComparison_of_approximation ψ lam hfg a hJ hfin hord
    ha hKos U hU hs hc hdesc M e τ hτfin hτzero hτlim F hFbound he z hF N hN hM
      hordB hspan hres mu ι hfinite hlim
  let K := ((FreeSequence.changeRing (algebraMap B T)).mapHomologicalComplex (.up ℤ)).obj F
  let hK := changeRing_strictlyBounded (algebraMap B T) F hFbound
  let X : (paperSupportedRank (s := s) (algebraMap A T ∘ a)).FullSubcategory :=
    ⟨(paperSequenceFunctor T s).obj (sequenceHomotopyObj K hK), hT⟩
  have hboundF (n : ℕ) (q : ℤ) (hq : q < -(e : ℤ) ∨ 0 < q) :
      IsZero (((evaluateComplex n).obj F).X q) := by
    have := hb.1
    have := hb.2
    rcases hq with hq | hq
    · exact (FreeSequence.evaluation n).map_isZero (F.isZero_of_isStrictlyGE _ q hq)
    · exact (FreeSequence.evaluation n).map_isZero (F.isZero_of_isStrictlyLE _ q hq)
  have hamem (j : Fin e) : a j ∈ maximalIdeal A := by
    rw [← ha]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hpositive (g : G) : 0 < paperBaseChangeEulerK0 ψ (algebraMap A T ∘ a)
      lam hfg hJ hfin U hU hs (g • TriangulatedK0.mk X) :=
    (mul_pos hQpos hp).trans_le
      (paperBaseChangeEuler_smul_lower_bound_of_local ψ a lam hfg hJ hfin U hU hs
        hamem hzero K hK hT (changeRing_evaluate_amplitude (algebraMap B T) F _ _ hboundF)
        (changeRing_minimal (algebraMap B T) F hm) Q hQmap hQ g)
  refine ⟨X, heval, hsecond, hpositive, ?_⟩
  have hsum := Finset.sum_pos (fun g _ ↦ hpositive g) Finset.univ_nonempty
  rw [← hsecond] at hsum
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  exact (mul_pos_iff_of_pos_left hcard).mp hsum

set_option maxHeartbeats 1200000 in
-- 二つの支持の有限性を根基条件から供給し、既存の構成定理へ渡す。
include ha hKos hc hdesc hτfin hτzero hτlim hI₀ hI₀fin hL₀fin hL₀pos hlen hN hz
  hres hfinite hlim hzero in
/-- 準素な支持条件から、通常有限性・支持変更・商の冪ねじれ性を内部で確認する版。
下界に使う商は `C / m_T C` とし、その正の長さだけを入力に残す。 -/
theorem exists_secondComparison_pos_of_primary [IsNoetherianRing T]
    (hprimaryA : maximalIdeal T ≤ (Ideal.span (Set.range (algebraMap A T ∘ a))).radical)
    (hprimaryB : maximalIdeal T ≤ (Ideal.span (Set.range (algebraMap B T ∘ z))).radical)
    (hquotpos : 0 < lam.len (C ⧸ (maximalIdeal T).map ψ)) :
    ∃ X : (paperSupportedRank (s := s) (algebraMap A T ∘ a)).FullSubcategory,
      (Fintype.card G : ℝ) * lambdaChi mu ι T =
        ∑ g : G, paperBaseChangeEulerK0 ψ (algebraMap A T ∘ a) lam hfg hJ hfin U hU hs
          (g • TriangulatedK0.mk X) ∧
      (∀ g : G, 0 < paperBaseChangeEulerK0 ψ (algebraMap A T ∘ a) lam hfg hJ hfin U hU hs
        (g • TriangulatedK0.mk X)) ∧
      0 < lambdaChi mu ι T := by
  have haT (j : Fin e) : algebraMap A T (a j) ∈ maximalIdeal T := by
    apply map_nonunit
    rw [← ha]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hspan' : Ideal.span (Set.range (algebraMap A T ∘ a)) ≤
      (Ideal.span (Set.range (algebraMap B T ∘ z))).radical := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hprimaryB (haT j)
  let Q' := (maximalIdeal T).map ψ
  have hQmap' : ∀ r ∈ maximalIdeal T, ψ r ∈ Q' := fun r hr ↦ Ideal.mem_map_of_mem ψ hr
  have haQ : Ideal.span (Set.range (ψ ∘ algebraMap A T ∘ a)) ≤ Q' := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hQmap' _ (haT j)
  have hQ' := LengthAlgebra.quotient_isPowTorsion_of_span_le hfg _ hJ Q' haQ
  have hQfin := LengthAlgebra.length_quotient_ne_top_of_koszul_finite lam hfg _ hJ Q' haQ hfin
  have hQpos' : 0 < (lam.len (C ⧸ Q')).toReal :=
    ENNReal.toReal_pos (ne_of_gt hquotpos) hQfin
  obtain ⟨X, _, heq, hpos, hχ⟩ := exists_secondComparison_pos_of_approximation
    ψ lam hfg a hJ hfin (ordinary_koszul_finite_of_maximal_le_radical _ hprimaryA)
    ha hKos U hU hs hc hdesc M τ hτfin hτzero hτlim I₀ hI₀ hI₀fin hL₀fin hL₀pos hlen
    z N hN hz (ordinary_koszul_finite_of_maximal_le_radical _ hprimaryB) hspan'
    hres mu ι hfinite hlim hzero Q' hQmap' hQ' hQpos'
  exact ⟨X, heq, hpos, hχ⟩

end SerrePositivity.Section5
