module

public import SerrePositivity.Paper.Section5.ApproximationBetti
public import SerrePositivity.Paper.Section5.SupportedApproximation
public import SerrePositivity.Paper.Section5.FirstComparison
public import SerrePositivity.HomologicalAlgebra.KoszulOrdinaryLength
public import SerrePositivity.Asymptotic.PaperSupportChange

/-! # 有限近似の通常 Euler 評価、ひねり、`c_σ`

極小分解から作った同一の商の対象について、係数写像を任意の自己同型で
ひねっても通常評価は変わらない。有限近似の Tor 極限を与えると、
その Euler 評価は `lambdaChi`、特に本文の `c_σ = twistedEuler` に一致する。
長さ付き代数の長さの群不変性は仮定しない。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section5

open CategoryTheory Filter Topology IsLocalRing Asymptotic
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {B S : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [CommRing S] [IsLocalRing S] [Algebra B S]
  (M : ℕ → FGModuleCat.{u} B) {s : ℕ → ℕ} (l : ℕ) (hs : ∀ n, 0 < s n)
  (τ : ℕ → ℝ≥0∞) (hτfin : ∀ i, τ i ≠ ⊤) (hτzero : ∀ i, l < i → τ i = 0)
  (hτlim : ∀ i, Tendsto (fun n ↦
    (Module.length B (TorModule B i (M n) (B ⧸ maximalIdeal B)) : ℝ≥0∞) / (s n : ℝ≥0∞))
    atTop (𝓝 (τ i)))
  (K : CochainComplex (FreeSequence B s) ℤ) (hK : strictlyBoundedComplex _ K)
  (eK : ∀ n, Nonempty ((evaluateComplex n).obj K ≅ MinimalFreeResolution.truncated (M n) l))
  {e : ℕ} (z : Fin e → B)
  (h : paperSupportedRank z ((paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK)))
  (v : ℕ) (hv : 0 < v) (hM : ∀ n j, z j ^ v • 𝟙 (M n).obj = 0)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q,
    (NormalizedLength.ordinary S).len
      ((koszulComplex (fun j ↦ algebraMap B S (z j) ^ v)).homology q) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)

include hτfin hτzero hτlim eK hv hM in
/-- 極小分解の商の通常 Euler 評価は、係数環の自己同型によるひねりで不変。
ひねり後の Koszul 有限性も元の有限性から導く。 -/
theorem paperOrdinaryEulerK0_comp_equiv (σ : S ≃+* S) :
    paperBaseChangeEulerK0 (σ.toRingHom.comp (algebraMap B S)) z (NormalizedLength.ordinary S)
      Submodule.fg_bot bot_le (ordinary_koszul_finite_comp_equiv _ σ z hfin) U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK), h⟩) =
    paperBaseChangeEulerK0 (algebraMap B S) z (NormalizedLength.ordinary S)
      Submodule.fg_bot bot_le hfin U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK), h⟩) := by
  obtain ⟨hO, ho⟩ := betti_growth_of_approximation_limits M l hs τ hτfin hτzero hτlim
  rw [paperBaseChangeEulerK0_eq_minimal_tor_limits _ M z _ _ _ _ U hU hs
    l K hK eK hO ho h v hv hM,
    paperBaseChangeEulerK0_eq_minimal_tor_limits _ M z _ _ _ _ U hU hs
      l K hK eK hO ho h v hv hM]
  congr 1
  funext i
  congr 1
  apply congrArg (normalizedLimit U s)
  funext n
  exact congrArg (fun a : ℕ∞ ↦ (a : ℝ≥0∞).toReal)
    (length_torAlg_comp_equiv (algebraMap B S) σ (M n) i)

variable (hres : Function.Surjective ((residue S).comp (algebraMap B S)))
  {R C : Type u} [CommRing R] [CommRing C] [Module R S]
  {J : Ideal C} (lam : NormalizedLength C J) (φ : R →+* C)
  (hfinite : ∀ i, lam.len (TorAlg φ i S) ≠ ⊤)
  (hlim : ∀ i, Tendsto (fun n ↦
    (Module.length B (TorModule B i (M n) S) : ℝ≥0∞) / (s n : ℝ≥0∞))
    atTop (𝓝 (lam.len (TorAlg φ i S))))

include hτfin hτzero hτlim eK hv hM hres hfinite hlim in
/-- 有限近似の Tor 極限から、すべてのひねりの通常 Euler 評価を同じ `lambdaChi` と同定する。 -/
theorem paperOrdinaryEulerK0_eq_lambdaChi (σ : S ≃+* S) :
    paperBaseChangeEulerK0 (σ.toRingHom.comp (algebraMap B S)) z (NormalizedLength.ordinary S)
      Submodule.fg_bot bot_le (ordinary_koszul_finite_comp_equiv _ σ z hfin) U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK), h⟩) =
      lambdaChi lam φ S := by
  rw [paperOrdinaryEulerK0_comp_equiv M l hs τ hτfin hτzero hτlim
    K hK eK z h v hv hM hfin U hU σ]
  exact paperOrdinaryEulerK0_eq_of_common_residueField_limits M l hs τ hτfin hτzero hτlim
    K hK eK z h v hv hM U hU hres hfin (fun i ↦ lam.len (TorAlg φ i S)) hfinite hlim

include hτfin hτzero hτlim hv hres hfinite hlim in
/-- 同じ有限近似から支持つき複体列を構成し、その全ひねりの通常 Euler 評価を計算する。
振幅・極小性・零次階数の正値性も保持し、後の共通 Euler 下界に使える形で返す。 -/
theorem exists_supported_approximation_with_lambdaChi
    (I : Ideal B) (hI : ∀ n, ∀ a ∈ I, ∀ m : M n, a • m = 0)
    (hIfin : Module.length B (B ⧸ I) ≠ ⊤) (hz : ∀ j, z j ^ v ∈ I)
    {L : ℝ≥0∞} (hLfin : L ≠ ⊤) (hLpos : 0 < L)
    (hlen : Tendsto (fun n ↦ (Module.length B (M n) : ℝ≥0∞) / (s n : ℝ≥0∞))
      atTop (𝓝 L)) :
    ∃ F : CochainComplex (FreeSequence B s) ℤ,
      ∃ hb : F.IsStrictlyGE (-(l : ℤ)) ∧ F.IsStrictlyLE 0,
      ∃ hF : paperSupportedRank z ((paperSequenceFunctor B s).obj
        (sequenceHomotopyObj F ⟨-(l : ℤ), 0, hb.1, hb.2⟩)),
      (∀ n, Nonempty ((evaluateComplex n).obj F ≅ MinimalFreeResolution.truncated (M n) l)) ∧
      (∀ n (x : Fin ((F.X (-1)).rank n) → B) (j : Fin ((F.X 0).rank n)),
        F.d (-1) 0 n x j ∈ maximalIdeal B) ∧
      0 < normalizedLimit U s (fun n ↦ ((F.X 0).rank n : ℝ)) ∧
      (∀ j, z j ^ v • 𝟙 ((paperSequenceFunctor B s).obj
        (sequenceHomotopyObj F ⟨-(l : ℤ), 0, hb.1, hb.2⟩)) = 0) ∧
      ∀ σ : S ≃+* S,
        paperBaseChangeEulerK0 (σ.toRingHom.comp (algebraMap B S)) z (NormalizedLength.ordinary S)
          Submodule.fg_bot bot_le (ordinary_koszul_finite_comp_equiv _ σ z hfin) U hU hs
          (TriangulatedK0.mk ⟨(paperSequenceFunctor B s).obj
            (sequenceHomotopyObj F ⟨-(l : ℤ), 0, hb.1, hb.2⟩), hF⟩) = lambdaChi lam φ S := by
  obtain ⟨hO, ho⟩ := betti_growth_of_approximation_limits M l hs τ hτfin hτzero hτlim
  obtain ⟨F, hb, he, _, hm, hp, hF, hx⟩ := exists_supported_minimal_approximation
    (fun n ↦ (M n).obj) (fun _ ↦ inferInstance) l s hs hO (ho (l + 1) (by omega))
      I hI hIfin hLfin hLpos hlen U hU z v hv hz
  have hM' (n : ℕ) (j : Fin e) : z j ^ v • 𝟙 (M n).obj = 0 := by
    ext m
    exact hI n (z j ^ v) (hz j) m
  refine ⟨F, hb, hF, he, hm, hp, hx, fun σ ↦ ?_⟩
  exact paperOrdinaryEulerK0_eq_lambdaChi M l hs τ hτfin hτzero hτlim F _ he
    z hF v hv hM' hfin U hU hres lam φ hfinite hlim σ

include hτfin hτzero hτlim eK hv hM hres in
/-- 本文の `c_σ` との同定。`σ` は近似する長さ付き代数側、`γ` は有限係数環側のひねり。
`σ` を固定すると、通常 Euler 評価はすべての `γ` について `c_σ` になる。 -/
theorem paperOrdinaryEulerK0_eq_twistedEuler
    (D G : Type u) [CommRing D] [Algebra R D] [Algebra D C]
    [Group G] [MulSemiringAction G D] (σ : G)
    (hfiniteσ : ∀ i, lam.len (TorAlg (twistedAlgebraMap R D C G σ) i S) ≠ ⊤)
    (hlimσ : ∀ i, Tendsto (fun n ↦
      (Module.length B (TorModule B i (M n) S) : ℝ≥0∞) / (s n : ℝ≥0∞))
      atTop (𝓝 (lam.len (TorAlg (twistedAlgebraMap R D C G σ) i S))))
    (γ : S ≃+* S) :
    paperBaseChangeEulerK0 (γ.toRingHom.comp (algebraMap B S)) z (NormalizedLength.ordinary S)
      Submodule.fg_bot bot_le (ordinary_koszul_finite_comp_equiv _ γ z hfin) U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK), h⟩) =
      twistedEuler R D S C G lam σ := by
  simpa only [twistedEuler] using
    paperOrdinaryEulerK0_eq_lambdaChi M l hs τ hτfin hτzero hτlim K hK eK
      z h v hv hM hfin U hU hres lam (twistedAlgebraMap R D C G σ) hfiniteσ hlimσ γ

end SerrePositivity.Section5
