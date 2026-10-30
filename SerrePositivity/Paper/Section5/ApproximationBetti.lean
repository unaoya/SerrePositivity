module

public import SerrePositivity.Paper.Section5.ApproximationHomology
public import SerrePositivity.HomologicalAlgebra.TorSymmetry
public import SerrePositivity.Asymptotic.MinimalBettiEvaluation
public import SerrePositivity.Asymptotic.NormalizedLowerBound
public import SerrePositivity.PerfectComplex.NormalizedLengthComap
public import SerrePositivity.CommutativeAlgebra.Length.Basic

/-! # 有限近似の極限を商の Betti・Euler 評価へ接続する

剰余体係数の極限から自由項の増大条件を確認し、共通の消去冪から
全分解とランク商の双方で Koszul 分裂を得る。比較の本体は Asymptotic 層に置く。
通常の収束値を用いる結論は超フィルターの選択によらない。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section5

open CategoryTheory Filter Topology IsLocalRing Asymptotic
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {B S : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [CommRing S] (φ : B →+* S) (M : ℕ → FGModuleCat.{u} B) {s : ℕ → ℕ}
  (l : ℕ) (hs : ∀ n, 0 < s n)
  (τ : ℕ → ℝ≥0∞) (hτfin : ∀ i, τ i ≠ ⊤) (hτzero : ∀ i, l < i → τ i = 0)
  (hτlim : ∀ i, Tendsto (fun n ↦
    (Module.length B (TorModule B i (M n) (B ⧸ maximalIdeal B)) : ℝ≥0∞) / (s n : ℝ≥0∞))
    atTop (𝓝 (τ i)))
  (K : CochainComplex (FreeSequence B s) ℤ) (hK : strictlyBoundedComplex _ K)
  (eK : ∀ n, Nonempty ((evaluateComplex n).obj K ≅ MinimalFreeResolution.truncated (M n) l))
  {e : ℕ} (z : Fin e → B)
  (h : paperSupportedRank z ((paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK)))
  (v : ℕ) (hv : 0 < v) (hM : ∀ n j, z j ^ v • 𝟙 (M n).obj = 0)
  {J : Ideal S} (lam : NormalizedLength S J) (hfg : J.FG)
  (hJ : J ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q,
    lam.len ((koszulComplex (fun j ↦ φ (z j) ^ v)).homology q) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)

section Nontrivial

variable [Nontrivial S]

include hτfin hτzero hτlim eK hv hM in
/-- 有限近似の各次数の極限は、商上の Betti 評価に一致する。 -/
theorem paperBaseChangeBetti_eq_of_approximation_limit (i : ℕ) (ρ : ℝ≥0∞) (hρ : ρ ≠ ⊤)
    (hlim : Tendsto (fun n ↦ lam.len (TorAlg φ i (M n)) / (s n : ℝ≥0∞)) atTop (𝓝 ρ)) :
    paperBaseChangeBetti φ z lam hfg hJ hfin U hU hs
      ⟨(paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK), h⟩ (-(i : ℤ)) = ρ.toReal := by
  obtain ⟨hO, ho⟩ := betti_growth_of_approximation_limits M l hs τ hτfin hτzero hτlim
  rw [paperBaseChangeBetti_eq_minimal_tor_limit φ M z lam hfg hJ hfin U hU hs
    l K hK eK hO ho h v hv hM]
  exact normalizedLimit_eq_of_ennreal_tendsto U hU s _ hρ hlim

include hs hτfin hτzero hτlim hK eK h hv hM hfg hJ hfin hU in
/-- すべての有限な極限を商の評価と同定すると、極限列の有限支持も従う。
各有限近似に一様な射影次元を仮定する必要はない。 -/
theorem approximation_tor_limits_hasFiniteSupport (ρ : ℕ → ℝ≥0∞)
    (hρ : ∀ i, ρ i ≠ ⊤)
    (hlim : ∀ i, Tendsto (fun n ↦ lam.len (TorAlg φ i (M n)) / (s n : ℝ≥0∞))
      atTop (𝓝 (ρ i))) : Function.HasFiniteSupport (fun i ↦ (ρ i).toReal) := by
  have hi : Function.Injective (fun i : ℕ ↦ -(i : ℤ)) := fun i j hij ↦ by
    exact_mod_cast neg_injective hij
  have hf := (paperBaseChangeBetti_hasFiniteSupport φ z lam hfg hJ hfin U hU hs
    ⟨(paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK), h⟩).fun_comp_of_injective hi
  have he (i : ℕ) := paperBaseChangeBetti_eq_of_approximation_limit φ M l hs τ
    hτfin hτzero hτlim K hK eK z h v hv hM lam hfg hJ hfin U hU i (ρ i) (hρ i) (hlim i)
  simpa only [he] using hf

include hτfin hτzero hτlim eK hv hM in
/-- 商の Euler 評価は有限近似の Tor 極限の有限交代和になる。 -/
theorem paperBaseChangeEulerK0_eq_of_approximation_limits (ρ : ℕ → ℝ≥0∞)
    (hρ : ∀ i, ρ i ≠ ⊤)
    (hlim : ∀ i, Tendsto (fun n ↦ lam.len (TorAlg φ i (M n)) / (s n : ℝ≥0∞))
      atTop (𝓝 (ρ i))) :
    paperBaseChangeEulerK0 φ z lam hfg hJ hfin U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK), h⟩) =
      ∑ᶠ i : ℕ, (-1 : ℝ) ^ i * (ρ i).toReal := by
  obtain ⟨hO, ho⟩ := betti_growth_of_approximation_limits M l hs τ hτfin hτzero hτlim
  rw [paperBaseChangeEulerK0_eq_minimal_tor_limits φ M z lam hfg hJ hfin U hU hs
    l K hK eK hO ho h v hv hM]
  congr 1
  funext i
  rw [normalizedLimit_eq_of_ennreal_tendsto U hU s _ (hρ i) (hlim i)]

section Ordinary

variable [Algebra B S]

local notation "lamB" =>
  NormalizedLength.comap (algebraMap B S) (NormalizedLength.ordinary B) ⊥ (by simp)

include hτfin hτzero hτlim eK hv hM in
/-- 有限近似で使う `Tor_i(M_n,S)` の基底環上の通常の長さから、商の評価を計算する。
ここでは商の評価も `B` 上の長さで測る。`S` 上の通常の長さへの変更は別の比較である。 -/
theorem paperOrdinaryBetti_eq_of_approximation_limit
    (hfinB : ∀ v : ℕ, 0 < v → ∀ q,
      (lamB).len ((koszulComplex (fun j ↦ algebraMap B S (z j) ^ v)).homology q) ≠ ⊤)
    (i : ℕ) (ρ : ℝ≥0∞) (hρ : ρ ≠ ⊤)
    (hlim : Tendsto (fun n ↦ (Module.length B (TorModule B i (M n) S) : ℝ≥0∞) /
      (s n : ℝ≥0∞)) atTop (𝓝 ρ)) :
    paperBaseChangeBetti (algebraMap B S) z lamB Submodule.fg_bot bot_le hfinB U hU hs
      ⟨(paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK), h⟩ (-(i : ℤ)) = ρ.toReal := by
  apply paperBaseChangeBetti_eq_of_approximation_limit (algebraMap B S) M l hs τ
    hτfin hτzero hτlim K hK eK z h v hv hM lamB Submodule.fg_bot bot_le hfinB U hU i ρ hρ
  have he (n : ℕ) : (lamB).len (TorAlg (algebraMap B S) i (M n)) =
      (Module.length B (TorModule B i (M n) S) : ℝ≥0∞) := by
    exact congrArg (fun x : ℕ∞ ↦ (x : ℝ≥0∞)) (length_restrictScalars_torAlg_comm (M n) i)
  simpa only [he] using hlim

end Ordinary
end Nontrivial

section OrdinaryResidue

variable [Algebra B S] [IsLocalRing S]
  (hres : Function.Surjective ((residue S).comp (algebraMap B S)))
  (hfinS : ∀ v : ℕ, 0 < v → ∀ q,
    (NormalizedLength.ordinary S).len
      ((koszulComplex (fun j ↦ algebraMap B S (z j) ^ v)).homology q) ≠ ⊤)

include hτfin hτzero hτlim eK hv hM hres in
/-- 剰余体が共通なら、`B` 上の通常 Tor の極限は `S` 上の通常長さによる商の評価となる。 -/
theorem paperOrdinaryBetti_eq_of_common_residueField_limit
    (i : ℕ) (ρ : ℝ≥0∞) (hρ : ρ ≠ ⊤)
    (hlim : Tendsto (fun n ↦ (Module.length B (TorModule B i (M n) S) : ℝ≥0∞) /
      (s n : ℝ≥0∞)) atTop (𝓝 ρ)) :
    paperBaseChangeBetti (algebraMap B S) z (NormalizedLength.ordinary S)
      Submodule.fg_bot bot_le hfinS U hU hs
      ⟨(paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK), h⟩ (-(i : ℤ)) = ρ.toReal := by
  apply paperBaseChangeBetti_eq_of_approximation_limit (algebraMap B S) M l hs τ
    hτfin hτzero hτlim K hK eK z h v hv hM (NormalizedLength.ordinary S)
    Submodule.fg_bot bot_le hfinS U hU i ρ hρ
  have he (n : ℕ) : (NormalizedLength.ordinary S).len (TorAlg (algebraMap B S) i (M n)) =
      (Module.length B (TorModule B i (M n) S) : ℝ≥0∞) := by
    let N := ModuleCat.of S (TorAlg (algebraMap B S) i (M n))
    exact congrArg (fun x : ℕ∞ ↦ (x : ℝ≥0∞))
      ((length_restrictScalars_eq hres N).symm.trans
        (length_restrictScalars_torAlg_comm (M n) i))
  simpa only [he] using hlim

include hτfin hτzero hτlim eK hv hM hres in
/-- 共通剰余体の下で、通常 Euler 評価は有限近似の通常 Tor 極限の交代和に一致する。 -/
theorem paperOrdinaryEulerK0_eq_of_common_residueField_limits (ρ : ℕ → ℝ≥0∞)
    (hρ : ∀ i, ρ i ≠ ⊤)
    (hlim : ∀ i, Tendsto (fun n ↦ (Module.length B (TorModule B i (M n) S) : ℝ≥0∞) /
      (s n : ℝ≥0∞)) atTop (𝓝 (ρ i))) :
    paperBaseChangeEulerK0 (algebraMap B S) z (NormalizedLength.ordinary S)
      Submodule.fg_bot bot_le hfinS U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK), h⟩) =
      ∑ᶠ i : ℕ, (-1 : ℝ) ^ i * (ρ i).toReal := by
  apply paperBaseChangeEulerK0_eq_of_approximation_limits (algebraMap B S) M l hs τ
    hτfin hτzero hτlim K hK eK z h v hv hM (NormalizedLength.ordinary S)
    Submodule.fg_bot bot_le hfinS U hU ρ hρ
  intro i
  have he (n : ℕ) : (NormalizedLength.ordinary S).len (TorAlg (algebraMap B S) i (M n)) =
      (Module.length B (TorModule B i (M n) S) : ℝ≥0∞) := by
    let N := ModuleCat.of S (TorAlg (algebraMap B S) i (M n))
    exact congrArg (fun x : ℕ∞ ↦ (x : ℝ≥0∞))
      ((length_restrictScalars_eq hres N).symm.trans
        (length_restrictScalars_torAlg_comm (M n) i))
  simpa only [he] using hlim i

end OrdinaryResidue

end SerrePositivity.Section5
