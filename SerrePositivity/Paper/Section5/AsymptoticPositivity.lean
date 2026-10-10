module

public import SerrePositivity.Paper.Section5.SupportedApproximation
public import SerrePositivity.Paper.Section5.ApproximationEuler
public import SerrePositivity.Paper.Section5.ApproximationGrowth
public import SerrePositivity.Paper.Section5.ApproximationSecondComparison
public import SerrePositivity.Paper.Section5.ApproximationPositivity
public import SerrePositivity.Paper.Section5.NormalizationPositivity
public import SerrePositivity.Paper.Section5.SecondComparisonLowerBound
public import SerrePositivity.Asymptotic.PaperMinimalLowerBound

/-! # 有限近似と抽象 Euler 理論による正値性

有限近似の長さの収束、極小性、自由振幅、商での支持、係数環の Koszul 消滅を
個別に与え、共通の下界から論文側の Euler 評価の正値性を導く。
`SupportedApproximation` が振幅・極小性・正の零次階数・商での支持を構成する。
構成した列に共通の下界を適用し、Euler 評価が正の対象の存在まで得る。
`ApproximationBetti` により、同じ対象の各次数の評価と有限近似の Tor 極限が一致し、
Euler 評価をその有限交代和で計算できる。
`ApproximationEuler` は有限近似の極限から全ひねりの通常評価を `c_σ` と同定する。
`ApproximationGrowth` はパラメータ商での有限性・消滅から Betti 数の増大条件を供給する。
`ApproximationSecondComparison` は同じ複体の支持を移し、実際の群作用について第二比較を導く。
`SecondComparisonLowerBound` は各共役の共通下界を、比較元の通常 Euler 評価にも移す。
`ApproximationPositivity` は同じ近似から第二比較の対象と全共役の正値性を同時に構成し、
通常 Euler 数の正値性まで導く。係数変更後の振幅・極小性も内部で確認する。
`LengthAlgebraPositivity` は有限局所代数と長さ代数の公式から適用条件を確認する。
`TowerPositivity` は Lemma 5.4 の近似列を内部で構成し、Lemma 5.3 の有限性・消滅を
用いて正値性へ接続する。`ParameterLengthPositivity` は本文のパラメータ商から
塔の作用・消去冪・支持を構成し、重複度公式から商の正の有限な長さを導く。
`TwistedLengthPositivity` は全ての `c_σ > 0` を一つのパラメータ系から導き、
`CoreLengthPositivity` は同じ設定で第一比較までつなぐ。
`SelectedParameterPositivity` は次元・根基条件からパラメータと有限商代数を選ぶ。
`NormalizationPositivity` は定理2.5から二つの長さ代数を構成し、不変環の条件から
幾何的推移性を導いて、核心の正値性へ接続する。
正規化基底と、それを固定する有限群作用付き拡大の存在構成が前段に残る。
-/

@[expose] public section

universe u

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Section5

open CategoryTheory CategoryTheory.Limits Filter Topology IsLocalRing Asymptotic
open scoped ENNReal

variable {B R S : Type u} [CommRing B] [IsLocalRing B]
  [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  {s : ℕ → ℕ} (φ : R →+* S) {e : ℕ} (z : Fin e → R)
  {J : Ideal S} (lam : NormalizedLength S J) (hfg : J.FG)
  (hJ : J ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q,
    lam.len ((koszulComplex (fun j ↦ φ (z j) ^ v)).homology q) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 有限近似の長さと極小生成元数の関係から、係数変更後の Euler 評価が正になる。
`B` はパラメータ商、`R` は比較に使う有限局所代数、`S` は長さ付き係数代数を想定する。
`B` の正則性や、元の複体列の一様支持は仮定しない。 -/
theorem paperEuler_pos_of_finiteApproximation
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) = 0)
    (hzero : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (fun j ↦ φ (z j) ^ v) i) = 0)
    (hbound : ∀ t q, q < -(e : ℤ) ∨ 0 < q → IsZero (((evaluateComplex t).obj K).X q))
    (I : Ideal R) (Q : Ideal S) (hIQ : ∀ r ∈ I, φ r ∈ Q)
    (hQ : IsPowTorsion J (S ⧸ Q))
    (hmin : ∀ t (m : Fin ((K.X (-1)).rank t) → R) j, (K.d (-1) 0 t m) j ∈ I)
    (hzI : ∀ j, z j ^ v ∈ I) (hlen : 0 < (lam.len (S ⧸ Q)).toReal)
    (M : ℕ → ModuleCat.{u} B) (hM : ∀ n, Module.Finite B (M n))
    (I₀ : Ideal B) (hI₀ : ∀ n, ∀ y ∈ I₀, ∀ m : M n, y • m = 0)
    (hI₀fin : Module.length B (B ⧸ I₀) ≠ ⊤)
    (hbeta : ∀ n, Module.length B (TorModule B 0 (M n) (B ⧸ maximalIdeal B)) = (K.X 0).rank n)
    {L : ℝ≥0∞} (hLfin : L ≠ ⊤) (hLpos : 0 < L)
    (hlim : Tendsto (fun n ↦ (Module.length B (M n) : ℝ≥0∞) / (s n : ℝ≥0∞))
      atTop (𝓝 L)) :
    0 < paperBaseChangeEulerK0 φ z lam hfg hJ hfin U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩) := by
  have hrank := finiteApproximation_rank_pos M hM I₀ hI₀ hI₀fin s (K.X 0).rank hs
    (K.X 0).rank_isBigO hbeta hLfin hlim U hU hLpos
  exact (mul_pos hlen hrank).trans_le
    (paperBaseChangeEuler_minimal_lower_bound φ z lam hfg hJ hfin U hU hs
      K hK h v hv hx hzero hbound I Q hIQ hQ hmin hzI)

section construction

variable [IsNoetherianRing B]

set_option maxHeartbeats 800000 in
-- 支持つき商と二つの係数環を含む存在命題の型の比較に余裕を与える。
/-- 有限近似のデータから、係数変更後の Euler 評価が正の支持つき対象を構成する。
複体列・極小性・零次階数公式・支持を、外部入力として要求しない。 -/
theorem exists_paperEuler_pos_of_minimalApproximation
    (ψ : B →+* S) (y : Fin e → B)
    (hJ' : J ≤ (Ideal.span (Set.range (ψ ∘ y))).radical)
    (hfin' : ∀ v : ℕ, 0 < v → ∀ q,
      lam.len ((koszulComplex (fun j ↦ ψ (y j) ^ v)).homology q) ≠ ⊤)
    (M : ℕ → ModuleCat.{u} B) (hM : ∀ n, Module.Finite B (M n))
    (hbetti : ∀ i ≤ e,
      Asymptotics.IsBigO atTop
        (fun n ↦ ((Module.length B (TorModule B i (M n) (B ⧸ maximalIdeal B))).toNat : ℝ))
        (fun n ↦ (s n : ℝ)))
    (hsmall : Asymptotics.IsLittleO atTop
      (fun n ↦ ((Module.length B
        (TorModule B (e + 1) (M n) (B ⧸ maximalIdeal B))).toNat : ℝ))
      (fun n ↦ (s n : ℝ)))
    (I : Ideal B) (hI : ∀ n, ∀ a ∈ I, ∀ m : M n, a • m = 0)
    (hIfin : Module.length B (B ⧸ I) ≠ ⊤)
    {L : ℝ≥0∞} (hLfin : L ≠ ⊤) (hLpos : 0 < L)
    (hlim : Tendsto (fun n ↦ (Module.length B (M n) : ℝ≥0∞) / (s n : ℝ≥0∞))
      atTop (𝓝 L))
    (N : ℕ) (hN : 0 < N) (hy : ∀ j, y j ^ N ∈ I)
    (hymax : ∀ j, y j ^ N ∈ maximalIdeal B)
    (hzero : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (fun j ↦ ψ (y j) ^ N) i) = 0)
    (Q : Ideal S) (hQmap : ∀ a ∈ maximalIdeal B, ψ a ∈ Q)
    (hQ : IsPowTorsion J (S ⧸ Q)) (hlen : 0 < (lam.len (S ⧸ Q)).toReal) :
    ∃ (K : CochainComplex (FreeSequence B s) ℤ)
      (hK : strictlyBoundedComplex _ K)
      (h : paperSupportedRank y ((paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK))),
      0 < paperBaseChangeEulerK0 ψ y lam hfg hJ' hfin' U hU hs
        (TriangulatedK0.mk ⟨(paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK), h⟩) := by
  obtain ⟨K, hb, _, _, hm, hp, h, hx⟩ := exists_supported_minimal_approximation
    M hM e s hs hbetti hsmall I hI hIfin hLfin hLpos hlim U hU y N hN hy
  let hK : strictlyBoundedComplex _ K := ⟨-(e : ℤ), 0, hb.1, hb.2⟩
  have := hb.1
  have := hb.2
  have hbound (t : ℕ) (q : ℤ) (hq : q < -(e : ℤ) ∨ 0 < q) :
      IsZero (((evaluateComplex t).obj K).X q) := by
    rcases hq with hq | hq
    · exact (FreeSequence.evaluation t).map_isZero (K.isZero_of_isStrictlyGE _ q hq)
    · exact (FreeSequence.evaluation t).map_isZero (K.isZero_of_isStrictlyLE _ q hq)
  exact ⟨K, hK, h, (mul_pos hlen hp).trans_le
    (paperBaseChangeEuler_minimal_lower_bound ψ y lam hfg hJ' hfin' U hU hs
      K hK h N hN hx hzero hbound (maximalIdeal B) Q hQmap hQ hm hymax)⟩

end construction

end SerrePositivity.Section5
