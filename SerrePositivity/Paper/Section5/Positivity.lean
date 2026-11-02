module

public import SerrePositivity.Paper.Section5.FirstComparison
public import SerrePositivity.Paper.Section5.SecondComparison
public import SerrePositivity.Paper.Section4.RankLowerBound
public import SerrePositivity.LengthAlgebra.QuotientBounds
public import SerrePositivity.Paper.Section4.LengthHypotheses
public import SerrePositivity.Paper.Section4.SupportedDescent
public import SerrePositivity.CommutativeAlgebra.Koszul.RegularEuler
public import SerrePositivity.Paper.Section5.ParameterQuotient
public import SerrePositivity.LengthAlgebra.RootTowerLength.Tower
public import SerrePositivity.Paper.Section2.LengthAlgebra.Formulas

/-! # 核の場合の正値性（論文 §5.5）

## 概要

第一比較 `|G| · a · d · χ = Σ_σ c_σ` と第二比較 `|H| · c_σ = Σ_γ b_{σ,γ}`（各 `b_{σ,γ} > 0`）から `χ > 0` を導く。本文のパラメータ商 `Z = D′/(ι(x))` と塔の作用 `θ` を作り、Lemma 5.4 の近似列と Lemma 5.3 で極限の有限性と高次の消滅を確かめ、有限近似から極小分解を切り詰めた対象に第二比較と共通下界を当てて、全ての共役の `c_σ > 0` を得る。長さ代数の公式 (2.4)–(2.6) から核心の正値性まで接続する。

## 方針

下界は極小性による `λ(C/mC)` と生成元数の正規化極限との積。パラメータ系と剰余体の条件は自己同型に沿って移す。

## 規約

データの存在を一括で仮定する class は置かない。未証明入力への依存は不変 K₀ 類の降下と Lemma 5.2 の入力に残る。

## 使われ方

`Section5/Setup`。
-/

@[expose] public noncomputable section

universe u

section PositivityPart

open IsLocalRing
open scoped ENNReal

namespace SerrePositivity

/-- 第一比較と各 `c_σ > 0` から交点数の正値性を得る。
第二比較の中間評価を再び入力する必要はない。 -/
theorem chi_pos_of_firstComparison {G : Type u} [Fintype G] [Nonempty G]
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (χ : ℤ) (c : G → ℝ)
    (hfirst : (Fintype.card G : ℝ) * a * d * (χ : ℝ) = ∑ σ, c σ)
    (hc : ∀ σ, 0 < c σ) : 0 < χ := by
  have hs : 0 < ∑ σ, c σ := Finset.sum_pos (fun σ _ ↦ hc σ) Finset.univ_nonempty
  rw [← hfirst] at hs
  have hk : (0 : ℝ) < (Fintype.card G : ℝ) * a * d := by
    have : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    positivity
  have : (0 : ℝ) < (χ : ℝ) := (mul_pos_iff_of_pos_left hk).mp hs
  exact_mod_cast this

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- 第一比較の設定と各 `c_σ > 0` から核心の交点数の正値性を導く。
`twistedEuler_pos_of_lengthAlgebras` の結論をそのまま受け取る入口。
環・群・長さ代数の存在を核心定理の仮定から構成する部分は別途必要である。 -/
theorem core_of_twistedEuler_pos
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (A D E C G : Type u) [CommRing A] [IsRegularLocalRing A]
    [CommRing D] [IsLocalRing D] [Algebra R D] [Algebra (R ⧸ P) D]
    [IsScalarTower R (R ⧸ P) D] [Module.Finite (R ⧸ P) D]
    [CommRing E] [Algebra R E] [Algebra (R ⧸ Q) E]
    [IsScalarTower R (R ⧸ Q) E] [Module.Finite (R ⧸ Q) E]
    [Algebra A D] [Module.Finite A D]
    [CommRing C] [Algebra D C] [Algebra A C] [IsScalarTower A D C]
    [Group G] [Finite G] [MulSemiringAction G D] [SMulCommClass G A D]
    {h l : ℕ} (z : Fin h → A) (hh : 0 < h)
    (hz : Ideal.span (Set.range z) = maximalIdeal A) (hdimA : ringKrullDim A = h)
    (hsupport : (Ideal.span (Set.range (algebraMap A D ∘ z))).radical = maximalIdeal D)
    (hresA : Function.Surjective ((residue D).comp (algebraMap A D)))
    (hresR : Function.Surjective ((residue D).comp (algebraMap R D)))
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A D)))
    (htrans : IsGeometricallyTransitive A D G)
    (rankD : 0 < Module.finrank (R ⧸ P) D) (rankE : 0 < Module.finrank (R ⧸ Q) E)
    (hPdim : ringKrullDim (R ⧸ P) = h) (hQdim : ringKrullDim (R ⧸ Q) = l)
    (lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C)))
    (hzero : ∀ v : ℕ, 0 < v → ∀ i : ℕ, 0 < i →
      lam.len (koszulHomologySelf (fun j ↦ algebraMap A C (z j ^ v)) i) = 0)
    (hquot : ∀ v : ℕ, 0 < v →
      lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap A C (z j ^ v))) =
        ((v ^ h * Module.finrank A D : ℕ) : ℝ≥0∞))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (hsum : ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) = ringKrullDim R)
    (hprimary : (P ⊔ Q).radical = maximalIdeal R)
    (hc : ∀ σ : G, 0 < twistedEuler R D E C G lam σ) :
    0 < chi R (R ⧸ P) (R ⧸ Q) := by
  let := Fintype.ofFinite G
  have hfirst := firstComparison P Q A D E C G z hh hz hdimA hsupport hresA hresR
    hsurj htrans rankE hPdim hQdim lam hzero hquot p hsum hprimary
  exact chi_pos_of_firstComparison (Module.finrank (R ⧸ P) D) (Module.finrank (R ⧸ Q) E)
    rankD rankE _ (twistedEuler R D E C G lam) hfirst.2 hc

end SerrePositivity

end PositivityPart

section ApproximationPositivityPart

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

end ApproximationPositivityPart

section LengthAlgebraPositivityPart

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

end LengthAlgebraPositivityPart

section RegularLengthAlgebraPositivityPart

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

end RegularLengthAlgebraPositivityPart

section TowerPositivityPart

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

end TowerPositivityPart

section ParameterLengthPositivityPart

namespace SerrePositivity.Section5

open CategoryTheory IsLocalRing ParamQuot
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

/-- (2.5) の一乗の場合から、本文の商 `U = C/(x)C` の長さを計算する。 -/
lemma parameterQuotient_length_eq_multiplicity
    {R D C : Type u} [CommRing R] [CommRing D] [IsLocalRing D]
    [CommRing C] [Algebra D C] (ι : R →+* D) {h : ℕ} (x : Fin h → R)
    (mu : NormalizedLength C ((maximalIdeal D).map (algebraMap D C)))
    (hquot : mu.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (ι (x j) ^ 1))) =
      ENNReal.ofReal ((1 : ℝ) ^ h *
        (HilbertSamuel.multiplicity D (Iσ ι x) D : ℝ))) :
    mu.len (U (φσ (C := C) ι) x) =
      ENNReal.ofReal (HilbertSamuel.multiplicity D (Iσ ι x) D : ℝ) := by
  have hspan : Ideal.span (Set.range fun j ↦ algebraMap D C (ι (x j) ^ 1)) =
      IC (φσ (C := C) ι) x := by
    rw [IC_eq]
    simp only [φσ, RingHom.comp_apply, Function.comp_def, pow_one]
  rw [hspan] at hquot
  simpa only [one_pow, one_mul] using hquot

set_option maxHeartbeats 2400000 in
-- 塔と二つの長さ代数の構造を同じパラメータ商に照合する。
/-- 本文のパラメータ商に抽象正値性を適用する。
`D′/(ι(x))`、共通消去冪、台、塔からの写像、商の正の有限な長さを内部で供給する。
入力は二つの有限局所代数、共通剰余体、パラメータ系、長さ代数の公式である。 -/
theorem lambdaChi_pos_of_parameter_lengthAlgebras
    {R D C₀ : Type u} [CommRing R] [IsRegularLocalRing R]
    [CommRing D] [IsLocalRing D] [CommRing C₀] [Algebra D C₀]
    (ι : R →+* D) {h : ℕ} (x : Fin h → R)
    (hx : IsSystemOfParameters D (ι ∘ x))
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x))
    (hresR : Function.Surjective ((residue D).comp ι))
    (A₀ : Type u) [CommRing A₀] [IsLocalRing A₀] [IsNoetherianRing A₀]
    [Algebra A₀ D] [Module.Finite A₀ D]
    (hinj : Function.Injective (algebraMap A₀ D))
    (hresD : Function.Surjective ((residue D).comp (algebraMap A₀ D)))
    {h₀ : ℕ} (t : Fin h₀ → A₀) (ht : Ideal.span (Set.range t) = maximalIdeal A₀)
    (p₀ : ℕ) [Fact p₀.Prime]
    [Algebra A₀ C₀] [Algebra (Section2.Tower A₀ t p₀) C₀]
    [IsScalarTower A₀ D C₀] [IsScalarTower A₀ (Section2.Tower A₀ t p₀) C₀]
    (hzeroD : ∀ v : ℕ, 0 < v → ∀ q : ℕ, 0 < q →
      (Section2.towerLengthOn A₀ D hinj t p₀
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) C₀).len
        (koszulHomologySelf (fun j ↦ algebraMap D C₀ (ι (x j) ^ v)) q) = 0)
    (hquotD : (Section2.towerLengthOn A₀ D hinj t p₀
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) C₀).len
        (C₀ ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C₀ (ι (x j) ^ 1))) =
      ENNReal.ofReal ((1 : ℝ) ^ h *
        (HilbertSamuel.multiplicity D (Iσ ι x) D : ℝ)))
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
      (koszulHomologySelf (fun j ↦ (algebraMap T C (algebraMap A T (a j))) ^ v) i) = 0)
    (hquotC : ∀ v : ℕ, 0 < v → lam.len
      (C ⧸ Ideal.span (Set.range fun j ↦ (algebraMap T C (algebraMap A T (a j))) ^ v)) =
        ((v ^ e * Module.finrank A T : ℕ) : ℝ≥0∞))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A T)))
    (htrans : IsGeometricallyTransitive A T G) :
    0 < lambdaChi (Section2.towerLengthOn A₀ D hinj t p₀
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) C₀) (φσ (C := C₀) ι) T := by
  let mu := Section2.towerLengthOn A₀ D hinj t p₀
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) C₀
  have : IsNoetherianRing D := IsNoetherianRing.of_finite A₀ D
  let := isLocalHom_of_residue_surjective ι hresR
  let := isLocalHom_of_residue_surjective (algebraMap A₀ D) hresD
  have hI : Iσ ι x ≠ ⊤ := by
    intro heq
    have : maximalIdeal D = ⊤ := by rw [← hx.2, show Ideal.span (Set.range (ι ∘ x)) = ⊤
      from heq, Ideal.radical_top]
    exact (maximalIdeal.isMaximal D).ne_top this
  let : Nontrivial (TD ι x) := Ideal.Quotient.nontrivial_iff.mpr hI
  let : IsLocalRing (TD ι x) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Iσ ι x)) Ideal.Quotient.mk_surjective
  let : Algebra (B x) (TD ι x) := (paramBT ι x).toAlgebra
  let : Nontrivial (B x) := (paramBT ι x).domain_nontrivial
  let : IsLocalRing (B x) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hresBZ : Function.Surjective
      ((residue (TD ι x)).comp (algebraMap (B x) (TD ι x))) := by
    have hs := residue_surjective_comp_of_surjective ι (Ideal.Quotient.mk (Iσ ι x))
      hresR Ideal.Quotient.mk_surjective
    intro z
    obtain ⟨r, hr⟩ := hs z
    exact ⟨Ideal.Quotient.mk _ r, hr⟩
  have hresZ := residue_surjective_comp_of_surjective (algebraMap A₀ D)
    (Ideal.Quotient.mk (Iσ ι x)) hresD Ideal.Quotient.mk_surjective
  have hresBT : Function.Surjective ((residue T).comp (algebraMap (B x) T)) := by
    intro z
    obtain ⟨r, hr⟩ := hresRT z
    refine ⟨algebraMap R (B x) r, ?_⟩
    simpa only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R (B x) T] using hr
  obtain ⟨v₀, _, hv₀⟩ := exists_pow_maximalIdeal_map_le (algebraMap A₀ D) hx.2.ge
  have hZa : ∀ r ∈ maximalIdeal A₀ ^ v₀, algebraMap A₀ (TD ι x) r = 0 := by
    intro r hr
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hv₀ r hr)
  have hAC : (algebraMap (Section2.Tower A₀ t p₀) C₀).comp
      (algebraMap A₀ (Section2.Tower A₀ t p₀)) =
        (algebraMap D C₀).comp (algebraMap A₀ D) := by
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  have hmap : (Iσ ι x).map (algebraMap D C₀) = IC (φσ (C := C₀) ι) x := by
    rw [IC_eq, Iσ, Ideal.map_span, ← Set.range_comp]
    rfl
  have hJrad : (maximalIdeal D).map (algebraMap D C₀) ≤
      (Ideal.span (Set.range (φσ (C := C₀) ι ∘ x))).radical := by
    rw [← hx.2]
    exact (Ideal.map_radical_le (algebraMap D C₀)).trans_eq
      (congrArg Ideal.radical (hmap.trans (IC_eq _ _)))
  have hfg := (maximalIdeal D).fg_of_isNoetherianRing.map (algebraMap D C₀)
  obtain ⟨b, hb⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJrad hfg
  have hU := parameterQuotient_length_eq_multiplicity ι x mu hquotD
  have hUfin : mu.len (U (φσ (C := C₀) ι) x) ≠ ⊤ := by
    rw [hU]; exact ENNReal.ofReal_ne_top
  have hUpos : 0 < mu.len (U (φσ (C := C₀) ι) x) := by
    rw [hU]
    exact ENNReal.ofReal_pos.mpr (by exact_mod_cast
      HilbertSamuel.multiplicity_pos_of_isSystemOfParameters D (ι ∘ x) hx)
  have hzero : ∀ v : ℕ, 0 < v → ∀ q : ℕ, 0 < q →
      mu.len (koszulHomologySelf (fun j ↦ φσ (C := C₀) ι (x j ^ v)) q) = 0 := by
    intro v hv q hq
    have hw : (fun j ↦ φσ (C := C₀) ι (x j ^ v)) =
        (fun j ↦ algebraMap D C₀ (ι (x j) ^ v)) := by
      ext j
      simp only [φσ, RingHom.comp_apply, map_pow]
    rw [hw]
    exact hzeroD v hv q hq
  exact lambdaChi_pos_of_parameter_tower (φσ (C := C₀) ι) x mu A₀ t p₀
    (fun j ↦ ht ▸ Ideal.subset_span (Set.mem_range_self j)) (TD ι x) hZa hresZ hresBZ
    (Section2.towerMaxIdeal_map_le A₀ D hinj t p₀ C₀) rfl
    (paramTheta ι x A₀ t p₀ hAC) (paramTheta_comp_tower ι x hAC)
    (paramTheta_comp_ψU ι x hAC rfl) hreg hfg (by simpa only [IC_eq] using hb)
    hJrad hzero hUfin hUpos
    A T C G lam a ha hdim hd hresA hresBT hzeroC hquotC p hsurj htrans

end SerrePositivity.Section5

end ParameterLengthPositivityPart

section TwistedLengthPositivityPart

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
      (Section2.towerLengthOn A₀ D hinj t p₀
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) C₀).len
        (koszulHomologySelf (fun j ↦ algebraMap D C₀ (z j ^ v)) q) = 0)
    (hquotD : ∀ (z : Fin h → D), IsSystemOfParameters D z →
      (Section2.towerLengthOn A₀ D hinj t p₀
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) C₀).len
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
      (Section2.towerLengthOn A₀ D hinj t p₀
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) C₀) σ := by
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

end TwistedLengthPositivityPart

section CoreLengthPositivityPart

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

end CoreLengthPositivityPart
