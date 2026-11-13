module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.Paper.Section4.EulerComparison
public import SerrePositivity.Paper.Section4.RankQuotient
public import SerrePositivity.CategoryTheory.Euler
public import SerrePositivity.LengthAlgebra.Koszul
public import SerrePositivity.Paper.Section4.LengthHypotheses
public import SerrePositivity.LengthAlgebra.Flat
public import SerrePositivity.Paper.Section4.SupportedDescent
public import SerrePositivity.CommutativeAlgebra.Koszul.RegularEuler
public import SerrePositivity.LengthAlgebra.KoszulFormula
public import SerrePositivity.LengthAlgebra.Core
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Fractions
public import SerrePositivity.LengthAlgebra.Perfect
public import SerrePositivity.PerfectComplex.KoszulLength
public import SerrePositivity.Paper.Section4.RankLowerBound

/-! # 対称なランク商比較と漸近ノルム比較（論文 Theorem 4.7）

## 概要

二つの係数環で Koszul Euler 数が一致すれば、基底の全対象で評価が一致し、不変類の降下を加えると共役和が一致する（`symmetricPaperEuler_conjSum_eq`、主経路）。論文の主張の形の Theorem 4.7（`theorem_4_7`、`theorem_4_7_K0`：仮定 (4.1) と幾何ファイバーに推移的な有限群作用の下で、通常・正規化 Euler 評価の共役和の一致）と、λ-平坦性から比較と下界を得る変種を与える。

## 方針

共通定理 `homologicalEulerK0_pullback_conjSum_eq_of_base_formula` を使う。群は評価元の K₀ にのみ作用し、係数代数や長さの同変性は要求しない。

## 規約

補題 4.6 と定理 3.1 の帰結は `supportedRankK0_descent` という一つの未証明入力（`SupportedDescent`）。ひねりは自己同型に沿った係数拡大。

## 使われ方

Paper/Section5/SecondComparison。
-/

@[expose] public noncomputable section

universe u

section SymmetricComparisonPart

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Section4

open CategoryTheory IsLocalRing Filter Asymptotic

variable {A S C D : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [HasDerivedCategory (ModuleCat.{u} A)]
  [CommRing S] [Nontrivial S] [CommRing C] [Nontrivial C] [CommRing D] [Nontrivial D]
  (α : A →+* S) (φ : S →+* C) (ψ : S →+* D)
  {J : Ideal C} {I : Ideal D} (lam : NormalizedLength C J) (mu : NormalizedLength D I)
  (hfg : J.FG) (hIfg : I.FG) {e : ℕ} (z : Fin e → A)
  (hJ : J ≤ (Ideal.span (Set.range (φ ∘ α ∘ z))).radical)
  (hI : I ≤ (Ideal.span (Set.range (ψ ∘ α ∘ z))).radical)
  (hfin : LengthAlgebra.KoszulFinite lam (φ ∘ α ∘ z))
  (hfinD : LengthAlgebra.KoszulFinite mu (ψ ∘ α ∘ z))
  (hz : Ideal.span (Set.range z) = maximalIdeal A) (hK : IsKoszulResolution z)
  {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

include hz hK

set_option maxHeartbeats 800000 in
-- 二段階の係数変更と、各係数環上の長さの局所化の型の比較に必要。
/-- 二段階の係数変更をした評価も、任意の Koszul Euler 数を係数とする。 -/
theorem paperBaseChangeEulerK0_eq_koszulEuler_mul :
    (paperBaseChangeEulerK0 φ (α ∘ z) lam hfg hJ hfin U hU hs).comp
      (TriangulatedK0.map (paperSupportedChangeRing α z)) =
        LengthAlgebra.koszulEuler lam (φ ∘ α ∘ z) •
          ordinaryPaperEulerK0 z (isArtinianRing_quotient_span_of_eq hz) U hU hs := by
  dsimp only [paperBaseChangeEulerK0]
  rw [AddMonoidHom.comp_assoc, paperSupportedChangeRingK0_comp]
  exact koszulPaperEulerK0_changeRing (φ.comp α) lam hfg z hJ hfin hz hK U hU hs

set_option maxHeartbeats 800000 in
-- 異なる二つの係数環の評価と、基底公式の比較に余裕を与える。
/-- 有限版と同じ対称な比較。全ての K₀ 類を扱い、係数環の高次消滅は仮定しない。 -/
theorem symmetricPaperEuler_conjSum_eq
    {G : Type*} [Group G] [Fintype G]
    [DistribMulAction G (TriangulatedK0 (paperSupportedRank (s := s) (α ∘ z)).FullSubcategory)]
    (hc : LengthAlgebra.koszulEuler lam (φ ∘ α ∘ z) =
      LengthAlgebra.koszulEuler mu (ψ ∘ α ∘ z))
    (hdesc : ∀ y : TriangulatedK0 (paperSupportedRank (s := s) (α ∘ z)).FullSubcategory,
      (∀ g : G, g • y = y) → ∃ (n : ℕ)
        (x : TriangulatedK0 (paperSupportedRank (s := s) z).FullSubcategory),
        0 < n ∧ n • y = TriangulatedK0.map (paperSupportedChangeRing α z) x)
    (y : TriangulatedK0 (paperSupportedRank (s := s) (α ∘ z)).FullSubcategory) :
    ∑ g : G, paperBaseChangeEulerK0 φ (α ∘ z) lam hfg hJ hfin U hU hs (g • y) =
      ∑ g : G, paperBaseChangeEulerK0 ψ (α ∘ z) mu hIfg hI hfinD U hU hs (g • y) := by
  have hC := paperBaseChangeEulerK0_eq_koszulEuler_mul α φ lam hfg z hJ hfin hz hK U hU hs
  have hD := paperBaseChangeEulerK0_eq_koszulEuler_mul α ψ mu hIfg z hI hfinD hz hK U hU hs
  -- 共通定理の適用。評価は完備化した商の上の Euler 評価を、係数変更と比較同値で引き戻したもの
  simp only [paperBaseChangeEulerK0, paperRankEulerK0, AddMonoidHom.comp_assoc]
  exact homologicalEulerK0_pullback_conjSum_eq_of_base_formula _ _ _ _ _ _ _ _ _ _ _ _
    ((TriangulatedK0.map (paperSupportedRankEquivalence (s := s) (φ ∘ α ∘ z)).functor).comp
      (TriangulatedK0.map (paperSupportedChangeRing (s := s) φ (α ∘ z))))
    ((TriangulatedK0.map (paperSupportedRankEquivalence (s := s) (ψ ∘ α ∘ z)).functor).comp
      (TriangulatedK0.map (paperSupportedChangeRing (s := s) ψ (α ∘ z))))
    (TriangulatedK0.map (paperSupportedChangeRing α z))
    (fun x ↦ ordinaryPaperEulerK0 z (isArtinianRing_quotient_span_of_eq hz) U hU hs x)
    (LengthAlgebra.koszulEuler lam (φ ∘ α ∘ z)) (LengthAlgebra.koszulEuler mu (ψ ∘ α ∘ z))
    (fun x ↦ by
      have := DFunLike.congr_fun hC x
      simp only [paperBaseChangeEulerK0, paperRankEulerK0, completedRankEulerK0,
        AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, smul_eq_mul] at this
      exact this)
    (fun x ↦ by
      have := DFunLike.congr_fun hD x
      simp only [paperBaseChangeEulerK0, paperRankEulerK0, completedRankEulerK0,
        AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, smul_eq_mul] at this
      exact this)
    hc hdesc y

end SerrePositivity.Section4

end SymmetricComparisonPart

section Theorem4_7Part

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Section4

open CategoryTheory IsLocalRing Filter Asymptotic
open scoped ENNReal

variable {A T C : Type u} [CommRing A] [IsRegularLocalRing A]
  [hderived : HasDerivedCategory (ModuleCat.{u} A)]
  [CommRing T] [IsLocalRing T] [IsDomain T] [Algebra A T] [Module.Finite A T]
  [CommRing C] [Algebra T C]
  {e : ℕ} (z : Fin e → A)
  (lam : NormalizedLength C ((maximalIdeal A).map
    ((algebraMap T C).comp (algebraMap A T))))
  (hz : Ideal.span (Set.range z) = maximalIdeal A)
  (hdim : ringKrullDim A = e)
  (hres : Function.Surjective ((residue T).comp (algebraMap A T)))
  (hzero : ∀ v : ℕ, 0 < v → ∀ j : ℕ, 0 < j →
    lam.len (koszulHomologySelf (fun k ↦ (algebraMap T C (algebraMap A T (z k))) ^ v) j) = 0)
  (hquot : ∀ v : ℕ, 0 < v →
    lam.len (C ⧸ Ideal.span (Set.range fun k ↦ (algebraMap T C (algebraMap A T (z k))) ^ v)) =
      ((v ^ e * Module.finrank A T : ℕ) : ℝ≥0∞))
  {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
  (G : Type u) [Group G] [Fintype G] [MulSemiringAction G T] [SMulCommClass G A T]
  (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A T)))
  (htrans : IsGeometricallyTransitive A T G)

include hquot hsurj in
omit hderived [IsLocalRing T] in
/-- §4 の商の長さの公式から C の非自明性を得る。
評価の構成で必要な型クラスを供給し、定理4.7の追加仮定にはしない。 -/
lemma section4_nontrivial : Nontrivial C := by
  let : IsDomain A := isDomain_of_isRegularLocalRing A
  exact nontrivial_of_section4_quotient lam _ hsurj
    (quotient_length_of_lengthAlgebra_values lam _ (Module.finrank A T) hquot)

set_option maxHeartbeats 800000 in
-- 一般の対称比較を、通常の評価と合成された係数変更の評価に特殊化する。
include hdim hres p hsurj htrans hderived in
/-- 定理4.7の K₀ 版。通常長さと λ の Koszul Euler 数の一致を確認し、
対称な共通比較に降下の引用を渡す。正の冪だけで足り、`0 < e` は不要。 -/
theorem theorem_4_7_K0
    (y : TriangulatedK0 (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory) :
    let : Nontrivial C := section4_nontrivial z lam hquot hsurj
    let : IsNoetherianRing T := IsNoetherianRing.of_finite A T
    let hfin := koszulFinite_of_lengthAlgebra_values lam
      (algebraMap T C ∘ algebraMap A T ∘ z) (Module.finrank A T) hzero hquot
    ∑ g : G, ordinaryPaperEulerK0 (algebraMap A T ∘ z)
      (isArtinianRing_quotient_span_of_finite A T z
        (by rw [hz]; exact (maximalIdeal.isMaximal A).isPrime.radical)) U hU hs (g • y) =
      ∑ g : G, paperBaseChangeEulerK0 (algebraMap T C) (algebraMap A T ∘ z) lam
        (LengthAlgebra.parameterIdeal_fg ((algebraMap T C).comp (algebraMap A T)))
        (LengthAlgebra.parameterIdeal_support ((algebraMap T C).comp (algebraMap A T)) z hz)
        hfin U hU hs (g • y) := by
  let : Nontrivial C := section4_nontrivial z lam hquot hsurj
  let : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  have hArt := isArtinianRing_quotient_span_of_finite A T z
    (by rw [hz]; exact (maximalIdeal.isMaximal A).isPrime.radical)
  have hK : IsKoszulResolution z := isKoszulResolution_of_isWeaklyRegular z
    (isWeaklyRegular_of_span_eq_maximalIdeal A z hz hdim)
  have hc : LengthAlgebra.koszulEuler (NormalizedLength.ordinary T) (algebraMap A T ∘ z) =
      LengthAlgebra.koszulEuler lam (algebraMap T C ∘ algebraMap A T ∘ z) := by
    apply Eq.trans ?_ (koszulEuler_of_lengthAlgebra_values lam
      (algebraMap T C ∘ algebraMap A T ∘ z) (Module.finrank A T) hzero hquot).symm
    rw [ordinary_koszulEuler_eq_koszulEulerChar z hres,
      koszulEulerChar_eq_finrank A T z hz hdim]
  have he := symmetricPaperEuler_conjSum_eq (algebraMap A T) (RingHom.id T) (algebraMap T C)
    (NormalizedLength.ordinary T) lam Submodule.fg_bot
    (LengthAlgebra.parameterIdeal_fg ((algebraMap T C).comp (algebraMap A T))) z bot_le
    (LengthAlgebra.parameterIdeal_support ((algebraMap T C).comp (algebraMap A T)) z hz)
    (fun v _ i ↦ ordinary_koszul_pow_finite (algebraMap A T ∘ z) v i)
    (koszulFinite_of_lengthAlgebra_values lam _ (Module.finrank A T) hzero hquot)
    hz hK U hU hs hc (supportedRankK0_descent A T p z hz s hs G hsurj htrans) y
  rw [paperBaseChangeEulerK0_id] at he
  exact he

include hdim hres p hsurj htrans hderived in
/-- 定理4.7：論文の支持圏の対象について、二つの Euler 評価の共役和は一致する。
K₀ 版を対象の類へ適用する。既存の降下と正則パラメータは証明済みで、保留した降下への依存は残る。 -/
theorem theorem_4_7
    (X : (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory) :
    let : Nontrivial C := section4_nontrivial z lam hquot hsurj
    let : IsNoetherianRing T := IsNoetherianRing.of_finite A T
    let hfin := koszulFinite_of_lengthAlgebra_values lam
      (algebraMap T C ∘ algebraMap A T ∘ z) (Module.finrank A T) hzero hquot
    ∑ g : G, ordinaryPaperEulerK0 (algebraMap A T ∘ z)
      (isArtinianRing_quotient_span_of_finite A T z
        (by rw [hz]; exact (maximalIdeal.isMaximal A).isPrime.radical)) U hU hs
        (TriangulatedK0.mk ((paperTwist z g).obj X)) =
      ∑ g : G, paperBaseChangeEulerK0 (algebraMap T C) (algebraMap A T ∘ z) lam
        (LengthAlgebra.parameterIdeal_fg ((algebraMap T C).comp (algebraMap A T)))
        (LengthAlgebra.parameterIdeal_support ((algebraMap T C).comp (algebraMap A T)) z hz)
        hfin U hU hs (TriangulatedK0.mk ((paperTwist z g).obj X)) := by
  let : Nontrivial C := section4_nontrivial z lam hquot hsurj
  simpa only [paperK0_smul_mk] using theorem_4_7_K0 z lam hz hdim hres hzero hquot
    U hU hs p G hsurj htrans (TriangulatedK0.mk X)

end SerrePositivity.Section4

end Theorem4_7Part

section FlatRealizationPart

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Section4

open CategoryTheory CategoryTheory.Limits IsLocalRing Filter Asymptotic LengthAlgebra

open scoped ENNReal

section lower

variable {A S C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing S] [Nontrivial S] [CommRing C] [Nontrivial C]
  (α : A →+* S) (φ : S →+* C) (lam : NormalizedLength C ((maximalIdeal A).map (φ.comp α)))
  (hfg : ((maximalIdeal A).map (φ.comp α)).FG) {e : ℕ} (z : Fin e → A)
  (hJ : (maximalIdeal A).map (φ.comp α) ≤ (Ideal.span (Set.range (φ ∘ α ∘ z))).radical)
  (hz : Ideal.span (Set.range z) = maximalIdeal A)
  (hreg : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn z))
  (hflat : ∀ (V : Type u) [AddCommGroup V] [Module A V], IsFiniteLength A V →
    ∀ i : ℕ, 0 < i → lam.len (TorAlg (φ.comp α) i V) = 0)
  (r : ℝ≥0∞) (hr : r ≠ ⊤) (hrank : lam.len (TorAlg (φ.comp α) 0 (A ⧸ maximalIdeal A)) = r)
  {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

set_option maxHeartbeats 800000 in
-- 二段階の係数変更とランク商の評価の依存型を比較するため。
/-- λ-平坦性から、ランク商のホモロジーが指定された範囲外で零対象となる。 -/
theorem paperBaseChangeHomology_vanishing_of_flat
    (K : CochainComplex (FreeSequence S s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank (α ∘ z) ((paperSequenceFunctor S s).obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, α (z j) ^ v • 𝟙 ((paperSequenceFunctor S s).obj (sequenceHomotopyObj K hK)) = 0)
    (a b : ℤ)
    (hbound : ∀ t q, q < a ∨ b < q → IsZero (((evaluateComplex t).obj K).X q))
    (q : ℤ) (hq : q < a + e ∨ b < q) :
    IsZero ((paperBaseChangeHomology φ (α ∘ z) lam hfg hJ
      (koszulFinite_of_flat (φ.comp α) lam z hz hreg hflat r hr hrank) U hU hs q).obj
      ⟨(paperSequenceFunctor S s).obj (sequenceHomotopyObj K hK), h⟩) :=
  paperBaseChangeHomology_vanishing φ (α ∘ z) lam hfg hJ
    (koszulFinite_of_flat (φ.comp α) lam z hz hreg hflat r hr hrank) U hU hs K hK h v hv hx
    (koszulAcyclic_of_flat (φ.comp α) lam z hz hreg hflat v hv) a b hbound q hq

set_option maxHeartbeats 800000 in
-- 二段階の係数変更とランク商の評価の依存型を比較するため。
/-- 有限長加群の Tor 条件からランク商の消滅・極小 Euler 下界へ接続する。 -/
theorem paperBaseChangeEuler_minimal_lower_bound_of_flat
    (K : CochainComplex (FreeSequence S s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank (α ∘ z) ((paperSequenceFunctor S s).obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, α (z j) ^ v • 𝟙 ((paperSequenceFunctor S s).obj (sequenceHomotopyObj K hK)) = 0)
    (hbound : ∀ t q, q < -(e : ℤ) ∨ 0 < q → IsZero (((evaluateComplex t).obj K).X q))
    (I : Ideal S) (Q : Ideal C) (hIQ : ∀ a ∈ I, φ a ∈ Q)
    (hQ : IsPowTorsion ((maximalIdeal A).map (φ.comp α)) (C ⧸ Q))
    (hmin : ∀ t (m : Fin ((K.X (-1)).rank t) → S) j, (K.d (-1) 0 t m) j ∈ I)
    (hzI : ∀ j, α (z j) ^ v ∈ I) :
    (lam.len (C ⧸ Q)).toReal * normalizedLimit U s (fun t ↦ ((K.X 0).rank t : ℝ)) ≤
      paperBaseChangeEulerK0 φ (α ∘ z) lam hfg hJ
        (koszulFinite_of_flat (φ.comp α) lam z hz hreg hflat r hr hrank) U hU hs
        (TriangulatedK0.mk ⟨(paperSequenceFunctor S s).obj (sequenceHomotopyObj K hK), h⟩) :=
  paperBaseChangeEuler_minimal_lower_bound φ (α ∘ z) lam hfg hJ
    (koszulFinite_of_flat (φ.comp α) lam z hz hreg hflat r hr hrank) U hU hs K hK h v hv hx
    (koszulAcyclic_of_flat (φ.comp α) lam z hz hreg hflat v hv) hbound I Q hIQ hQ hmin hzI

end lower

section comparison

variable {A S C D : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [HasDerivedCategory (ModuleCat.{u} A)]
  [CommRing S] [Nontrivial S] [CommRing C] [Nontrivial C] [CommRing D] [Nontrivial D]
  (α : A →+* S) (φ : S →+* C) (ψ : S →+* D)
  (lam : NormalizedLength C ((maximalIdeal A).map (φ.comp α)))
  (mu : NormalizedLength D ((maximalIdeal A).map (ψ.comp α)))
  (hfg : ((maximalIdeal A).map (φ.comp α)).FG)
  (hIfg : ((maximalIdeal A).map (ψ.comp α)).FG)
  {e : ℕ} (z : Fin e → A)
  (hJ : (maximalIdeal A).map (φ.comp α) ≤ (Ideal.span (Set.range (φ ∘ α ∘ z))).radical)
  (hI : (maximalIdeal A).map (ψ.comp α) ≤ (Ideal.span (Set.range (ψ ∘ α ∘ z))).radical)
  (hz : Ideal.span (Set.range z) = maximalIdeal A)
  (hreg : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn z))
  (hflatC : ∀ (V : Type u) [AddCommGroup V] [Module A V], IsFiniteLength A V →
    ∀ i : ℕ, 0 < i → lam.len (TorAlg (φ.comp α) i V) = 0)
  (hflatD : ∀ (V : Type u) [AddCommGroup V] [Module A V], IsFiniteLength A V →
    ∀ i : ℕ, 0 < i → mu.len (TorAlg (ψ.comp α) i V) = 0)
  (r : ℝ≥0∞) (hr : r ≠ ⊤)
  (hrankC : lam.len (TorAlg (φ.comp α) 0 (A ⧸ maximalIdeal A)) = r)
  (hrankD : mu.len (TorAlg (ψ.comp α) 0 (A ⧸ maximalIdeal A)) = r)
  {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

set_option maxHeartbeats 800000 in
-- 二段階の係数変更とランク商の評価の依存型を比較するため。
/-- 同じ有限ランクの λ-平坦代数の評価は、ランク商でも共役和が一致する。 -/
theorem symmetricPaperEuler_conjSum_eq_of_flat
    {G : Type*} [Group G] [Fintype G]
    [DistribMulAction G (TriangulatedK0 (paperSupportedRank (s := s) (α ∘ z)).FullSubcategory)]
    (hdesc : ∀ y : TriangulatedK0 (paperSupportedRank (s := s) (α ∘ z)).FullSubcategory,
      (∀ g : G, g • y = y) → ∃ (n : ℕ)
        (x : TriangulatedK0 (paperSupportedRank (s := s) z).FullSubcategory),
        0 < n ∧ n • y = TriangulatedK0.map (paperSupportedChangeRing α z) x)
    (y : TriangulatedK0 (paperSupportedRank (s := s) (α ∘ z)).FullSubcategory) :
    ∑ g : G, paperBaseChangeEulerK0 φ (α ∘ z) lam hfg hJ
      (koszulFinite_of_flat (φ.comp α) lam z hz hreg hflatC r hr hrankC) U hU hs (g • y) =
    ∑ g : G, paperBaseChangeEulerK0 ψ (α ∘ z) mu hIfg hI
      (koszulFinite_of_flat (ψ.comp α) mu z hz hreg hflatD r hr hrankD) U hU hs (g • y) := by
  apply symmetricPaperEuler_conjSum_eq α φ ψ lam mu hfg hIfg z hJ hI _ _ hz
    (isKoszulResolution_of_isWeaklyRegular z hreg) U hU hs _ hdesc y
  exact (koszulEuler_of_flat (φ.comp α) lam z hz hreg hflatC r hr hrankC).trans
    (koszulEuler_of_flat (ψ.comp α) mu z hz hreg hflatD r hr hrankD).symm

end comparison

end SerrePositivity.Section4

end FlatRealizationPart

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Paper "Prop 4.5" (partial := component) "仮定：台付きランク商、A の正則パラメータと (4.1) の長さ条件（原典の正規化長側。Lean は有限性の引数を明示）。結論：商内の冪等元による直和因子も含む K₀ 類について、係数拡大後の正規化 Euler 評価は A の通常評価の階数倍（原典の正規化長側）。"] _root_.SerrePositivity.Section4.paperBaseChangeEulerK0_eq_koszulEuler_mul
