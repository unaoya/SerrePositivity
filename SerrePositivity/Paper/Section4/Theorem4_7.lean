module

public import SerrePositivity.LengthAlgebra.OrdinaryKoszulEuler

public import SerrePositivity.Paper.Section4.SymmetricComparison
public import SerrePositivity.Paper.Section4.LengthAlgebraRealization
public import SerrePositivity.LengthAlgebra.Flat
public import SerrePositivity.Asymptotic.PaperComplexBaseChange
public import SerrePositivity.Paper.Section4.SupportedDescent
public import SerrePositivity.Paper.Section4.LengthHypotheses
public import SerrePositivity.CommutativeAlgebra.Koszul.RegularEuler

/-!
# 定理4.7：漸近ノルム比較

## 主張

§4 の環 A、有限局所整域 T、T 代数 C と長さ関数 λ を抽象的に与える。
仮定 (4.1) と幾何ファイバーに推移的な有限群作用の下で、論文の支持圏の
任意の対象について、通常・正規化 Euler 評価の共役和が一致する。
λ の不変性や C の群作用、§2の具体的な構成は仮定しない。

## 依存と規約

補題4.6と定理3.1の帰結は `supportedRankK0_descent` という一つの未証明入力。
正則パラメータの正則性は証明済みの定理を使う。
このファイルに新しい `sorry` はなく、(4.1) からの有限性、階数倍公式、
共役和の群論を接続する。ひねりは自己同型に沿った係数拡大で定義する。
定理4.7の証明の完成は、これらの未証明入力に相対的な意味である。
-/

@[expose] public section

universe u

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
