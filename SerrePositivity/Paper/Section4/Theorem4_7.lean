module

public import SerrePositivity.Paper.Section4.NormComparison
public import SerrePositivity.Paper.Section4.SupportedDescent
public import SerrePositivity.Paper.Section4.LengthHypotheses
public import SerrePositivity.Inputs.RegularLocalRing

/-!
# 定理4.7：漸近ノルム比較

## 主張

§4 の環 A、有限局所整域 T、T 代数 C と長さ関数 λ を抽象的に与える。
仮定 (4.1) と幾何ファイバーに推移的な有限群作用の下で、論文の支持圏の
任意の対象について、通常・正規化 Euler 評価の共役和が一致する。
λ の不変性や C の群作用、§2の具体的な構成は仮定しない。

## 依存と規約

補題4.6と定理3.1の帰結は `supportedRankK0_descent` という一つの未証明入力。
正則パラメータの正則性も既存の名前付き未証明入力に依存する。
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
  [CommRing C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
  {e : ℕ} (z : Fin e → A)
  (lam : NormalizedLength C ((maximalIdeal A).map (algebraMap A C)))
  (hz : Ideal.span (Set.range z) = maximalIdeal A)
  (hdim : ringKrullDim A = e) (he : 0 < e)
  (hres : Function.Surjective ((residue T).comp (algebraMap A T)))
  (hzero : ∀ v : ℕ, 0 < v → ∀ j : ℕ, 0 < j →
    lam.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) = 0)
  (hquot : ∀ v : ℕ, 0 < v →
    lam.len (C ⧸ Ideal.span (Set.range fun k ↦ algebraMap A C (z k ^ v))) =
      ((v ^ e * Module.finrank A T : ℕ) : ℝ≥0∞))
  {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
  (G : Type u) [Group G] [Fintype G] [MulSemiringAction G T] [SMulCommClass G A T]
  (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A T)))
  (htrans : IsGeometricallyTransitive A T G)

include hquot hsurj in
omit hderived [IsLocalRing T] [Algebra T C] [IsScalarTower A T C] in
/-- §4 の商の長さの公式から C の非自明性を得る。
評価の構成で必要な型クラスを供給し、定理4.7の追加仮定にはしない。 -/
lemma section4_nontrivial : Nontrivial C := by
  let : IsDomain A := isDomain_of_isRegularLocalRing A
  have hone : (fun k : Fin e ↦ algebraMap A C (z k ^ 1)) = algebraMap A C ∘ z := by
    funext k
    simp
  have hq := hquot 1 one_pos
  rw [hone, one_pow, one_mul] at hq
  exact nontrivial_of_section4_quotient lam _ hsurj hq

include hdim hres p hsurj htrans hderived in
/-- 定理4.7の K₀ 版。仮定 (4.1) から有限性を供給し、降下と命題4.5を適用する。
全ての K₀ 類で共役和が一致し、個々の類での評価の一致は仮定しない。 -/
theorem theorem_4_7_K0
    (y : TriangulatedK0 (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory) :
    let : Nontrivial C := section4_nontrivial z lam hquot hsurj
    let hfin := koszul_finite_of_section4 lam z he (Module.finrank A T) hzero hquot
    ∑ g : G, ordinaryPaperEulerOnT z hz U hU hs (g • y) =
      ∑ g : G, normalizedPaperEulerOnT z lam hz hfin U hU hs (g • y) := by
  let : Nontrivial C := section4_nontrivial z lam hquot hsurj
  let hfin := koszul_finite_of_section4 lam z he (Module.finrank A T) hzero hquot
  have hK : IsKoszulResolution z := isKoszulResolution_of_isWeaklyRegular z
    (isWeaklyRegular_of_span_eq_maximalIdeal A z hz hdim)
  have hone : (fun k : Fin e ↦ algebraMap A C (z k ^ 1)) = algebraMap A C ∘ z := by
    funext k
    simp
  have hkz := hzero 1 one_pos
  rw [hone] at hkz
  have hq := hquot 1 one_pos
  rw [hone, one_pow, one_mul] at hq
  exact normComparison_of_descent z lam hz hfin U hU hs hK hres
    (koszulEulerChar_eq_finrank A T z hz hdim) hkz hq G
    (supportedRankK0_descent A T p z hz s hs G hsurj htrans) y

include hdim hres p hsurj htrans hderived in
/-- 定理4.7：論文の支持圏の任意の対象について、二つの Euler 評価の共役和は一致する。
補題4.6と定理3.1の帰結、および既存の正則パラメータの入力に依存する。 -/
theorem theorem_4_7
    (X : (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory) :
    let : Nontrivial C := section4_nontrivial z lam hquot hsurj
    let hfin := koszul_finite_of_section4 lam z he (Module.finrank A T) hzero hquot
    ∑ g : G, ordinaryPaperEulerOnT z hz U hU hs
        (TriangulatedK0.mk ((paperTwist z g).obj X)) =
      ∑ g : G, normalizedPaperEulerOnT z lam hz hfin U hU hs
        (TriangulatedK0.mk ((paperTwist z g).obj X)) := by
  let : Nontrivial C := section4_nontrivial z lam hquot hsurj
  simpa only [paperK0_smul_mk] using theorem_4_7_K0 z lam hz hdim he hres hzero hquot
    U hU hs p G hsurj htrans (TriangulatedK0.mk X)

end SerrePositivity.Section4
