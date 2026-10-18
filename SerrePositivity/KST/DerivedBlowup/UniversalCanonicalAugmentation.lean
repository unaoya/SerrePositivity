module

public import SerrePositivity.KST.DerivedBlowup.ExteriorAugmentationNaturality
public import SerrePositivity.KST.DerivedBlowup.UniversalKoszulResolution
public import SerrePositivity.KST.DerivedBlowup.KoszulConeComparison

/-!
概要：KST Def3.1・Lemma3.6 の普遍チャートの標準添加射の解消性。
方針：有限関係式列の弱正則性で高次を消し、標準 H⁰ 計算と明示的商表示を使う。
規約：生成元を零へ送る添加射であり、既存解消定理の選択付き添加射は使わない。
使われ方：普遍チャート Koszul 模型と通常の普遍チャートとの標準比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Limits

variable {r : ℕ}

/-- 概要：普遍有限関係式列を生成加群から係数環へ送る微分。
方針：既存チャート列の線形結合を使う。
規約：KST Def3.1。使われ方：標準添加射の外積模型。 -/
abbrev universalSequenceDifferential (i : Fin (r + 1)) :=
  Finsupp.linearCombination (ChartRing (UniversalBase (Fin (r + 1))) i)
    (chartKoszulSequence (R := UniversalBase (Fin (r + 1))) MvPolynomial.X i)

/-- 概要：普遍微分の像は全チャート関係式イデアルに等しい。
方針：自由生成加群の線形結合の像と有限列の生成イデアルを比較する。
規約：KST Def3.1。使われ方：標準 H⁰ 商の環表示。 -/
theorem universalSequenceDifferential_range (i : Fin (r + 1)) :
    LinearMap.range (universalSequenceDifferential i) = universalRelationIdeal i := by
  rw [Finsupp.range_linearCombination]
  exact universalChartSequence_ideal i

/-- 概要：微分像の商と通常の普遍チャートの係数代数同型。
方針：微分像の計算を関係式商同型へ合成し、係数での可換性を検証する。
規約：KST Def3.1。使われ方：標準添加射の解消性の目標。 -/
def universalSequenceDifferentialQuotientEquiv (i : Fin (r + 1)) :
    letI := (universalPresentationMap i).toAlgebra
    (ChartRing (UniversalBase (Fin (r + 1))) i ⧸
      LinearMap.range (universalSequenceDifferential i)) ≃ₐ[
        ChartRing (UniversalBase (Fin (r + 1))) i] UniversalChart i := by
  letI := (universalPresentationMap i).toAlgebra
  let e := (Ideal.quotEquivOfEq (universalSequenceDifferential_range i)).trans
    (universalPresentationEquiv i)
  apply AlgEquiv.ofRingEquiv (f := e)
  intro p
  change universalPresentationEquiv i
    ((Ideal.quotEquivOfEq (universalSequenceDifferential_range i))
      (Ideal.Quotient.mk _ p)) = _
  rw [Ideal.quotEquivOfEq_mk]
  rfl

/-- 概要：普遍チャート環で微分の値は零となる。
方針：微分像の商での消滅を係数代数同型で移す。
規約：KST Def3.1。使われ方：通常のチャートへの標準添加射。 -/
theorem universalSequenceDifferential_zero (i : Fin (r + 1)) :
    letI := (universalPresentationMap i).toAlgebra
    ∀ m, algebraMap _ (UniversalChart i) (universalSequenceDifferential i m) = 0 := by
  let := (universalPresentationMap i).toAlgebra
  intro m
  rw [← (universalSequenceDifferentialQuotientEquiv i).commutes]
  rw [exteriorDifferential_quotient_zero, map_zero]

/-- 概要：普遍チャートの外積 Koszul 模型の非零次数ホモロジーは零。
方針：反復 cone 模型との同型で弱正則列の解消性を移す。
規約：KST Lemma3.6。使われ方：標準添加射の擬同型性。 -/
theorem universalSequenceExterior_homology_isZero (i : Fin (r + 1))
    (q : ℤ) (hq : q ≠ 0) :
    IsZero ((exteriorKoszulCochain (universalSequenceDifferential i)).homology q) :=
  ((universalChartSequence_isKoszulResolution i).isZero q hq).of_iso
    (HomologicalComplex.homologyMapIso
      (koszulExteriorIso (chartKoszulSequence
        (R := UniversalBase (Fin (r + 1))) MvPolynomial.X i)) q).symm

/-- 概要：普遍チャートの外積 Koszul 模型から通常のチャートへの標準添加射。
方針：外積生成元を零へ送り、係数に普遍チャート代入を使う。
規約：KST Def3.1、H⁰ 同型の選択を含まない。
使われ方：普遍チャートの dg 代数比較の underlying 鎖写像。 -/
def universalCanonicalAugmentation (i : Fin (r + 1)) :
    letI := (universalPresentationMap i).toAlgebra
    exteriorKoszulCochain (universalSequenceDifferential i) ⟶
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of (ChartRing (UniversalBase (Fin (r + 1))) i) (UniversalChart i)) := by
  letI := (universalPresentationMap i).toAlgebra
  exact exteriorKoszulAugmentation _ (universalSequenceDifferential_zero i)

/-- 概要：普遍チャートの標準添加射は擬同型。
方針：標準 H⁰ 商同型と高次ホモロジー消滅を一般の添加射定理へ渡す。
規約：KST Lemma3.6。使われ方：普遍チャートからの導来底変更の基礎。 -/
instance universalCanonicalAugmentation_quasiIso (i : Fin (r + 1)) :
    letI := (universalPresentationMap i).toAlgebra
    QuasiIso (universalCanonicalAugmentation i) := by
  let := (universalPresentationMap i).toAlgebra
  exact exteriorKoszulAugmentation_quasiIso_of_quotient _
    (universalSequenceDifferential_zero i) (universalSequenceDifferentialQuotientEquiv i)
    (universalSequenceExterior_homology_isZero i)

end SerrePositivity.KST.DerivedBlowup
