module

public import SerrePositivity.KST.DerivedBlowup.ExteriorAugmentationDGComparison
public import SerrePositivity.KST.DerivedBlowup.UniversalCanonicalAugmentation
public import SerrePositivity.KST.DerivedBlowup.ChartBaseChangeDGFunctor

/-!
概要：KST Def3.1・Lemma3.6 の普遍チャートの外積 dg 模型と通常の環の局所 dg 準同値。
方針：既存 DerivedChartObject から空 Koszul の係数制限へ標準添加関手を取る。
規約：空 Koszul の Hom は通常のチャート環の次数0単一複体と同型。
使われ方：普遍 blowup の通常チャートから導来底変更する局所 dg 模型の根拠。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Limits

variable {r : ℕ}

/-- 概要：ChartIndex で添字付けした普遍チャートの生成元微分。
方針：全普遍チャート関係式の自由線形結合を使う。
規約：KST Def3.1、既存 DerivedChartObject の微分と同じ。
使われ方：普遍チャートの dg 解消。 -/
abbrev universalChartDifferential (i : Fin (r + 1)) :=
  Finsupp.linearCombination (ChartRing (UniversalBase (Fin (r + 1))) i) (universalRelation i)

/-- 概要：チャート添字による微分像は関係式イデアル。
方針：自由線形結合の像の一般公式を使う。
規約：KST Def3.1。使われ方：H⁰ 商の係数代数同型。 -/
theorem universalChartDifferential_range (i : Fin (r + 1)) :
    LinearMap.range (universalChartDifferential i) = universalRelationIdeal i :=
  Finsupp.range_linearCombination _

/-- 概要：普遍チャートの微分像商は通常のチャート環と係数代数同型。
方針：微分像の計算を普遍商表示に合成する。
規約：KST Def3.1。使われ方：標準添加射の H⁰ 比較。 -/
def universalChartDifferentialQuotientEquiv (i : Fin (r + 1)) :
    letI := (universalPresentationMap i).toAlgebra
    (ChartRing (UniversalBase (Fin (r + 1))) i ⧸
      LinearMap.range (universalChartDifferential i)) ≃ₐ[
        ChartRing (UniversalBase (Fin (r + 1))) i] UniversalChart i := by
  letI := (universalPresentationMap i).toAlgebra
  apply AlgEquiv.ofRingEquiv (f :=
    (Ideal.quotEquivOfEq (universalChartDifferential_range i)).trans
      (universalPresentationEquiv i))
  intro p
  change universalPresentationEquiv i
    ((Ideal.quotEquivOfEq (universalChartDifferential_range i)) (Ideal.Quotient.mk _ p)) = _
  rw [Ideal.quotEquivOfEq_mk]
  rfl

/-- 概要：通常の普遍チャートで生成元微分が零となる。
方針：微分像商での零を明示的な係数代数同型で移す。
規約：KST Def3.1。使われ方：標準添加 dg 関手の定義。 -/
theorem universalChartDifferential_zero (i : Fin (r + 1)) :
    ∀ m, universalPresentationMap i (universalChartDifferential i m) = 0 := by
  let := (universalPresentationMap i).toAlgebra
  intro m
  change algebraMap _ (UniversalChart i) _ = 0
  rw [← (universalChartDifferentialQuotientEquiv i).commutes,
    exteriorDifferential_quotient_zero, map_zero]

/-- 概要：普遍チャートの ChartIndex 外積模型は非零次数でホモロジーが零。
方針：既存チャート複体比較で普遍正則列の解消性を移す。
規約：KST Lemma3.6。使われ方：添加 dg 関手の各 Hom の擬同型性。 -/
theorem universalChartExterior_homology_isZero (i : Fin (r + 1))
    (q : ℤ) (hq : q ≠ 0) :
    IsZero ((exteriorKoszulCochain (universalChartDifferential i)).homology q) :=
  ((universalChartSequence_isKoszulResolution i).isZero q hq).of_iso
    (HomologicalComplex.homologyMapIso
      (derivedChartExteriorIso (R := UniversalBase (Fin (r + 1))) MvPolynomial.X i) q).symm

/-- 概要：普遍 DerivedChartObject から通常のチャートの空 Koszul 模型への dg 関手。
方針：標準添加 dg 関手を既存のチャート対象型に直接適用する。
規約：KST Def3.1・Lemma3.6。使われ方：普遍局所模型の dg 比較。 -/
def universalChartAugmentationDGFunctor (i : Fin (r + 1)) :
    letI := (universalPresentationMap i).toAlgebra
    DifferentialGraded.DGFunctor (ChartRing (UniversalBase (Fin (r + 1))) i)
      (DerivedChartObject (R := UniversalBase (Fin (r + 1))) MvPolynomial.X i)
      (DifferentialGraded.ScalarExtension.DGRestriction (universalPresentationMap i)
        (EmptyKoszulObject (UniversalChart i))) := by
  letI := (universalPresentationMap i).toAlgebra
  exact exteriorAugmentationDGFunctor _ _ (universalChartDifferential_zero i)

/-- 概要：普遍チャートの標準添加 dg 関手は準同値。
方針：標準 H⁰ 商同型と非零次数消滅により各 Hom の擬同型性を示す。
規約：KST Lemma3.6。使われ方：通常の普遍 blowup の局所 dg 解消。 -/
theorem universalChartAugmentationDGFunctor_quasiEquivalence (i : Fin (r + 1)) :
    letI := (universalPresentationMap i).toAlgebra
    DifferentialGraded.QuasiEquivalence (universalChartAugmentationDGFunctor i) := by
  let := (universalPresentationMap i).toAlgebra
  apply exteriorAugmentationDGFunctor_quasiEquivalence
  exact exteriorKoszulAugmentation_quasiIso_of_quotient _
    (universalChartDifferential_zero i) (universalChartDifferentialQuotientEquiv i)
    (universalChartExterior_homology_isZero i)

end SerrePositivity.KST.DerivedBlowup
