module

public import SerrePositivity.KST.DerivedBlowup.UniversalRegularSequence
public import SerrePositivity.KST.DerivedBlowup.UniversalPresentationEquiv
public import SerrePositivity.KST.DerivedBlowup.ChartComplexes

/-!
概要：KST Def3.1・Lemma3.6 の普遍チャート Koszul 複体の解消性。
方針：pivot を除く有限列挙に一般の弱正則性を適用し、関係式商を自由チャートと比較する。
規約：ここでの添加射は既存 IsKoszulResolution の選択した H⁰ 同型を使う複体の射。
使われ方：普遍チャートの underlying 複体の比較。cdga の標準添加射との一致は別途必要。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Limits

variable {r : ℕ}

/-- 概要：既存有限チャート列の普遍基底上での弱正則性。
方針：finSuccAboveEquiv の単射性を用いる。
規約：KST Def3.1・Lemma3.6。使われ方：普遍 Koszul 解消。 -/
theorem universalChartSequence_isWeaklyRegular (i : Fin (r + 1)) :
    RingTheory.Sequence.IsWeaklyRegular (ChartRing (UniversalBase (Fin (r + 1))) i)
      (List.ofFn (chartKoszulSequence (R := UniversalBase (Fin (r + 1))) MvPolynomial.X i)) := by
  exact universalRelation_fin_isWeaklyRegular i (finSuccAboveEquiv i)
    (finSuccAboveEquiv i).injective

/-- 概要：普遍チャートの有限関係式列は関係式商の Koszul 解消を与える。
方針：弱正則性から既存の解消定理を使う。
規約：KST Lemma3.6。使われ方：通常の普遍チャートの導来表示。 -/
theorem universalChartSequence_isKoszulResolution (i : Fin (r + 1)) :
    SerrePositivity.IsKoszulResolution
      (chartKoszulSequence (R := UniversalBase (Fin (r + 1))) MvPolynomial.X i) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (universalChartSequence_isWeaklyRegular i)

/-- 概要：有限列の生成イデアルと全チャート関係式イデアルは等しい。
方針：既存の列挙の像の等式を span に適用する。
規約：KST Def3.1。使われ方：Koszul 解消の商と通常のチャート商の比較。 -/
theorem universalChartSequence_ideal (i : Fin (r + 1)) :
    Ideal.span (Set.range
      (chartKoszulSequence (R := UniversalBase (Fin (r + 1))) MvPolynomial.X i)) =
      universalRelationIdeal i := by
  rw [chartKoszulSequence_range]
  rfl

/-- 概要：普遍チャート商の明示同型は表示環上の代数同型である。
方針：商の標準射との可換性を quotient lift の公式から示す。
規約：KST Def3.1。使われ方：複体の係数を保つ通常のチャートとの比較。 -/
def universalPresentationAlgEquiv (i : Fin (r + 1)) :
    letI := (universalPresentationMap i).toAlgebra
    UniversalPresentationQuotient i ≃ₐ[ChartRing (UniversalBase (Fin (r + 1))) i]
      UniversalChart i := by
  letI := (universalPresentationMap i).toAlgebra
  apply AlgEquiv.ofRingEquiv (f := universalPresentationEquiv i)
  intro p
  change universalQuotientToChart i (Ideal.Quotient.mk (universalRelationIdeal i) p) = _
  rfl

/-- 概要：有限列の関係式商を通常の普遍チャートへ係数線形に同定する。
方針：生成イデアルの等式による商同型と代数同型を合成する。
規約：KST Lemma3.6。使われ方：普遍 Koszul 解消の H⁰ の目標。 -/
def universalChartSequenceQuotientEquiv (i : Fin (r + 1)) :
    letI := (universalPresentationMap i).toAlgebra
    (ChartRing (UniversalBase (Fin (r + 1))) i ⧸
      Ideal.span (Set.range
        (chartKoszulSequence (R := UniversalBase (Fin (r + 1))) MvPolynomial.X i))) ≃ₗ[
        ChartRing (UniversalBase (Fin (r + 1))) i] UniversalChart i := by
  letI := (universalPresentationMap i).toAlgebra
  exact (Submodule.quotEquivOfEq _ _ (universalChartSequence_ideal i)).trans
    (universalPresentationAlgEquiv i).toLinearEquiv

/-- 概要：普遍チャート Koszul 複体の H⁰ と通常のチャート環の線形同型。
方針：既存解消の H⁰ 同型と明示的な関係式商同型を合成する。
規約：KST Lemma3.6。H⁰ 側の同型は選択を含み、代数同型とはまだ主張しない。
使われ方：underlying 複体の普遍チャート比較。 -/
def universalChartH0Iso (i : Fin (r + 1)) :
    letI := (universalPresentationMap i).toAlgebra
    (derivedChartComplex (R := UniversalBase (Fin (r + 1))) MvPolynomial.X i).homology 0 ≅
      ModuleCat.of (ChartRing (UniversalBase (Fin (r + 1))) i) (UniversalChart i) := by
  letI := (universalPresentationMap i).toAlgebra
  exact SerrePositivity.koszulH0Iso (universalChartSequence_isKoszulResolution i) ≪≫
    (universalChartSequenceQuotientEquiv i).toModuleIso

/-- 概要：普遍 Koszul 複体から通常のチャート環の単一複体への比較射。
方針：既存の選択付き添加射に明示的な商環同型を合成する。
規約：KST Lemma3.6、複体の射。積・単位との可換性はこの射から推論しない。
使われ方：underlying 複体の擬同型の供給。 -/
def universalChartComplexComparison (i : Fin (r + 1)) :
    letI := (universalPresentationMap i).toAlgebra
    derivedChartComplex (R := UniversalBase (Fin (r + 1))) MvPolynomial.X i ⟶
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of (ChartRing (UniversalBase (Fin (r + 1))) i) (UniversalChart i)) := by
  letI := (universalPresentationMap i).toAlgebra
  exact SerrePositivity.koszulAugmentation (universalChartSequence_isKoszulResolution i) ≫
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
      (universalChartSequenceQuotientEquiv i).toModuleIso.hom

/-- 概要：普遍チャート underlying 複体の比較射は擬同型。
方針：Koszul 添加射の擬同型性と商環比較の可逆性を使う。
規約：KST Lemma3.6。使われ方：普遍チャートの通常模型との導来比較。 -/
instance universalChartComplexComparison_quasiIso (i : Fin (r + 1)) :
    letI := (universalPresentationMap i).toAlgebra
    QuasiIso (universalChartComplexComparison i) := by
  let := (universalPresentationMap i).toAlgebra
  let e := (universalChartSequenceQuotientEquiv i).toModuleIso
  have : IsIso e.hom := e.isIso_hom
  have : IsIso ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map e.hom) :=
    inferInstance
  have := SerrePositivity.quasiIso_koszulAugmentation
    (universalChartSequence_isKoszulResolution i)
  dsimp only [universalChartComplexComparison]
  exact quasiIso_comp _ _

end SerrePositivity.KST.DerivedBlowup
