module

public import SerrePositivity.KST.DerivedBlowup.UniversalDerivedChartComparison
public import SerrePositivity.KST.DerivedBlowup.ExteriorQuotientAugmentation

/-!
概要：KST Def3.1・Lemma3.6 の通常の普遍チャート商とその標準 Koszul 解消。
方針：宇宙移送した表示環の商を元の自由チャートと同定し、標準添加の擬同型を使う。
規約：標準添加は生成元を零へ送る射。任意に選択した H⁰ 同型は使用しない。
使われ方：通常の普遍 blowup チャートの実導来底変更を Koszul 模型へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w w'

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Limits

variable {r : ℕ}

/-- 概要：宇宙移送した普遍チャートの有限列の生成元微分。
方針：既存有限チャート列の自由線形結合を使う。
規約：KST Lemma3.6。使われ方：通常のチャート商への標準添加。 -/
abbrev liftedUniversalSequenceDifferential (i : Fin (r + 1)) :=
  Finsupp.linearCombination (ChartRing (LiftedUniversalBase.{u} r) i)
    (chartKoszulSequence (liftedUniversalCoefficients r) i)

/-- 概要：宇宙移送した通常の普遍チャート環。
方針：表示多項式環を関係式微分の像で割る。
規約：KST Def3.1、元の普遍自由チャートとの同型を下で証明する。
使われ方：実導来底変更の通常環の始域。 -/
abbrev LiftedUniversalOrdinaryChart (i : Fin (r + 1)) :=
  ChartRing (LiftedUniversalBase.{u} r) i ⧸ LinearMap.range (liftedUniversalSequenceDifferential i)

/-- 概要：宇宙移送の表示環同型は関係式イデアルを元の普遍関係式イデアルへ送る。
方針：自由線形結合の像を span とし、関係式の像を有限列で比較する。
規約：KST Def3.1。使われ方：通常の普遍チャート商の環同型。 -/
theorem liftedUniversalSequenceIdeal_map (i : Fin (r + 1)) :
    Ideal.map (liftedUniversalPresentationEquiv i).toRingHom
      (LinearMap.range (liftedUniversalSequenceDifferential.{u} i)) = universalRelationIdeal i := by
  rw [Finsupp.range_linearCombination, Ideal.map_span, ← Set.range_comp]
  have he : (liftedUniversalPresentationEquiv.{u} i).toRingHom ∘
      chartKoszulSequence (liftedUniversalCoefficients r) i =
      chartKoszulSequence (R := UniversalBase (Fin (r + 1))) MvPolynomial.X i := by
    funext j
    exact liftedUniversalPresentationEquiv_relation i (i.succAbove j)
  rw [he]
  exact universalChartSequence_ideal i

/-- 概要：宇宙移送した通常の普遍チャート商と元の自由多項式チャートの環同型。
方針：表示環同型を関係式商へ降ろし、元の普遍商表示同型を合成する。
規約：KST Def3.1・Lemma3.6。使われ方：古典普遍チャートとの接続。 -/
def liftedUniversalOrdinaryChartEquiv (i : Fin (r + 1)) :
    LiftedUniversalOrdinaryChart.{u} i ≃+* UniversalChart i :=
  (Ideal.quotientEquiv _ _ (liftedUniversalPresentationEquiv i)
    (liftedUniversalSequenceIdeal_map i).symm).trans (universalPresentationEquiv i)

/-- 概要：通常の普遍チャート商の同型は表示環の元の代入と可換。
方針：環同型による商射の生成元公式と普遍代入を使う。
規約：KST Def3.1。使われ方：普遍基底の作用を保つことの確認。 -/
theorem liftedUniversalOrdinaryChartEquiv_mk (i : Fin (r + 1))
    (p : ChartRing (LiftedUniversalBase.{u} r) i) :
    liftedUniversalOrdinaryChartEquiv i
      (Ideal.Quotient.mk (LinearMap.range (liftedUniversalSequenceDifferential i)) p) =
      universalPresentationMap i (liftedUniversalPresentationEquiv i p) := by
  change universalQuotientToChart i
      ((Ideal.quotientMap (universalRelationIdeal i)
        (liftedUniversalPresentationEquiv i).toRingHom
          (Ideal.map_le_iff_le_comap.mp (liftedUniversalSequenceIdeal_map i).le))
          (Ideal.Quotient.mk (LinearMap.range (liftedUniversalSequenceDifferential i)) p)) = _
  rw [Ideal.quotientMap_mk]
  rfl

/-- 概要：宇宙移送した通常チャートの比較は普遍基底の係数作用を保つ。
方針：商射との可換性と係数の ULift 同型を計算する。
規約：KST Def3.1。使われ方：Rees–Proj チャートとの基底上の接続。 -/
theorem liftedUniversalOrdinaryChartEquiv_base (i : Fin (r + 1))
    (p : LiftedUniversalBase.{u} r) :
    liftedUniversalOrdinaryChartEquiv i
      (Ideal.Quotient.mk (LinearMap.range (liftedUniversalSequenceDifferential i))
        (MvPolynomial.C p)) = universalBaseMap i (ULift.ringEquiv p) := by
  rw [liftedUniversalOrdinaryChartEquiv_mk]
  change universalPresentationMap i
    (MvPolynomial.map ULift.ringEquiv.toRingHom (MvPolynomial.C p)) = _
  rw [MvPolynomial.map_C, universalPresentationMap_C]
  rfl

/-- 概要：通常の普遍チャート商への標準添加鎖写像。
方針：チャート添字を有限列へ戻し、微分像の商への標準添加を合成する。
規約：KST Lemma3.6。使われ方：普遍基底上の通常環の K-flat 解消。 -/
def liftedUniversalOrdinaryAugmentation (i : Fin (r + 1)) :
    chartExteriorCochain (fun j => MvPolynomial.C (liftedUniversalCoefficients.{u} r j))
        (chartCoordinate (LiftedUniversalBase.{u} r) i) i ⟶
      (HomologicalComplex.single _ (.up ℤ) 0).obj
        (ModuleCat.of (ChartRing (LiftedUniversalBase.{u} r) i)
          (LiftedUniversalOrdinaryChart.{u} i)) :=
  (chartSequenceExteriorIso (liftedUniversalCoefficients.{u} r) i).inv ≫
    exteriorQuotientAugmentation (liftedUniversalSequenceDifferential i)

/-- 概要：通常の普遍チャート商への標準添加は擬同型。
方針：移送した普遍関係式列の解消性を外積模型へ移し、標準 H⁰ 計算を使う。
規約：KST Lemma3.6。使われ方：通常環を実導来底変更するための具体的解消。 -/
instance liftedUniversalOrdinaryAugmentation_quasiIso (i : Fin (r + 1)) :
    QuasiIso (liftedUniversalOrdinaryAugmentation.{u} i) := by
  have : QuasiIso (exteriorQuotientAugmentation (liftedUniversalSequenceDifferential.{u} i)) :=
    exteriorQuotientAugmentation_quasiIso _ (fun q hq =>
      ((liftedUniversalChartSequence_isKoszulResolution.{u} i).isZero q hq).of_iso
        (HomologicalComplex.homologyMapIso (koszulExteriorIso
          (chartKoszulSequence (liftedUniversalCoefficients.{u} r) i)) q).symm)
  dsimp only [liftedUniversalOrdinaryAugmentation]
  infer_instance

/-- 概要：通常の普遍チャート商の単一複体を普遍基底へ係数制限したもの。
方針：表示多項式環上の標準係数作用を保持して制限する。
規約：KST Def3.1。使われ方：実導来底変更の入力複体。 -/
abbrev liftedUniversalOrdinaryChartComplex (i : Fin (r + 1)) :=
  ((ModuleCat.restrictScalars (algebraMap (LiftedUniversalBase.{u} r)
    (ChartRing (LiftedUniversalBase.{u} r) i))).mapHomologicalComplex (.up ℤ)).obj
      ((HomologicalComplex.single _ (.up ℤ) 0).obj
        (ModuleCat.of (ChartRing (LiftedUniversalBase.{u} r) i)
          (LiftedUniversalOrdinaryChart.{u} i)))

/-- 概要：普遍基底の導来圏でチャート Koszul 模型は通常の普遍チャートに同型。
方針：標準添加の擬同型性を係数制限して導来圏へ送る。
規約：KST Lemma3.6。使われ方：通常の普遍チャートを具体的な K-flat 解消で置き換える。 -/
def liftedUniversalOrdinaryResolutionIso (i : Fin (r + 1))
    [HasDerivedCategory.{w} (ModuleCat.{u} (LiftedUniversalBase.{u} r))] :
    DerivedCategory.Q.obj (chartRestrictedExterior (liftedUniversalCoefficients.{u} r) i) ≅
      DerivedCategory.Q.obj (liftedUniversalOrdinaryChartComplex.{u} i) := by
  let f := ((ModuleCat.restrictScalars (algebraMap (LiftedUniversalBase.{u} r)
    (ChartRing (LiftedUniversalBase.{u} r) i))).mapHomologicalComplex (.up ℤ)).map
      (liftedUniversalOrdinaryAugmentation.{u} i)
  have : QuasiIso f := by
    dsimp only [f]
    infer_instance
  exact asIso (DerivedCategory.Q.map f)

/-- 概要：通常の普遍チャート環の実導来底変更は標準 Koszul チャートを与える。
方針：通常環の標準解消同型を実導来係数拡大へ送り、証明済みの局所計算と合成する。
規約：KST Def3.1・Lemma3.6、任意宇宙の可換係数環で平坦性は不要。
使われ方：導来 blowup チャートの明示 Koszul 表示の根拠。 -/
def liftedUniversalDerivedOrdinaryChartIso {R : Type u} [CommRing R]
    (a : Fin (r + 1) → R) (i : Fin (r + 1))
    [HasDerivedCategory.{w} (ModuleCat.{u} (LiftedUniversalBase.{u} r))]
    [HasDerivedCategory.{w'} (ModuleCat.{u} R)] :
    letI := (liftedUniversalSpecialization a).toAlgebra
    (DifferentialGraded.ScalarExtension.complexDerivedExtension
      (liftedUniversalSpecialization a)).obj
        (DerivedCategory.Q.obj (liftedUniversalOrdinaryChartComplex.{u} i)) ≅
      DerivedCategory.Q.obj (chartRestrictedExterior a i) := by
  letI := (liftedUniversalSpecialization a).toAlgebra
  exact (DifferentialGraded.ScalarExtension.complexDerivedExtension
      (liftedUniversalSpecialization a)).mapIso (liftedUniversalOrdinaryResolutionIso i).symm ≪≫
    liftedUniversalDerivedChartIso a i

end SerrePositivity.KST.DerivedBlowup
