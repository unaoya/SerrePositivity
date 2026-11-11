module

public import SerrePositivity.KST.Spectra.FilteredSpectrumInjection

/-!
概要：filtered Ω 図式の自然変換が誘導する BF 対象間の実際の射。
方針：段ごとの余極限射を作り、cofibrant な源から比較射へ持ち上げる。
規約：持ち上げの厳密な関手法則は主張しない。段ごとの π_* 同型性を保存する。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。telescope の比較。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {J : Type u} [SmallCategory J] [IsFiltered J]
  {D E : J ⥤ OmegaSpectrum.{u}}

/-- 概要：図式の自然変換が各段の点つき図式に誘導する自然変換。
方針：段評価関手を右 whisker する。
規約：対象・射は元の厳密なスペクトルの射の成分。
使われ方：BF 1978 §2。余極限の比較射の各段。 -/
abbrev levelTransformation (τ : D ⟶ E) (k : ℕ) : levelDiagram D k ⟶ levelDiagram E k :=
  CategoryTheory.Functor.whiskerRight τ (levelEvaluation k)

/-- 概要：段の余極限射は元の各段への制限で自然変換の成分になる。
方針：余極限への誘導射の成分式を使う。
規約：点つき単体集合の等式。
使われ方：BF 1978 §2、HA §1.4.2。構造射の可換性の検証。 -/
@[reassoc]
theorem levelTransformation_colimit_ι (τ : D ⟶ E) (k : ℕ) (a : J) :
    colimit.ι (levelDiagram D k) a ≫ colimMap (levelTransformation τ k) =
      (τ.app a).app k ≫ colimit.ι (levelDiagram E k) a :=
  colimit.ι_map (levelTransformation τ k) a

/-- 概要：図式の自然変換は段ごとの Kan 余極限列の厳密な射を誘導する。
方針：各段で余極限射を取り、suspension の余極限保存により構造条件を検査する。
規約：単射置換前の Kan 列の射。
使われ方：BF 1978 §2、HA §1.4.2。BF 置換への持ち上げの入力。 -/
def filteredKanMap (τ : D ⟶ E) :
    KanSequence.Hom (filteredKanSequence D) (filteredKanSequence E) where
  app k := colimMap (levelTransformation τ k)
  comm k := by
    apply (isColimitOfPreserves (tensorLeft PointedSimplicialSet.circle.{u})
      (colimit.isColimit (levelDiagram D k))).hom_ext
    intro a
    change (PointedSimplicialSet.circle.{u} ◁ colimit.ι (levelDiagram D k) a) ≫
      (PointedSimplicialSet.circle.{u} ◁ colimMap (levelTransformation τ k) ≫
        (filteredKanSequence E).sigma k) =
      (PointedSimplicialSet.circle.{u} ◁ colimit.ι (levelDiagram D k) a) ≫
        ((filteredKanSequence D).sigma k ≫ colimMap (levelTransformation τ (k + 1)))
    have hD : (PointedSimplicialSet.circle.{u} ◁ colimit.ι (levelDiagram D k) a) ≫
        (filteredKanSequence D).sigma k =
        (D.obj a).sigma k ≫ colimit.ι (levelDiagram D (k + 1)) a :=
      (filteredKanInjection D a).comm k
    have hE : (PointedSimplicialSet.circle.{u} ◁ colimit.ι (levelDiagram E k) a) ≫
        (filteredKanSequence E).sigma k =
        (E.obj a).sigma k ≫ colimit.ι (levelDiagram E (k + 1)) a :=
      (filteredKanInjection E a).comm k
    rw [← Category.assoc, ← whiskerLeft_comp, levelTransformation_colimit_ι,
      whiskerLeft_comp, Category.assoc, hE,
      ← Category.assoc, (τ.app a).comm k, Category.assoc]
    conv_rhs => rw [← Category.assoc, hD, Category.assoc, levelTransformation_colimit_ι]

/-- 概要：自然変換が単射置換した BF 対象間に誘導する厳密な射。
方針：源の BF 比較射と Kan 余極限の射の合成を、標的の BF 比較射へ持ち上げる。
規約：選んだ持ち上げを一つ固定する。
使われ方：BF 1978 §2、HTT A.3.3。telescope の実際の比較射。 -/
def filteredSpectrumMap (τ : D ⟶ E) : filteredOmegaSpectrum D ⟶ filteredOmegaSpectrum E := by
  let f : KanSequence.Hom (filteredOmegaSpectrum D).toKanSequence
      (filteredOmegaSpectrum E).toKanSequence :=
    KanSequence.liftHom (X := (filteredOmegaSpectrum D).toKanSequence)
      (W := (filteredOmegaSpectrum E).toKanSequence) (Z := filteredKanSequence E)
      (filteredOmegaSpectrum D).sigma_mono (filteredSequenceComparison E)
      (fun k ↦ (KanSequence.replacementStage (filteredKanSequence E) k).projection_rlp)
      ((filteredSequenceComparison D).comp (filteredKanMap τ))
  exact { app := f.app, comm := f.comm }

/-- 概要：BF 対象間の比較射は各段の余極限比較射と厳密に整合する。
方針：選んだ持ち上げの右辺との比較式を使う。
規約：各段の点つき射の等式。
使われ方：BF 1978 §2、HTT A.3.3。π_* 同型性の検証。 -/
theorem filteredSpectrumMap_comparison (τ : D ⟶ E) (k : ℕ) :
    (filteredSpectrumMap τ).app k ≫ filteredLevelComparison E k =
      filteredLevelComparison D k ≫ colimMap (levelTransformation τ k) :=
  KanSequence.liftHom_fac (X := (filteredOmegaSpectrum D).toKanSequence)
    (W := (filteredOmegaSpectrum E).toKanSequence) (Z := filteredKanSequence E)
    (filteredOmegaSpectrum D).sigma_mono (filteredSequenceComparison E)
    (fun n ↦ (KanSequence.replacementStage (filteredKanSequence E) n).projection_rlp)
    ((filteredSequenceComparison D).comp (filteredKanMap τ)) k

/-- 概要：段ごとの全基点 π_* 同型の自然変換は BF 余極限対象でも段ごとに π_* 同型。
方針：filtered colimit の保存、単射置換の比較、後合成の打ち消しを使う。
規約：零次数を含み、全ての基点で述べる。
使われ方：BF 1978 §2、Goerss–Jardine I §7。telescope の置換不変性。 -/
theorem filteredSpectrumMap_levelwise (τ : D ⟶ E)
    (hτ : ∀ a k, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((τ.app a).app k).right) (k : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((filteredSpectrumMap τ).app k).right := by
  have hc : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (colimMap (levelTransformation τ k)).right :=
    pointedColimMap_kanPiIsomorphism _ (fun a ↦ hτ a k)
  have hcomp := (filteredLevelComparison_piIsomorphism D k).comp hc
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := (filteredLevelComparison E k).right) _
    (filteredLevelComparison_piIsomorphism E k)
  have h := congrArg Under.Hom.right (filteredSpectrumMap_comparison τ k)
  change ((filteredSpectrumMap τ).app k).right ≫ (filteredLevelComparison E k).right =
    (filteredLevelComparison D k).right ≫ (colimMap (levelTransformation τ k)).right at h
  rw [h]
  exact hcomp

/-- 概要：上の BF 比較射は全整数次数の π_* 同型。
方針：各段の全基点の比較を整数次数の準同型へ移す。
規約：coherent nerve の同値との同定は別工程。
使われ方：BF 1978 §2、HA §1.4.2。telescope の整数次数での置換不変性。 -/
theorem filteredSpectrumMap_piIsomorphism (τ : D ⟶ E)
    (hτ : ∀ a k, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((τ.app a).app k).right) :
    PiIsomorphism (filteredSpectrumMap τ) :=
  piIsomorphism_of_levelwise _ (filteredSpectrumMap_levelwise τ hτ)

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
