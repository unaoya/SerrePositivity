module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.SConstruction.BoundaryOmegaSpectrum
public import SerrePositivity.KST.SConstruction.KSpaceSequence
public import SerrePositivity.KST.SConstruction.MultiStageConnected

/-! # 元の K 空間を零段とする BF Ω スペクトル
概要：既存の K の列の零段と構造射を保ち、Ω 条件を証明して BF スペクトルに束ねる。
方針：零段の随伴は恒等射、正の段には元の境界商の Ω 条件を適用する。
規約：零段は Ω|S•|。負次数消滅は別に証明する。使われ方：π₀ K と三角圏 K₀ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra

/-- K 空間を零段にした既存の列は全ての段で元の Ω 条件を満たす。 -/
lemma kKanSequence_omegaCondition (X : StableModel.{u}) :
    (kKanSequence X).OmegaCondition := by
  intro r
  cases r with
  | zero => exact kKanSequence_zero_piIsomorphism X
  | succ r => exact boundaryKanSequence_omegaCondition X r

/-- 既存の単射置換した K の列も全基点の Ω 条件を満たす。 -/
lemma monicKKanSequence_omegaCondition (X : StableModel.{u}) :
    (monicKKanSequence X).OmegaCondition :=
  KanSequence.cofibrantReplacement_omegaCondition _ (kKanSequence_omegaCondition X)

/-- 元の K 空間を零段にした列の単射置換による BF Ω スペクトル。 -/
def kOmegaSpectrum (X : StableModel.{u}) : OmegaSpectrum.{u} :=
  (monicKKanSequence X).toOmegaSpectrum (fun _ => inferInstance)
    (monicKKanSequence_omegaCondition X)

/-- BF 模型の零段は元の境界商による K 空間に厳密に一致する。 -/
lemma kOmegaSpectrum_zero (X : StableModel.{u}) :
    ((kOmegaSpectrum X).level 0).space = boundaryKSpaceFunctor.obj X := rfl

/-- BF 模型の全ての正の段は連結。 -/
instance kOmegaSpectrum_positive_isConnected (X : StableModel.{u}) (r : ℕ) :
    SSet.IsConnected (((kOmegaSpectrum X).level (r + 1)).space).right :=
  monicKKanSequence_positive_isConnected X r

/-- 既存の K 空間から BF K スペクトルの零段への元の比較射。 -/
def kSpaceSpectrumComparison (X : StableModel.{u}) :
    kSpace X.carrier ⟶ ((kOmegaSpectrum X).level 0).space := kSpaceBoundaryComparison X

/-- 元の K 空間と BF K スペクトルの零段の比較は全基点 π 同型。 -/
lemma kSpaceSpectrumComparison_piIsomorphism (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (kSpaceSpectrumComparison X).right := kSpaceBoundaryComparison_piIsomorphism X

end SerrePositivity.KST.SConstruction

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BGT "Def 7.5" (partial := special) "仮定：安定準圏と完全写像を束ねた StableModel（Lean が強い：安定準圏に限る）。結論：各 Gap の反復から core と実現を取り、構造写像を持つ連結 K の Ω スペクトルを作る（安定な入力についての同じ反復 S 構成）。"] _root_.SerrePositivity.KST.SConstruction.kKanSequence_omegaCondition
attribute [cite BGT "Def 7.5" (partial := special) "仮定：安定準圏と完全写像を束ねた StableModel（Lean が強い：安定準圏に限る）。結論：各 Gap の反復から core と実現を取り、構造写像を持つ連結 K の Ω スペクトルを作る（安定な入力についての同じ反復 S 構成）。"] _root_.SerrePositivity.KST.SConstruction.kOmegaSpectrum
