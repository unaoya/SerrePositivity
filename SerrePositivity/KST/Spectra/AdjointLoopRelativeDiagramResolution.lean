module

public import SerrePositivity.KST.Spectra.AdjointLoopRelativeNativeDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InnerPullback

/-!
概要：左右因子を保つ始域に、厳密な終点上の実 loop 図式を加える。
方針：実 loop 図式の終点評価を引き戻し、全単射 RLP と全図式比較を回収する。
規約：置換 BF 対象への比較射を加えた射影の RLP はこの補題からは従わない。
使われ方：d3b② の共通分解のうち、指定 loop 図式を保持する基底。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 概要：元の終点を保つ全 loop 図式を記憶する共通始域。
方針：全 Hom の可換な組の終点関手に沿って引き戻す。
規約：頂点だけでなく全単体の実図式を保持する。
使われ方：比較射を加える前の図式側の基底。 -/
def fullLoopDiagramResolution : SSet.{u + 1} :=
  pullback (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1) fullNativeLoopEndpoint

/-- 概要：同じ始域から元の可換な組を回収する射影。
方針：実引き戻しの第二射影を使う。
規約：元の左右因子を保つ始域へ戻す。
使われ方：追加した loop 図式を忘れる関手。 -/
def fullLoopDiagramResolutionProjection :
    fullLoopDiagramResolution.{u} ⟶ SimplicialNerve FullObject :=
  pullback.snd _ _

/-- 概要：同じ始域から記憶した実 loop 図式を回収する。
方針：実引き戻しの第一射影を使う。
規約：nativeLoop の別定義ではない。
使われ方：指定終点上の全図式比較。 -/
def fullLoopDiagramResolutionFamily :
    fullLoopDiagramResolution.{u} ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams Sp.{u} :=
  pullback.fst _ _

/-- 概要：記憶した図式の終点は元の一段移動と厳密に一致する。
方針：実引き戻しの可換式を使う。
規約：対象ごとの同型で置き換えない。
使われ方：nativeLoopDiagramFamilyIso の同じ終点条件。 -/
lemma fullLoopDiagramResolutionFamily_target :
    fullLoopDiagramResolutionFamily.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1 =
      fullLoopDiagramResolutionProjection ≫ fullNativeLoopEndpoint :=
  pullback.condition

/-- 概要：図式を忘れる射影は全単射に対する実 RLP を持つ。
方針：元の終点評価の自明 Kan fibration を基底変換する。
規約：比較射を含む射影の充填性はここでは主張しない。
使われ方：図式側の共通分解の全境界充填。 -/
instance fullLoopDiagramResolutionProjection_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration fullLoopDiagramResolutionProjection.{u} :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.pullback_snd _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem
    (p := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1))⟩

/-- 概要：図式側の共通始域は実 quasicategory。
方針：元の可換な組への射影の inner fibration 性を使う。
規約：quasicategory 性を追加入力にしない。
使われ方：全図式同値の始域。 -/
instance fullLoopDiagramResolution_quasicategory :
    Quasicategory fullLoopDiagramResolution.{u} :=
  quasicategory_of_innerFibration fullLoopDiagramResolutionProjection

/-- 概要：図式を忘れる元の射影を順射とする同値。
方針：実自明 Kan fibration の同値判定を使う。
規約：比較射をまだ加えていない始域に対する同値。
使われ方：元の全 Hom の可換な組の回収。 -/
def fullLoopDiagramResolutionEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence fullLoopDiagramResolution.{u} (SimplicialNerve FullObject) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration fullLoopDiagramResolutionProjection

/-- 概要：既存の指定 native 図式族は図式側の共通始域への厳密な切断。
方針：同じ厳密終点式で引き戻しへ持ち上げる。
規約：比較射の自然性をこの切断から推論しない。
使われ方：従来の指定族との接続。 -/
def fullLoopDiagramResolutionSection :
    SimplicialNerve FullObject ⟶ fullLoopDiagramResolution.{u} :=
  pullback.lift fullNativeLoopDiagramFamily (𝟙 _) (by
    rw [Category.id_comp]
    exact fullNativeLoopDiagramFamily_target)

/-- 概要：切断は元の可換な組を厳密に回収する。
方針：引き戻しの第二射影式を使う。
規約：全単体の等式。
使われ方：共通始域の底の照合。 -/
@[reassoc (attr := simp)]
lemma fullLoopDiagramResolutionSection_projection :
    fullLoopDiagramResolutionSection.{u} ≫ fullLoopDiagramResolutionProjection = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- 概要：同じ切断は元の指定 native loop 図式族を厳密に回収する。
方針：引き戻しの第一射影式を使う。
規約：全図式の族自体を保持する。
使われ方：元の nativeLoop との接続。 -/
@[reassoc (attr := simp)]
lemma fullLoopDiagramResolutionSection_family :
    fullLoopDiagramResolutionSection.{u} ≫ fullLoopDiagramResolutionFamily =
      fullNativeLoopDiagramFamily :=
  pullback.lift_fst _ _ _

/-- 概要：記憶した全図式と同じ終点の指定 native 図式族との関手同型。
方針：厳密終点の一致を元の終点評価の自明 Kan fibration へ適用する。
規約：相対 BF 置換への比較射を含む自然性は別途必要。
使われ方：d3b② の図式側の比較。 -/
def fullLoopDiagramResolutionNativeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso fullLoopDiagramResolutionFamily.{u}
      (fullLoopDiagramResolutionProjection ≫ fullNativeLoopDiagramFamily) :=
  nativeLoopDiagramFamilyIso _ _ (by
    rw [Category.assoc, fullNativeLoopDiagramFamily_target]
    exact fullLoopDiagramResolutionFamily_target)

/-- 概要：図式側の比較の始点評価は元の nativeLoop を厳密に使う。
方針：全図式同型を始点評価で写し、元の始点式を適用する。
規約：この比較の他端は記憶した図式の始点であり、middle ではない。
使われ方：比較射の全 Hom 充填を接続する端点。 -/
def fullLoopDiagramResolutionSourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (fullLoopDiagramResolutionFamily.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 0 0)
      ((fullLoopDiagramResolutionProjection ≫ fullNativeLoopEndpoint) ≫ nativeLoop) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp fullLoopDiagramResolutionNativeIso
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 0 0)
  rw [Category.assoc, fullNativeLoopDiagramFamily_source, ← Category.assoc] at e
  exact e

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
