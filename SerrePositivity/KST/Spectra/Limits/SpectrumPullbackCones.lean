module

public import SerrePositivity.KST.Spectra.Limits.SpectrumPullbackOmega

/-!
概要：段ごとの一脚 fibration の引き戻しのスペクトル錐と実際の豊穣 Hom の普遍性。
方針：各段の点つき引き戻しの普遍性を写像空間の族の普遍性へ渡す。
規約：∞ 極限性に必要な Hom の fibration 条件は別途検証する。
使われ方：BF 1978 §2、HTT 4.2.4.1 の Sp の実際の引き戻し錐。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

variable {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)

/-- 概要：二つのスペクトルの射から小さい cospan の図式を作る。
方針：通常の cospan の添字を Hom の宇宙まで持ち上げる。
規約：左脚は f、右脚は g。
使われ方：Sp の厳密な引き戻し図式と coherent nerve の図式。 -/
def spectrumPullbackDiagram : AsSmall.{u} WalkingCospan ⥤ OmegaSpectrum.{u} :=
  AsSmall.down ⋙ cospan f g

variable [∀ n, Fibration (f.app n).right]

/-- 概要：引き戻しスペクトルと二つの射影による通常の cospan の錐。
方針：各段で検証済みの可換条件を PullbackCone に束ねる。
規約：頂点は実際の spectrumPullback f g。
使われ方：各段の引き戻しの普遍性の入力。 -/
def spectrumPullbackOrdinaryCone : PullbackCone f g :=
  PullbackCone.mk (spectrumPullbackFst f g) (spectrumPullbackSnd f g)
    (spectrumPullback_condition f g)

/-- 概要：持ち上げた cospan の図式の実際のスペクトル錐。
方針：通常の引き戻し錐を AsSmall の忘却に沿って制限する。
規約：頂点と二つの脚のデータは変えない。
使われ方：全ての豊穣 Hom で検査する引き戻し錐。 -/
def spectrumPullbackCone : Cone (spectrumPullbackDiagram f g) :=
  (spectrumPullbackOrdinaryCone f g).whisker
    (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan)

/-- 概要：通常の引き戻し錐を各段へ評価した錐は極限。
方針：錐の評価と標準の引き戻し錐の比較を使い、点つき引き戻しの普遍性を適用する。
規約：全自然数段で厳密な通常の極限性を与える。
使われ方：スペクトルの実際の Hom の引き戻しの検証。 -/
def spectrumPullbackOrdinaryCone_level_isLimit (n : ℕ) :
    IsLimit ((spectrumLevelFunctor n).mapCone (spectrumPullbackOrdinaryCone f g)) :=
  (isLimitMapConePullbackConeEquiv (spectrumLevelFunctor n)
    (spectrumPullback_condition f g)).symm (pullbackIsPullback (f.app n) (g.app n))

/-- 概要：小さい cospan のスペクトル錐は各段で点つき極限となる。
方針：通常の錐の極限性を添字の圏同値で持ち上げる。
規約：右脚 g に fibration 性は不要。
使われ方：実際の豊穣 Hom の極限性へ渡す各段の条件。 -/
def spectrumPullbackCone_level_isLimit (n : ℕ) :
    IsLimit (spectrumLevelCone (spectrumPullbackCone f g) n) := by
  exact (spectrumPullbackOrdinaryCone_level_isLimit f g n).whiskerEquivalence
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).symm

local instance spectrumPullbackCones_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 概要：実際のスペクトルの引き戻し錐は全ての豊穣 Hom で極限となる。
方針：各段の極限性を L9 の整合写像空間の族の普遍性へ渡す。
規約：Hom を代替模型に取り替えない。
使われ方：HTT 4.2.4.1 の Sp の引き戻しの Hom の普遍性。 -/
def spectrumPullbackCone_hom_isLimit (Z : OmegaSpectrum.{u}) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone (spectrumPullbackCone f g) Z) :=
  spectrumHomCone_isLimit_of_levelwise _ (spectrumPullbackCone_level_isLimit f g) Z

/-- 概要：実際のスペクトルの引き戻し錐を L9 の Sp の錐へ写す。
方針：小さい cospan の厳密な錐へ coherent nerve の構成を適用する。
規約：この定義だけでは ∞ 極限性は主張しない。
使われ方：Hom の fibration 性の検証後に Sp の極限錐として公開する対象。 -/
def spectrumPullbackInfinityCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (spectrumPullbackDiagram f g)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (spectrumPullbackCone f g)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
