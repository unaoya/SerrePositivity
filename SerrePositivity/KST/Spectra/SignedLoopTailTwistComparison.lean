module

public import SerrePositivity.KST.Spectra.SignedLoopComparison

/-!
概要：一段移動した元の Kan cotensor 列から、符号付き列への同じ twist 比較を公開する。
方針：元の反転自己射を一段移動し、既存の反復比較を取る。
規約：元の BF raw 比較の因子そのもの。使われ方：全 Hom の評価写像への符号補正。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.KST.Spectra.KanSequence

/-- 一段移動した元の Kan cotensor から、構造に符号を入れた列への実比較。 -/
def signedLoopTailTwistComparison (Y : KanSequence.{u}) :
    Hom (tail (mapping CirclePower.space.{u} Y)) (signedLoopTail Y) := by
  let V := tail (mapping CirclePower.space.{u} Y)
  let r : Hom V V := tailHom (mappingPre (CirclePower.integerPowerMap.{u} (-1)) Y)
  change Hom V (twist r)
  exact twistMap r

/-- 同じ twist 比較は、各段で全基点 π 同型。 -/
lemma signedLoopTailTwistComparison_levelwise (Y : KanSequence.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((signedLoopTailTwistComparison Y).app n).right :=
  twistMap_piIsomorphism (tailHom (mappingPre (CirclePower.integerPowerMap.{u} (-1)) Y))
    (fun k => LoopMappingClasses.pre_neg_one_piIsomorphism (Y.level (k + 1)).space) n

end SerrePositivity.KST.Spectra.KanSequence

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 元の BF raw 比較全体は、一段移動した射影と同じ twist 比較の合成。 -/
lemma signedLoopRawComparison_tail_factor (Y : OmegaSpectrum.{u}) :
    (KanSequence.tailHom (cotensorProjection CirclePower.space.{u} Y)).comp
      (KanSequence.signedLoopTailTwistComparison Y.toKanSequence) =
      signedLoopRawComparison Y := rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
