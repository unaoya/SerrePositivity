module

public import SerrePositivity.KST.Spectra.TwistedKanSequenceMaps
public import SerrePositivity.KST.Spectra.CotensorIntegerPower
public import SerrePositivity.KST.Spectra.SignedLoopComparison

/-!
概要：段ごとの符号補正を、元の BF loop 源の実際の自己射による一つの twist へ移す。
方針：cotensorPre の反転と BF 射影の厳密な可換式を twistHom へ入力する。
規約：構造射の単射性は BF 置換で回復し、元の raw 比較の因子分解を保持する。
使われ方：HA §1.4.2。段依存の補正を厳密な列比較へ束ねる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
variable (X : OmegaSpectrum.{u})

/-- 元の一段移動した BF loop 源の実際の反転自己射。 -/
def signedLoopSourceReversal :
    KanSequence.Hom (tail (cotensor CirclePower.space.{u} X)).toKanSequence
      (tail (cotensor CirclePower.space.{u} X)).toKanSequence :=
  sequenceHom (tailMap (cotensorPre (CirclePower.integerPowerMap.{u} (-1)) X))

/-- 源の実際の反転は、全段・全基点で π 同型。 -/
lemma signedLoopSourceReversal_levelwise (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((signedLoopSourceReversal X).app n).right :=
  cotensorPre_neg_one_levelwise X (n + 1)

/-- 段依存の符号補正を源の構造射に入れた BF 対象。 -/
def signedLoopSourceTwist : OmegaSpectrum.{u} :=
  twisted (tail (cotensor CirclePower.space.{u} X))
    (signedLoopSourceReversal X) (signedLoopSourceReversal_levelwise X)

/-- 源を twist した段階での、符号付き Kan loop 列への単一の厳密な射。 -/
def signedLoopSourceTwistRawProjection :
    KanSequence.Hom (KanSequence.twist (signedLoopSourceReversal X))
      (KanSequence.signedLoopTail X.toKanSequence) :=
by
  let V := KanSequence.tail (KanSequence.mapping CirclePower.space.{u} X.toKanSequence)
  let r := signedLoopSourceReversal X
  let s : KanSequence.Hom V V := KanSequence.tailHom
    (KanSequence.mappingPre (CirclePower.integerPowerMap.{u} (-1)) X.toKanSequence)
  let q : KanSequence.Hom (tail (cotensor CirclePower.space.{u} X)).toKanSequence V :=
    KanSequence.tailHom (cotensorProjection CirclePower.space.{u} X)
  have h : ∀ n, r.app n ≫ q.app n = q.app n ≫ s.app n := by
    intro n
    exact cotensorPre_comparison (CirclePower.integerPowerMap.{u} (-1)) X (n + 1)
  change KanSequence.Hom (KanSequence.twist r) (KanSequence.twist s)
  exact KanSequence.twistHom r s q h

/-- 源の BF 置換後も同じ厳密な Kan 列への比較を保つ。 -/
def signedLoopSourceTwistProjection :
    KanSequence.Hom (signedLoopSourceTwist X).toKanSequence
      (KanSequence.signedLoopTail X.toKanSequence) :=
  (twistedProjection (tail (cotensor CirclePower.space.{u} X))
    (signedLoopSourceReversal X) (signedLoopSourceReversal_levelwise X)).comp
    (signedLoopSourceTwistRawProjection X)

/-- 元の BF loop 源から、構造に符号を入れた BF 源への実際の厳密な比較。 -/
def signedLoopSourceTwistComparison :
    tail (cotensor CirclePower.space.{u} X) ⟶ signedLoopSourceTwist X :=
  twistComparison (tail (cotensor CirclePower.space.{u} X))
    (signedLoopSourceReversal X) (signedLoopSourceReversal_levelwise X)

/-- 同じ源の twist 比較は全段・全基点で π 同型。 -/
lemma signedLoopSourceTwistComparison_levelwise (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((signedLoopSourceTwistComparison X).app n).right :=
  twistComparison_levelwise (tail (cotensor CirclePower.space.{u} X))
    (signedLoopSourceReversal X) (signedLoopSourceReversal_levelwise X) n

/-- twist 後の生の射影は元の同じ BF 射影を各段に持つ。 -/
lemma signedLoopSourceTwistRawProjection_levelwise (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((signedLoopSourceTwistRawProjection X).app n).right :=
  cotensorProjection_piIsomorphism CirclePower.space.{u} X (n + 1)

/-- BF 置換後の射影も全段・全基点で π 同型。 -/
lemma signedLoopSourceTwistProjection_levelwise (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((signedLoopSourceTwistProjection X).app n).right :=
  (KanSequence.replacementProjection_piIsomorphism
    (KanSequence.twist (signedLoopSourceReversal X)) n).comp
      (signedLoopSourceTwistRawProjection_levelwise X n)

/-- 元の raw 比較自身は、同じ源の単一の twist 比較と射影へ厳密に因子分解する。 -/
lemma signedLoopSourceTwistComparison_factor (n : ℕ) :
    (signedLoopSourceTwistComparison X).app n ≫
      (signedLoopSourceTwistProjection X).app n = (signedLoopRawComparison X).app n := by
  let q := KanSequence.tailHom (cotensorProjection CirclePower.space.{u} X)
  let s := KanSequence.tailHom (KanSequence.mappingPre
    (CirclePower.integerPowerMap.{u} (-1)) X.toKanSequence)
  have hi := KanSequence.iterateHom_natural (signedLoopSourceReversal X) s q
    (fun k => cotensorPre_comparison (CirclePower.integerPowerMap.{u} (-1)) X (k + 1)) n n
  change (signedLoopSourceTwistComparison X).app n ≫
    ((twistedProjection (tail (cotensor CirclePower.space.{u} X))
      (signedLoopSourceReversal X) (signedLoopSourceReversal_levelwise X)).app n ≫ q.app n) =
    q.app n ≫ (KanSequence.iterateHom s n).app n
  rw [← Category.assoc]
  exact (congrArg (· ≫ q.app n)
    (twistComparison_projection (tail (cotensor CirclePower.space.{u} X))
      (signedLoopSourceReversal X) (signedLoopSourceReversal_levelwise X) n)).trans hi

end SerrePositivity.KST.Spectra.OmegaSpectrum
