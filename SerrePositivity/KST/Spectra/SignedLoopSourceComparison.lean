module

public import SerrePositivity.KST.Spectra.SignedLoopSourceTwist

/-!
概要：符号補正を構造へ移した単一の BF 源から、元の signedLoopModel への実際の比較。
方針：厳密な源の twist 射影を元の BF 置換射影へ持ち上げ、同じ raw 比較の因子分解を保つ。
規約：各段の成分比較だけで列射を推論しない。持ち上げは単射構造と全単射 RLP による。
使われ方：HA §1.4.2。元の円評価を保つ厳密な符号補正比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
variable (X : OmegaSpectrum.{u})

/-- 単一の BF 源の twist 比較を、元の符号付き BF loop 模型へ実際に持ち上げる。 -/
def signedLoopSourceComparison : signedLoopSourceTwist X ⟶ signedLoopModel X := by
  let g := KanSequence.liftHom (X := (signedLoopSourceTwist X).toKanSequence)
    (W := (signedLoopModel X).toKanSequence) (Z := KanSequence.signedLoopTail X.toKanSequence)
    (signedLoopSourceTwist X).sigma_mono (signedLoopProjection X)
    (fun n =>
      (KanSequence.replacementStage (KanSequence.signedLoopTail X.toKanSequence) n).projection_rlp)
    (signedLoopSourceTwistProjection X)
  exact { app := g.app, comm := g.comm }

/-- 元の BF 置換射影の後では、同じ源の twist 射影へ厳密に戻る。 -/
lemma signedLoopSourceComparison_projection (n : ℕ) :
    (signedLoopSourceComparison X).app n ≫ (signedLoopProjection X).app n =
      (signedLoopSourceTwistProjection X).app n :=
  KanSequence.liftHom_fac (X := (signedLoopSourceTwist X).toKanSequence)
    (W := (signedLoopModel X).toKanSequence) (Z := KanSequence.signedLoopTail X.toKanSequence)
    (signedLoopSourceTwist X).sigma_mono (signedLoopProjection X)
    (fun n =>
      (KanSequence.replacementStage (KanSequence.signedLoopTail X.toKanSequence) n).projection_rlp)
    (signedLoopSourceTwistProjection X) n

/-- 源の twist と符号付き loop 模型の実際の比較は全段・全基点で π 同型。 -/
lemma signedLoopSourceComparison_levelwise (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((signedLoopSourceComparison X).app n).right := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := ((signedLoopProjection X).app n).right) _
    (KanSequence.replacementProjection_piIsomorphism (KanSequence.signedLoopTail X.toKanSequence) n)
  have h := congrArg Under.Hom.right (signedLoopSourceComparison_projection X n)
  change ((signedLoopSourceComparison X).app n).right ≫
    ((signedLoopProjection X).app n).right = ((signedLoopSourceTwistProjection X).app n).right at h
  rw [h]
  exact signedLoopSourceTwistProjection_levelwise X n

/-- この二つの厳密な BF 比較の合成は、元の raw 比較自身の同じ持ち上げを与える。 -/
lemma signedLoopSourceComparison_factor (n : ℕ) :
    ((signedLoopSourceTwistComparison X ≫ signedLoopSourceComparison X).app n) ≫
      (signedLoopProjection X).app n = (signedLoopRawComparison X).app n := by
  change ((signedLoopSourceTwistComparison X).app n ≫ (signedLoopSourceComparison X).app n) ≫
    (signedLoopProjection X).app n = _
  rw [Category.assoc, signedLoopSourceComparison_projection, signedLoopSourceTwistComparison_factor]

end SerrePositivity.KST.Spectra.OmegaSpectrum
