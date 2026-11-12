module

public import SerrePositivity.KST.Spectra.SignedLoopModel
public import SerrePositivity.KST.Spectra.CotensorRestriction
public import SerrePositivity.KST.Spectra.SpectrumTail
public import SerrePositivity.KST.Spectra.LoopIntegerPower

/-!
概要：通常の一段先の loop 模型と符号を調整した loop 模型の実際の比較。
方針：実際の内部 Hom 列への射影に段ごとの符号反転の反復を合成し、BF 置換へ持ち上げる。
規約：群の同型から射の存在を推論しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。有理化の通常の loop 模型へ元の対象を比較する。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：通常の BF loop 模型から符号を調整した実際の Kan loop 列への厳密な比較。
方針：BF の射影と段ごとの自己射の反復による twist の比較を合成する。
規約：元の列を一段先へずらして次数を合わせる。
使われ方：BF 1978 §2。符号を調整した BF 模型への持ち上げの入力。 -/
def signedLoopRawComparison (X : OmegaSpectrum.{u}) :
    KanSequence.Hom (tail (cotensor CirclePower.space.{u} X)).toKanSequence
      (KanSequence.signedLoopTail X.toKanSequence) := by
  let V := KanSequence.tail (KanSequence.mapping CirclePower.space.{u} X.toKanSequence)
  let q : KanSequence.Hom (tail (cotensor CirclePower.space.{u} X)).toKanSequence V :=
    KanSequence.tailHom (cotensorProjection CirclePower.space.{u} X)
  let r : KanSequence.Hom V V := KanSequence.tailHom
    (KanSequence.mappingPre (CirclePower.integerPowerMap.{u} (-1)) X.toKanSequence)
  exact q.comp (KanSequence.twistMap r)

/-- 概要：通常の BF 模型から符号を変えた Kan 列への比較は各段で全基点 π_* 同型。
方針：BF 射影の同型性と符号反転の反復の同型性を合成する。
規約：零次数を含む。
使われ方：Goerss–Jardine I §7、BF 1978 §2。BF 置換へ持ち上げる比較の検査。 -/
theorem signedLoopRawComparison_levelwise (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((signedLoopRawComparison X).app n).right := by
  let V := KanSequence.tail (KanSequence.mapping CirclePower.space.{u} X.toKanSequence)
  let r : KanSequence.Hom V V := KanSequence.tailHom
    (KanSequence.mappingPre (CirclePower.integerPowerMap.{u} (-1)) X.toKanSequence)
  have hr : ∀ k, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (r.app k).right :=
    fun k => LoopMappingClasses.pre_neg_one_piIsomorphism (X.level (k + 1)).space
  exact (cotensorProjection_piIsomorphism CirclePower.space X (n + 1)).comp
    (KanSequence.twistMap_piIsomorphism r hr n)

/-- 概要：通常の BF loop 模型から符号を調整した BF loop 模型への厳密な射。
方針：通常の模型の単射構造射を使い、符号を調整した列の cofibrant 比較射へ持ち上げる。
規約：各段の持ち上げは列として同時に構成する。
使われ方：BF 1978 §2、HTT A.3.3。元の対象からの射を通常の loop 模型へ戻す橋渡し。 -/
def signedLoopComparison (X : OmegaSpectrum.{u}) :
    tail (cotensor CirclePower.space.{u} X) ⟶ signedLoopModel X := by
  let g := KanSequence.liftHom
    (X := (tail (cotensor CirclePower.space.{u} X)).toKanSequence)
    (W := (signedLoopModel X).toKanSequence) (Z := KanSequence.signedLoopTail X.toKanSequence)
    (tail (cotensor CirclePower.space.{u} X)).sigma_mono (signedLoopProjection X)
    (fun n =>
      (KanSequence.replacementStage (KanSequence.signedLoopTail X.toKanSequence) n).projection_rlp)
    (signedLoopRawComparison X)
  exact { app := g.app, comm := g.comm }

/-- 概要：BF 比較射を実際の loop 列へ戻すと元の符号反転の反復の比較に一致。
方針：列の持ち上げの因子分解式を取り出す。
規約：各段で点つき射の厳密な等式。
使われ方：BF 1978 §2。比較射の同型性を標準射影で打ち消す。 -/
theorem signedLoopComparison_projection (X : OmegaSpectrum.{u}) (n : ℕ) :
    (signedLoopComparison X).app n ≫ (signedLoopProjection X).app n =
      (signedLoopRawComparison X).app n :=
  KanSequence.liftHom_fac
    (X := (tail (cotensor CirclePower.space.{u} X)).toKanSequence)
    (W := (signedLoopModel X).toKanSequence) (Z := KanSequence.signedLoopTail X.toKanSequence)
    (tail (cotensor CirclePower.space.{u} X)).sigma_mono (signedLoopProjection X)
    (fun n =>
      (KanSequence.replacementStage (KanSequence.signedLoopTail X.toKanSequence) n).projection_rlp)
    (signedLoopRawComparison X) n

/-- 概要：通常の BF loop 模型と符号を調整した模型の比較は各段で全基点 π_* 同型。
方針：標準射影の同型性を、元の Kan 列への比較の同型性から打ち消す。
規約：零次数を含む。
使われ方：Goerss–Jardine I §7、BF 1978 §2。逆方向の厳密な比較射を作る条件。 -/
theorem signedLoopComparison_levelwise (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((signedLoopComparison X).app n).right := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := ((signedLoopProjection X).app n).right) _
    (KanSequence.replacementProjection_piIsomorphism (KanSequence.signedLoopTail X.toKanSequence) n)
  have h := congrArg Under.Hom.right (signedLoopComparison_projection X n)
  change ((signedLoopComparison X).app n).right ≫ ((signedLoopProjection X).app n).right =
    ((signedLoopRawComparison X).app n).right at h
  rw [h]
  exact signedLoopRawComparison_levelwise X n

/-- 概要：通常の BF loop 模型と符号を調整した模型の比較は全整数次数で π_* 同型。
方針：段ごとの全基点の同型性を整数次数へ移す。
規約：coherent nerve の同値との比較は主張しない。
使われ方：HA §1.4.2。有理化の二つの模型の実際の比較。 -/
theorem signedLoopComparison_piIsomorphism (X : OmegaSpectrum.{u}) :
    PiIsomorphism (signedLoopComparison X) :=
  piIsomorphism_of_levelwise _ (signedLoopComparison_levelwise X)

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
