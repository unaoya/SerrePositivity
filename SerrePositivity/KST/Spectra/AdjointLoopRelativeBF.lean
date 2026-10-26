module

public import SerrePositivity.KST.Spectra.AdjointLoopUnitRawHom
public import SerrePositivity.KST.Spectra.CofibrantSequenceLifting
public import SerrePositivity.KST.NonConnective.SequentialRelativeCofibration

/-!
概要：元の補助 loop 単位の相対 BF 分解を実構成する。
方針：標的の絶対 BF 置換へ単位を持ち上げ、既存の BF 射の相対分解を適用する。
規約：持ち上げの選択から関手性を結論しない。nativeLoop は変更しない。
使われ方：全 Hom の比較へ接続する相対 cofibration と厳密な右射影。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.KST.NonConnective
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 概要：元の BF 対象の一段移動した補助 loop 列。
方針：元の Kan 列の厳密な随伴単位の標的を使う。
規約：元の nativeLoop の定義ではない。
使われ方：同じ単位を回収する相対分解の標的。 -/
def target (X : OmegaSpectrum.{u}) : KanSequence.{u} :=
  KanSequence.adjointLoop (KanSequence.tail X.toKanSequence)

/-- 概要：補助標的は実際に Ω 条件を満たす。
方針：元の Ω 条件を一段ずらし、補助 loop の保存則を適用する。
規約：構造射の単射性を追加仮定しない。
使われ方：絶対 BF 置換の実入力。 -/
lemma target_omega (X : OmegaSpectrum.{u}) : (target X).OmegaCondition :=
  KanSequence.adjointLoop_omegaCondition (fun n ↦ X.omega_condition (n + 1))

/-- 概要：元の単位を補助標的の絶対 BF 置換へ厳密に持ち上げる。
方針：BF 源の単射構造と置換射影の全単射 RLP を適用する。
規約：選択した持ち上げに自然性を仮定しない。
使われ方：既存の BF 射の相対分解を使うための実射。 -/
def liftedUnit (X : OmegaSpectrum.{u}) :
    X ⟶ (target X).cofibrantOmegaSpectrum (target_omega X) := by
  let f := KanSequence.liftHom X.sigma_mono
    ((target X).cofibrantOmegaProjection (target_omega X))
    (fun n ↦ ((target X).replacementStage n).projection_rlp)
    (KanSequence.adjointLoopTailUnit X.toKanSequence)
  exact ⟨f.app, f.comm⟩

/-- 概要：持ち上げと元の置換射影の合成は元の随伴単位そのもの。
方針：既存の持ち上げの厳密な因子分解式を取り出す。
規約：各段の点つき射の等式。
使われ方：相対分解で指定終点を変えない照合。 -/
lemma liftedUnit_projection (X : OmegaSpectrum.{u}) (n : ℕ) :
    (liftedUnit X).app n ≫
      ((target X).cofibrantOmegaProjection (target_omega X)).app n =
        (KanSequence.adjointLoopTailUnit X.toKanSequence).app n :=
  KanSequence.liftHom_fac X.sigma_mono _
    (fun k ↦ ((target X).replacementStage k).projection_rlp) _ n

/-- 概要：元の補助単位の相対 BF 分解の実中間対象。
方針：持ち上げた BF 射に所有正本の相対分解を使う。
規約：K-B の相対 latching 帰納を複製しない。
使われ方：全 Hom での相対比較の対象。 -/
def middle (X : OmegaSpectrum.{u}) : OmegaSpectrum.{u} :=
  sequentialBFArrowMiddle (liftedUnit X)

/-- 概要：元の源から実中間 BF 対象への左因子。
方針：既存の相対分解の左因子を使う。
規約：元の BF 源のまま構成する。
使われ方：相対 latching 単射条件を持つ比較。 -/
def inclusion (X : OmegaSpectrum.{u}) : X ⟶ middle X :=
  sequentialBFArrowLeft (liftedUnit X)

/-- 概要：実中間 BF 対象から元の補助標的への右因子。
方針：相対分解の右因子と絶対 BF 置換射影を合成する。
規約：標的を別の BF 代表に変えない。
使われ方：元の単位の厳密回収。 -/
def projection (X : OmegaSpectrum.{u}) : KanSequence.Hom (middle X).toKanSequence (target X) :=
  (⟨(sequentialBFArrowRight (liftedUnit X)).app,
    (sequentialBFArrowRight (liftedUnit X)).comm⟩ :
      KanSequence.Hom (middle X).toKanSequence
        ((target X).cofibrantOmegaSpectrum (target_omega X)).toKanSequence).comp
    ((target X).cofibrantOmegaProjection (target_omega X))

/-- 概要：相対分解の両因子は各段で元の補助単位を厳密に回収する。
方針：BF 分解の合成式と持ち上げの射影式をつなぐ。
規約：元の構造随伴そのものの等式。
使われ方：全 Hom 比較の指定単位の境界条件。 -/
lemma fac (X : OmegaSpectrum.{u}) (n : ℕ) :
    (inclusion X).app n ≫ (projection X).app n =
      (KanSequence.adjointLoopTailUnit X.toKanSequence).app n := by
  change (sequentialBFArrowLeft (liftedUnit X)).app n ≫
    ((sequentialBFArrowRight (liftedUnit X)).app n ≫ _) = _
  rw [← Category.assoc]
  have h := congrArg (fun f ↦ OmegaSpectrum.Hom.app f n)
    (sequentialBFArrow_fac (liftedUnit X))
  change (sequentialBFArrowLeft (liftedUnit X)).app n ≫
    (sequentialBFArrowRight (liftedUnit X)).app n = (liftedUnit X).app n at h
  rw [h, liftedUnit_projection]

/-- 概要：左因子の零段と全ての相対 latching 射は実際に単射。
方針：所有正本の相対分解の検証を適用する。
規約：cofibration のモデル圏 instance を入力しない。
使われ方：後続の全 Hom の相対充填。 -/
lemma inclusion_relative (X : OmegaSpectrum.{u}) :
    IsSequentialRelativeCofibration (inclusion X) :=
  sequentialBFArrowLeft_isRelativeCofibration (liftedUnit X)

/-- 概要：右因子は全ての段で全単射に対する RLP を持つ。
方針：二つの実射影の RLP を合成する。
規約：元の補助標的への射そのものを検証する。
使われ方：全 Hom の実 trivial fibration への適用。 -/
lemma projection_rlp (X : OmegaSpectrum.{u}) (n : ℕ) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp ((projection X).app n).right :=
  (MorphismProperty.monomorphisms SSet.{u}).rlp.comp_mem _ _
    (sequentialBFArrowRight_rlp (liftedUnit X) n)
    ((target X).replacementStage n).projection_rlp

/-- 概要：相対分解の左因子も各段で元の全基点 π 同型。
方針：元の単位の π 同型から右因子の全単射 RLP を打ち消す。
規約：構成した左因子の射そのものの検証。
使われ方：BF 比較の同値性。 -/
lemma inclusion_levelwise (X : OmegaSpectrum.{u}) (n : ℕ) :
    KanPiIsomorphism ((inclusion X).app n).right := by
  apply KanPiIsomorphism.of_comp (g := ((projection X).app n).right) _
    (kanPiIsomorphism_of_monoRight _ (projection_rlp X n))
  rw [← Under.comp_right, fac]
  exact KanSequence.adjointLoopTailUnit_levelwise X.toKanSequence_omega n

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
