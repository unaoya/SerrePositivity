module

public import SerrePositivity.KST.Spectra.AdjointLoopRelativeBF
public import SerrePositivity.KST.Spectra.AdjointLoopParameterHom
public import SerrePositivity.KST.Spectra.RawSpectrumParameterHomFamilies
public import SerrePositivity.KST.Spectra.RawSpectrumMappingPrecomposition
public import SerrePositivity.KST.Spectra.PointedPrecompositionNaturality

/-!
概要：元の補助単位の相対 BF 左因子と右射影を同じ全パラメータ族で照合する。
方針：元の単位の厳密自然性へ実分解式を代入し、元の全 Raw Hom の境界へ移す。
規約：右射影の自然性を左因子の自然性だけから推論しない。
使われ方：二変数 corner へ与える指定境界の実構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 概要：元の全パラメータ族の補助標的への作用。
方針：元の一段移動した族へ補助 loop を施す。
規約：パラメータの Kan 性を要求しない。
使われ方：相対右射影の指定した射影先の族。 -/
def targetParameterHom (X Y : OmegaSpectrum.{u}) {P : PointedSimplicialSet.{u}}
    (f : KanSequence.Hom X.toKanSequence (KanSequence.mapping P Y.toKanSequence)) :
    KanSequence.Hom (target X) (KanSequence.mapping P (target Y)) :=
  KanSequence.adjointLoopParameterHom (KanSequence.tailHom f)

/-- 概要：相対置換の元の右射影から指定補助標的へ進む全パラメータ族。
方針：元の右射影と補助標的の全パラメータ作用を合成する。
規約：元の右射影の各段の射を保持する。
使われ方：二変数 corner の標的側の境界。 -/
def projectionParameterHom (X Y : OmegaSpectrum.{u}) {P : PointedSimplicialSet.{u}}
    (f : KanSequence.Hom X.toKanSequence (KanSequence.mapping P Y.toKanSequence)) :
    KanSequence.Hom (middle X).toKanSequence (KanSequence.mapping P (target Y)) :=
  (projection X).comp (targetParameterHom X Y f)

/-- 概要：元の全パラメータ族から指定相対左因子へ進む族。
方針：元の族へ同じ相対左因子の後合成を施す。
規約：別の代表射やホモトピー類へ移さない。
使われ方：二変数 corner の源側の境界。 -/
def inclusionParameterHom (X Y : OmegaSpectrum.{u}) {P : PointedSimplicialSet.{u}}
    (f : KanSequence.Hom X.toKanSequence (KanSequence.mapping P Y.toKanSequence)) :
    KanSequence.Hom X.toKanSequence (KanSequence.mapping P (middle Y).toKanSequence) :=
  f.comp (KanSequence.mappingPost P
    (⟨(inclusion Y).app, (inclusion Y).comm⟩ :
      KanSequence.Hom Y.toKanSequence (middle Y).toKanSequence))

/-- 概要：指定左因子と右射影を同時に保つ全パラメータ境界の厳密可換性。
方針：元の単位の全パラメータ自然性と各段の実分解式を使う。
規約：corner に渡す境界可換性を明示入力に残さない。
使われ方：相対 BF 右射影の全 Hom 自然性の実境界。 -/
lemma parameterBoundary_comm (X Y : OmegaSpectrum.{u}) {P : PointedSimplicialSet.{u}}
    (f : KanSequence.Hom X.toKanSequence (KanSequence.mapping P Y.toKanSequence)) :
    (⟨(inclusion X).app, (inclusion X).comm⟩ :
        KanSequence.Hom X.toKanSequence (middle X).toKanSequence).comp
      (projectionParameterHom X Y f) =
    (inclusionParameterHom X Y f).comp (KanSequence.mappingPost P (projection Y)) := by
  apply KanSequence.Hom.ext_app
  intro n
  change (inclusion X).app n ≫
      ((projection X).app n ≫ (targetParameterHom X Y f).app n) =
    (f.app n ≫ (ihom P).map ((inclusion Y).app n)) ≫
      (ihom P).map ((projection Y).app n)
  rw [← Category.assoc, fac X n, Category.assoc, ← CategoryTheory.Functor.map_comp, fac Y n]
  exact (congrArg (fun g ↦ KanSequence.Hom.app g n)
    (KanSequence.adjointLoopTailUnit_parameter_natural f)).symm

/-- 概要：右射影の指定族を元の全 Raw Hom の点つきパラメータ族へ移す。
方針：構成した厳密な列射を元のパラメータ族へ戻す。
規約：元の補助標的と右射影を保持する。
使われ方：元の二変数 corner の射影先の指定。 -/
def projectionParameterFamily (X Y : OmegaSpectrum.{u}) (P : PointedSimplicialSet.{u})
    (f : KanSequence.Hom X.toKanSequence (KanSequence.mapping P Y.toKanSequence)) :
    P ⟶ RawSpectrumMapping.pointedSpace (middle X) (target Y) :=
  RawSpectrumMapping.parameterFamily (middle X) (target Y) P (projectionParameterHom X Y f)

/-- 概要：左因子の指定族を元の全 Raw Hom の点つきパラメータ族へ移す。
方針：構成した源側の列射を同じパラメータ族へ戻す。
規約：指定左因子の各段の射を保持する。
使われ方：元の二変数 corner の源上の指定。 -/
def inclusionParameterFamily (X Y : OmegaSpectrum.{u}) (P : PointedSimplicialSet.{u})
    (f : KanSequence.Hom X.toKanSequence (KanSequence.mapping P Y.toKanSequence)) :
    P ⟶ RawSpectrumMapping.pointedSpace X (middle Y).toKanSequence :=
  RawSpectrumMapping.parameterFamily X (middle Y).toKanSequence P (inclusionParameterHom X Y f)

/-- 概要：同じ指定二境界は元の全 Raw Hom の全単体上で厳密可換。
方針：全段評価で転置の源・標的自然性を使い、実列射の可換式へ戻す。
規約：指定単位を各対象の同値だけで置き換えない。
使われ方：元の二変数 corner の実引き戻しへの接続。 -/
lemma parameterFamilyBoundary_comm (X Y : OmegaSpectrum.{u}) (P : PointedSimplicialSet.{u})
    (f : KanSequence.Hom X.toKanSequence (KanSequence.mapping P Y.toKanSequence)) :
    projectionParameterFamily X Y P f ≫
      RawSpectrumMapping.pointedPre (inclusion X) (target Y) =
    inclusionParameterFamily X Y P f ≫ RawSpectrumMapping.pointedPost X (projection Y) := by
  apply RawSpectrumMapping.pointed_hom_ext X (target Y)
  intro n
  dsimp only [projectionParameterFamily, inclusionParameterFamily]
  rw [Category.assoc, RawSpectrumMapping.pointedPre_evaluation, ← Category.assoc,
    RawSpectrumMapping.parameterFamily_evaluation]
  rw [Category.assoc, RawSpectrumMapping.pointedPost_evaluation, ← Category.assoc,
    RawSpectrumMapping.parameterFamily_evaluation]
  rw [← PointedMapping.transpose_pre_outer]
  exact (congrArg PointedMapping.transpose
    (congrArg (fun g ↦ KanSequence.Hom.app g n) (parameterBoundary_comm X Y f))).trans
      (PointedMapping.transpose_post ((inclusionParameterHom X Y f).app n)
        ((projection Y).app n))

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
