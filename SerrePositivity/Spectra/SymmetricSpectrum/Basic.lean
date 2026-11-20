module

public import SerrePositivity.Spectra.General.MappingEnrichment
public import SerrePositivity.Spectra.General.StructureMaps
public import SerrePositivity.Spectra.General.TensorFreeAtSum
public import SerrePositivity.Spectra.SymmetricSequence.SphereCommMonoid

/-! # 円周を座標とする対称スペクトル

概要：対称スペクトルの型、自由対象と評価、構造射、テンソルと余テンソル、
内部 Hom・基点付き写像対象、懸垂とループを扱う。
方針：一般の `GeneralSymmetricSpectrum` の座標を円周に固定する。
自由対象と評価は `freeFunctor`・`freeAt`・`evaluation`、各段の作用は
`pointwiseTensorFunctor`・`cotensorFunctor` とその随伴を使う。
基点付き写像対象は `mappingObjectBifunctor` と `mappingEnrichedOrdinaryCategory` で表す。
規約：構造射は和次数へ向かい、左右ブロックの置換を保つ。
使われ方：球面スペクトル、単体集合の作用、レベルモデルと安定化の入口。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity

/-- 球面対称列のモノイド上の内部加群としての対称スペクトル。 -/
abbrev SymmetricSpectrum :=
  GeneralSymmetricSpectrum PointedSimplicialSet.{u} PointedSimplicialSet.circle

namespace SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open GeneralSymmetricSpectrum (action level structureMap)
open PointedSimplicialSet

/-- 球面の加群作用を忘れる関手。 -/
abbrev forget := GeneralSymmetricSpectrum.forget circle.{u}

/-- 対称列Fを生成元とする自由球面加群。 -/
abbrev freeObj := GeneralSymmetricSpectrum.freeObj circle.{u}

/-- 対称列から自由対称スペクトルを作る関手。 -/
abbrev freeFunctor := GeneralSymmetricSpectrum.freeFunctor circle.{u}

/-- 対称列から自由対称スペクトルへの生成元の射。 -/
abbrev generator := GeneralSymmetricSpectrum.generator circle.{u}

/-- スペクトルの置換作用を忘れた第n段の評価。 -/
abbrev evaluation := GeneralSymmetricSpectrum.evaluation (K := circle.{u})

/-- 基点付き単体的集合から第n段を生成する自由スペクトル関手F_n。 -/
abbrev freeAt := GeneralSymmetricSpectrum.freeAt (K := circle.{u})

/-- F_nと第n段の評価との随伴。 -/
abbrev freeAtAdjunction := GeneralSymmetricSpectrum.freeAtAdjunction (K := circle.{u})

/-- F_n Xの第n段への生成元の射。 -/
abbrev freeAtGenerator := GeneralSymmetricSpectrum.freeAtGenerator (K := circle.{u})

/-- 各次数の構造射は左右ブロックの置換と両立する。 -/
lemma structureMap_equivariance (E : SymmetricSpectrum.{u}) (p q : ℕ)
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    PointedObject.smashMap (spherePermutationAction.{u} p σ).asIso.hom
        (E.X.map (FiniteBijection.permutation q τ)) ≫ structureMap E p q =
      structureMap E p q ≫ E.X.map
        (FiniteBijection.sumMap (FiniteBijection.permutation p σ)
          (FiniteBijection.permutation q τ)) := by
  rw [← sphereSequence_map_permutation]
  exact GeneralSymmetricSpectrum.structureMap_equivariance E p q σ τ

/-- スペクトルの構造射は一般のconvolutionの次数成分に一致する。 -/
lemma structureMap_eq_convolutionComponent (E : SymmetricSpectrum.{u}) (p q : ℕ) :
    structureMap E p q =
      SymmetricSequence.convolutionComponent (action E)
        (FiniteBijection.of p) (FiniteBijection.of q) := by
  rfl

/-- F_m XとF_n Yの積は、和次数からXとYのsmashを生成する自由スペクトルと同型。 -/
abbrev sphereTensorFreeAtSum := GeneralSymmetricSpectrum.tensorFreeAtSum (K := circle.{u})

/-- 各段のsmashを持つテンソルの値域スペクトルに関する関手。 -/
abbrev pointwiseTensorFunctor := GeneralSymmetricSpectrum.pointwiseTensorFunctor (K := circle.{u})

/-- F_0 Xとの全体の比較は値域スペクトルに関する自然同型。 -/
abbrev sphereTensorFreeZeroPointwiseNatIso := GeneralSymmetricSpectrum.tensorFreeZeroPointwiseNatIso (K := circle.{u})

/-- 各段のsmashを持つテンソルは生成対象と値域スペクトルに共変な二変数関手。 -/
abbrev pointwiseTensorBifunctor := GeneralSymmetricSpectrum.pointwiseTensorBifunctor (K := circle.{u})

/-- 各段のsmashを持つテンソルの反復と入力のsmashの自然比較。 -/
abbrev pointwiseTensorAssociatorNatIso := GeneralSymmetricSpectrum.pointwiseTensorAssociatorNatIso (K := circle.{u})

/-- 単位比較を値域スペクトルに関する自然同型へまとめる。 -/
abbrev pointwiseTensorUnitNatIso := GeneralSymmetricSpectrum.pointwiseTensorUnitNatIso (K := circle.{u})

/-- cotensorの値域スペクトルに関する関手。 -/
abbrev cotensorFunctor := GeneralSymmetricSpectrum.cotensorFunctor (K := circle.{u})

/-- 各段の通常のsmashを持つテンソルはcotensor関手の左随伴。 -/
abbrev pointwiseTensorCotensorAdjunction :=
  GeneralSymmetricSpectrum.pointwiseTensorCotensorAdjunction (K := circle.{u})

/-- 原変数に反変な内部Homの二変数関手。 -/
abbrev internalHomBifunctor := MonoidalModuleInternalHom.homBifunctor sphereSequence.{u}

/-- 基点付き写像対象は原変数に反変、値域に共変な二変数関手。 -/
abbrev pointedMappingSpaceBifunctor :=
  GeneralSymmetricSpectrum.mappingObjectBifunctor (K := circle.{u})

/-- 各段のsmashと写像対象の、スペクトル変数に関して自然な随伴。 -/
abbrev pointedMappingSpaceParametrizedAdjunction :=
  MonoidalMappingAdjunction.transportedParametrizedAdjunction (freeAtAdjunction.{u} 0)
    pointwiseTensorBifunctor.{u} GeneralSymmetricSpectrum.mappingTensorNatIso
    (fun {_ _} f X ↦ (GeneralSymmetricSpectrum.tensorFreeZeroPointwiseNatIso X).hom.naturality f)

/-- 基点付き写像対象の豊穣構造を既存の通常の圏構造へ接続する。 -/
abbrev pointedMappingEnrichedOrdinaryCategory :=
  GeneralSymmetricSpectrum.mappingEnrichedOrdinaryCategory (K := PointedSimplicialSet.circle.{u})

/-- 円の各段のsmashによる懸垂関手。 -/
abbrev suspensionFunctor :=
  GeneralSymmetricSpectrum.pointwiseTensorFunctor (K := circle.{u}) circle

/-- 円周で特殊化した余テンソル関手としてのループ関手。 -/
abbrev loopFunctor := GeneralSymmetricSpectrum.cotensorFunctor (K := circle.{u}) circle

/-- 懸垂とループの随伴。 -/
abbrev suspensionLoopAdjunction :=
  GeneralSymmetricSpectrum.pointwiseTensorCotensorAdjunction (K := circle.{u}) circle

end SymmetricSpectrum
end SerrePositivity
