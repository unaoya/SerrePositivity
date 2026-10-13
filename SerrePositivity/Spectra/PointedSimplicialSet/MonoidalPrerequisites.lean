module

public import SerrePositivity.Spectra.PointedSimplicialSet.Spheres
public import SerrePositivity.Spectra.Pointed.SmashUnit
public import SerrePositivity.Spectra.Pointed.SmashPentagon
public import SerrePositivity.Spectra.Pointed.SmashHexagon
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# 単体的集合の閉構造と smash 積の単位への接続

## 基礎圏の性質

Mathlib の型への関手圏の閉構造を、単体的集合に適用する。
各対象との直積が余極限を保存するため、一般論で必要な保存条件を供給できる。
基点付き単体的集合の smash の左右単位同型を、自由な基点を持つ零次球面について得る。

## 未構成の範囲

ここで使う閉構造は基礎圏 SSet の直積についてのもの。
基点付き内部 Hom と随伴は `PointedSimplicialSet.InternalHom` で構成する。
smash の結合子は三変数の普遍性から構成したものに接続する。
pentagon と二つの hexagon は、標準射へ引き戻して証明済み。
単位との triangle と構造の登録は、
`Pointed.SmashTriangle` と `PointedSimplicialSet.Monoidal` で確認する。
基礎圏の閉構造だけから、それらが自動的に構成済みとはしない。
-/

@[expose] public section

universe u

namespace SerrePositivity.PointedSimplicialSet

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

/-- 単体的集合との左からの直積は余極限を保存する。閉構造の左随伴性による。 -/
lemma tensorLeft_preservesColimits (X : SSet.{u}) : PreservesColimits (tensorLeft X) :=
  inferInstance

/-- 単体的集合との右からの直積も余極限を保存する。
直積の交換同型により、左からの直積の左随伴性に帰着する。 -/
lemma tensorRight_preservesColimits (X : SSet.{u}) : PreservesColimits (tensorRight X) := by
  let := BraidedCategory.ofCartesianMonoidalCategory (C := SSet.{u})
  infer_instance

/-- 基点付き単体的集合の smash 積の左単位同型。 -/
noncomputable def smashLeftUnitor (X : PointedSimplicialSet.{u}) :
    PointedObject.smash sphereZero X ≅ X := PointedObject.smashLeftUnitor X

/-- 基点付き単体的集合の smash 積の右単位同型。 -/
noncomputable def smashRightUnitor (X : PointedSimplicialSet.{u}) :
    PointedObject.smash X sphereZero ≅ X := PointedObject.smashRightUnitor X

/-- 基点付き単体的集合の smash 積の結合同型。 -/
noncomputable def smashAssociator (X Y Z : PointedSimplicialSet.{u}) :
    PointedObject.smash (PointedObject.smash X Y) Z ≅
      PointedObject.smash X (PointedObject.smash Y Z) := PointedObject.smashAssociator X Y Z

end SerrePositivity.PointedSimplicialSet
