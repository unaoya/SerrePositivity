module

public import SerrePositivity.Spectra.PointedSimplicialSet.MonoidalPrerequisites
public import SerrePositivity.Spectra.Pointed.SmashAdjunction

/-!
# 基点付き単体的集合の内部 Hom と随伴

単体的集合の閉直積構造・等化子・有限余極限から、一般の基点付き内部 Hom を特殊化する。
smash との Hom 同値と随伴を備え、左右の smash が余極限を保存することを得る。
モデル構造や単体的なホモトピー論を仮定しない通常の圏の結果。
smash の閉対称モノイダル構造への登録と API の比較は
`PointedSimplicialSet.Monoidal` で行う。
-/

@[expose] public section

universe u

namespace SerrePositivity.PointedSimplicialSet

open CategoryTheory CategoryTheory.Limits

/-- 基点を保つ写像の内部 Hom。基点は基点で定数となる写像。 -/
noncomputable abbrev internalHom (X Y : PointedSimplicialSet.{u}) : PointedSimplicialSet.{u} :=
  PointedObject.basedHom X Y

/-- 基点付き内部 Hom を行き先に関する関手として扱う。 -/
noncomputable abbrev internalHomFunctor (X : PointedSimplicialSet.{u}) :
    PointedSimplicialSet.{u} ⥤ PointedSimplicialSet.{u} := PointedObject.basedHomFunctor X

/-- 基点付き単体的集合の smash と内部 Hom の随伴。 -/
noncomputable def smashHomAdjunction (X : PointedSimplicialSet.{u}) :
    (PointedObject.smashFunctor (C := SSet.{u})).obj X ⊣ internalHomFunctor X :=
  PointedObject.smashHomAdjunction X

/-- 左からの smash は余極限を保存する。 -/
lemma smashLeft_preservesColimits (X : PointedSimplicialSet.{u}) :
    PreservesColimits ((PointedObject.smashFunctor (C := SSet.{u})).obj X) := inferInstance

/-- 右からの smash も余極限を保存する。 -/
lemma smashRight_preservesColimits (X : PointedSimplicialSet.{u}) :
    PreservesColimits ((PointedObject.smashFunctor (C := SSet.{u})).flip.obj X) := inferInstance

end SerrePositivity.PointedSimplicialSet
