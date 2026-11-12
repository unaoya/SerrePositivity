module

public import SerrePositivity.KST.Spectra.SignedAdjointParametricCoordinates
public import SerrePositivity.KST.Spectra.PointedParametricPostExchange
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget

/-!
概要：二つの実入力区間の全族合成に使う、二重 loop 入力と共通中間射の厳密座標。
方針：標準全族作用の転置表示と交換同型の標的自然性を同じ射の族へ適用する。
規約：頂点ごとの一致に還元しない。使われ方：実入力比較区間の端点照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.SignedAdjointPaths
open LoopExchangePaths

/-- 第二入力の実比較を内部 Hom と交換へ移した始点は、元の合成入力の全族像。 -/
lemma inputParametricFirst_start {P A Y Z Z' : PointedSimplicialSet.{u}}
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
    (v : P ⟶ PointedObject.basedHom Z Z') :
    (f ≫ PointedObject.basedHomMap CirclePower.space.{u}
      (g ≫ PointedMapping.parametricPost CirclePower.space.{u} v)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} P
          (PointedObject.basedHom CirclePower.space.{u} Z')).hom =
      input f g ≫ doubleParametricPost v := by
  let K : PointedSimplicialSet.{u} := CirclePower.space.{u}
  have he := PointedMapping.parametricPost_exchange K
    (v ≫ PointedMapping.ihomAction K Z Z')
  change doubleParametricPost v =
    PointedObject.basedHomMap K (PointedMapping.parametricPost K v) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K P (PointedObject.basedHom K Z')).hom at he
  have hm : PointedObject.basedHomMap K (g ≫ PointedMapping.parametricPost K v) =
      PointedObject.basedHomMap K g ≫
        PointedObject.basedHomMap K (PointedMapping.parametricPost K v) :=
    CategoryTheory.Functor.map_comp (ihom K) _ _
  rw [hm, he]
  exact Category.assoc _ _ _

/-- 第二入力比較の終点は、第一入力比較へ同じ後合成を付けた始点と厳密に一致。 -/
lemma inputParametricFirst_finish {P A Y Y' Z' : PointedSimplicialSet.{u}}
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g' : Y' ⟶ PointedObject.basedHom CirclePower.space.{u} Z')
    (u : P ⟶ PointedObject.basedHom Y Y') :
    (f ≫ PointedObject.basedHomMap CirclePower.space.{u}
      (PointedMapping.transpose u ≫ PointedObject.basedHomMap P g')) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} P
          (PointedObject.basedHom CirclePower.space.{u} Z')).hom =
      (f ≫ PointedMapping.parametricPost CirclePower.space.{u} u) ≫
        PointedObject.basedHomMap P (PointedObject.basedHomMap CirclePower.space.{u} g') := by
  let K : PointedSimplicialSet.{u} := CirclePower.space.{u}
  have hn := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget.natural_post K P g'
  change PointedObject.basedHomMap K (PointedObject.basedHomMap P g') ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K P (PointedObject.basedHom K Z')).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K P Y').hom ≫
      PointedObject.basedHomMap P (PointedObject.basedHomMap K g') at hn
  have hm : PointedObject.basedHomMap K
      (PointedMapping.transpose u ≫ PointedObject.basedHomMap P g') =
    PointedObject.basedHomMap K (PointedMapping.transpose u) ≫
      PointedObject.basedHomMap K (PointedObject.basedHomMap P g') :=
    CategoryTheory.Functor.map_comp (ihom K) _ _
  rw [hm, PointedMapping.parametricPost_exchange K u]
  simp only [Category.assoc]
  rw [hn]

end SerrePositivity.KST.Spectra.SignedAdjointPaths
