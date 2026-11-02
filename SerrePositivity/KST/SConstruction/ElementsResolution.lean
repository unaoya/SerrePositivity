module
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ElementsChainLifting
public import Mathlib.CategoryTheory.Category.Cat.Op
public import Mathlib.CategoryTheory.Functor.Currying
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence

/-! # 単体集合値図式の二重単体解消
概要：各次数の要素の圏の反対圏の nerve により、反変図式の二重単体解消を構成する。
方針：図式を転置し、要素の圏・反対圏・nerve の関手を合成する。
規約：係数の Kan 性や余極限の存在は要求しない。使われ方：単体積版 Quillen A。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 概要：各次数の係数の要素の圏の反対圏の nerve による二重単体解消。
方針：二変数を交換して要素の圏の関手に渡す。
規約：対象・射の宇宙の最大値にそろえる。使われ方：fiber 図式の解消。 -/
def elementsResolution {J : Type u} [Category.{v} J]
    (F : J ⥤ SSet.{max u v}) : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} :=
  F.flip ⋙ Functor.elementsFunctor ⋙ Cat.opFunctor ⋙ nerveFunctor

/-- 概要：係数の自然変換は二重単体解消の射を与える。
方針：転置した自然変換に要素の圏・反対圏・nerve を適用する。
規約：元の自然変換の各成分を保つ。使われ方：fiber 図式と定値図式の比較。 -/
def elementsResolutionMap {J : Type u} [Category.{v} J]
    {F G : J ⥤ SSet.{max u v}} (η : F ⟶ G) : elementsResolution F ⟶ elementsResolution G :=
  Functor.whiskerRight ((flipFunctor J SimplexCategoryᵒᵖ (Type (max u v))).map η)
    (Functor.elementsFunctor ⋙ Cat.opFunctor ⋙ nerveFunctor)

/-- 概要：二重単体解消の固定した係数次数での行は要素の圏の反対圏の nerve。
方針：合成した関手の対象を展開する。
規約：型の厳密な等号。使われ方：各 x 上の縮約可能な圏による augmentation の比較。 -/
lemma elementsResolution_obj {J : Type u} [Category.{v} J]
    (F : J ⥤ SSet.{max u v}) (n : SimplexCategoryᵒᵖ) :
    (elementsResolution F).obj n = nerve (F.flip.obj n).Elementsᵒᵖ := rfl

/-- 概要：解消の比較の固定次数での射は元の自然変換が誘導する要素の圏の射。
方針：関手の合成の射を展開する。
規約：全単体での等号。使われ方：対象ごとの比較と二重単体解消の射の照合。 -/
lemma elementsResolutionMap_app {J : Type u} [Category.{v} J]
    {F G : J ⥤ SSet.{max u v}} (η : F ⟶ G) (n : SimplexCategoryᵒᵖ) :
    (elementsResolutionMap η).app n = nerveMap (η.flipApp n).mapElements.op := rfl

end SerrePositivity.KST.SConstruction
