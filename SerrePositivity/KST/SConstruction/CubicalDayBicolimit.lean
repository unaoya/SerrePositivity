module
public import SerrePositivity.KST.SConstruction.CubicalDayColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor

/-! # 元の Day tensor による二つの余極限の普遍性
概要：左右の余極限を元の Day tensor に送り、全ての両生成射による普遍性を得る。
方針：各変数の余極限保存を二変数の余錐に適用する。
規約：左右の順序を保つ。使われ方：necklace の生成射上の合成を全体へ降ろす。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits Functor

/-- 元の Day tensor の二変数を curry した関手。 -/
def cubicalDayTensorCurried : CubicalSet.{u} ⥤ CubicalSet.{u} ⥤ CubicalSet.{u} :=
  curry.obj cubicalDayTensorFunctor

/-- curry した元の Day tensor は、各左因子で余極限を保つ。 -/
instance cubicalDayTensorCurried_left_preserves (K : CubicalSet.{u}) :
    PreservesColimitsOfSize.{u, u} (cubicalDayTensorCurried.obj K) :=
  cubicalDayTensorLeft_preservesColimits K

/-- curry した元の Day tensor は、各右因子で余極限を保つ。 -/
instance cubicalDayTensorCurried_right_preserves (L : CubicalSet.{u}) :
    PreservesColimitsOfSize.{u, u} (cubicalDayTensorCurried.flip.obj L) :=
  cubicalDayTensorRight_preservesColimits L

variable {J I : Type u} [Category.{u} J] [Category.{u} I]
  (F : J ⥤ CubicalSet.{u}) (G : I ⥤ CubicalSet.{u})

/-- 元の二つの全図式から元の Day tensor の図式を作る。 -/
def cubicalDayPairDiagram : J × I ⥤ CubicalSet.{u} :=
  uncurry.obj ((whiskeringLeft₂ CubicalSet.{u}).obj F |>.obj G |>.obj
    cubicalDayTensorCurried)

/-- 元の両余極限の生成射の Day tensor による余錐。 -/
def cubicalDayPairCocone : Cocone (cubicalDayPairDiagram F G) :=
  cubicalDayTensorCurried.mapCocone₂ (colimit.cocone F) (colimit.cocone G)

/-- 同じ両余極限の元の Day tensor は、両生成射で生成された余極限。 -/
def cubicalDayPairIsColimit : IsColimit (cubicalDayPairCocone F G) :=
  isColimitOfPreserves₂ cubicalDayTensorCurried (colimit.isColimit F) (colimit.isColimit G)

/-- 二変数の余錐の生成射は元の両生成射の Day tensor を回収する。 -/
lemma cubicalDayPairCocone_ι (j : J) (i : I) :
    (cubicalDayPairCocone F G).ι.app (j, i) =
      cubicalDayTensorMap (colimit.ι F j) (colimit.ι G i) := by
  change cubicalDayTensorMap (colimit.ι F j) (𝟙 (G.obj i)) ≫
    cubicalDayTensorMap (𝟙 (colimit F)) (colimit.ι G i) = _
  rw [← cubicalDayTensorMap_comp, Category.comp_id, Category.id_comp]

end SerrePositivity.KST.SConstruction
