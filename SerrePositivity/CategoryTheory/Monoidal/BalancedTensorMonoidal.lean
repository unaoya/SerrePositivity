module

public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorPentagon
public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorTriangle

/-! # 可換モノイド上の内部加群のモノイダル構造 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (M : C) [MonObj M] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

/-- 釣り合いテンソル積、正則加群と構成済みの比較同型によるモノイダル構造のデータ。 -/
instance monoidalCategoryStruct : MonoidalCategoryStruct (Mod C M) where
  tensorObj := moduleObj M
  tensorHom := moduleMap M
  whiskerLeft E {_ _} f := moduleMap M (𝟙 E) f
  whiskerRight {_ _} f F := moduleMap M f (𝟙 F)
  tensorUnit := Mod.regular M
  associator := associatorIso M
  leftUnitor := leftUnitIso M
  rightUnitor := rightUnitIso M

/-- 釣り合いテンソル積は可換モノイド上の内部加群圏をモノイダル圏にする。 -/
instance monoidalCategory : MonoidalCategory (Mod C M) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun E F => Mod.hom_ext _ _ (map_id M E F))
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := fun f g f' g' =>
      Mod.hom_ext _ _ (map_comp M f f' g g').symm)
    (associator_naturality := fun f g h => associator_naturality M f g h)
    (leftUnitor_naturality := fun f => leftUnit_naturality M f)
    (rightUnitor_naturality := fun f => rightUnit_naturality M f)
    (pentagon := pentagon M)
    (triangle := triangle M)

end SerrePositivity.MonoidalBalancedTensor
