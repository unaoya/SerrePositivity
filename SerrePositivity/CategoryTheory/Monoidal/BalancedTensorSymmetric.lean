module

public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorMonoidal
public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorHexagon

/-! # 可換モノイド上の内部加群の対称モノイダル構造 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  (M : C) [MonObj M] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

/-- 釣り合いテンソル積と商上の交換による内部加群圏の対称モノイダル構造。 -/
instance symmetricCategory : SymmetricCategory (Mod C M) where
  braiding := swapIso M
  braiding_naturality_right := by
    intro E F G f
    exact swap_naturality M (𝟙 E) f
  braiding_naturality_left := by
    intro E F f G
    exact swap_naturality M f (𝟙 G)
  hexagon_forward := hexagon_forward M
  hexagon_reverse := hexagon_reverse M
  symmetry := swapIso_symmetry M

/-- 登録した内部加群のbraidingは構成済みの釣り合い商の交換同型。 -/
lemma braiding_eq_swapIso (E F : Mod C M) : β_ E F = swapIso M E F := rfl

end SerrePositivity.MonoidalBalancedTensor
