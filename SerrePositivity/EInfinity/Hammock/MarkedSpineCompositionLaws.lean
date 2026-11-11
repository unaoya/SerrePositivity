module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineCompositionMaps
public import SerrePositivity.EInfinity.Hammock.AllMarkedUnitPoints

/-!
# 元の全因子列の合成の単位則と結合則

概要：指定終端の元の単位を使って全因子列の合成公理を証明する。
方針：貼り戻しの単射性・合成保存と元の hammock の合成公理を使う。
規約：明示的な因子列の合成を保持する。
使われ方：自由積の実際の単体的豊穣圏。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C}
  {X Y Z T : Paths C} {n : SimplexCategoryᵒᵖ}

def unitPoint (W : MorphismProperty C) (X : Paths C) (n : SimplexCategoryᵒᵖ) :
    MarkedSpine W X n X := nil X (AllMarked.nativeUnitPoint W X n)

lemma glue_unit (W : MorphismProperty C) (X : Paths C) (n : SimplexCategoryᵒᵖ) :
    glue (unitPoint W X n) = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W.paths X).app n PUnit.unit :=
  AllMarked.inclusion_unitPoint W X n

lemma append_left_unit (t : MarkedSpine W Y n X) : append (unitPoint W X n) t = t := by
  apply glue_injective
  rw [glue_append, glue_unit, ← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint_identity]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_identity_left W.paths (glue t)

lemma append_right_unit (t : MarkedSpine W Y n X) : append t (unitPoint W Y n) = t := by
  apply glue_injective
  rw [glue_append, glue_unit, ← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint_identity]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_identity_right W.paths (glue t)

lemma append_assoc (s : MarkedSpine W Y n X) (t : MarkedSpine W Z n Y)
    (r : MarkedSpine W T n Z) : append (append s t) r = append s (append t r) := by
  apply glue_injective
  simp only [glue_append, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_assoc]

def unitMap (W : MorphismProperty C) (X : Paths C) : 𝟙_ SSet.{u} ⟶ space W X X where
  app n := ↾fun _ => unitPoint W X n
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    intro p
    exact (congrArg (nil X) (AllMarked.nativeUnitPoint_simplex W X θ)).symm

lemma unitMap_gluing (W : MorphismProperty C) (X : Paths C) :
    unitMap W X ≫ gluing W X X = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W.paths X := by
  ext n p
  exact glue_unit W X n

lemma composition_left_unit (W : MorphismProperty C) (X Y : Paths C) :
    (unitMap W X ⊗ₘ 𝟙 (space W Y X)) ≫ composition W X X Y = (λ_ (space W Y X)).hom := by
  ext n p
  exact append_left_unit p.2

lemma composition_right_unit (W : MorphismProperty C) (X Y : Paths C) :
    (𝟙 (space W Y X) ⊗ₘ unitMap W Y) ≫ composition W X Y Y = (ρ_ (space W Y X)).hom := by
  ext n p
  exact append_right_unit p.1

lemma composition_assoc (W : MorphismProperty C) (X Y Z T : Paths C) :
    (composition W X Y Z ⊗ₘ 𝟙 (space W T Z)) ≫ composition W X Z T =
      (α_ (space W Y X) (space W Z Y) (space W T Z)).hom ≫
        (𝟙 (space W Y X) ⊗ₘ composition W Y Z T) ≫ composition W X Y T := by
  ext n p
  exact append_assoc p.1.1 p.1.2 p.2

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
