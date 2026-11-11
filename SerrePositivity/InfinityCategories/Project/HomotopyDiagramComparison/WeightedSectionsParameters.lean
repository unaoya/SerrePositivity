module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedFunctor

/-!
概要：係数図式のパラメータ付き射を重み付き end の全パラメータの射へ移す。
方針：普遍切断を追加パラメータと tensor し、成分で後合成して end へ持ち上げる。
規約：パラメータの Kan 性・有限性・可縮性は要求しない。
使われ方：HTT 4.2.4.1 の豊穣作用と weighted nerve の普遍評価の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {I : Type u} [SmallCategory I]

/-- 切断のパラメータと係数の変換のパラメータを結合した自然変換。 -/
def weightedSectionParameterTransform {W H H' : I ⥤ SSet.{u}} {A B : SSet.{u}}
    (s : W ⊗ (Functor.const I).obj A ⟶ H) (η : H ⋙ tensorRight B ⟶ H') :
    W ⊗ (Functor.const I).obj (A ⊗ B) ⟶ H' where
  app i := (α_ (W.obj i) A B).inv ≫ (s.app i ▷ B) ≫ η.app i
  naturality i j f := by
    change (W.map f ▷ (A ⊗ B)) ≫ (α_ (W.obj j) A B).inv ≫
        (s.app j ▷ B) ≫ η.app j =
      ((α_ (W.obj i) A B).inv ≫ (s.app i ▷ B) ≫ η.app i) ≫ H'.map f
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc]
    have hs := s.naturality f
    change (W.map f ▷ A) ≫ s.app j = s.app i ≫ H.map f at hs
    rw [hs, comp_whiskerRight_assoc]
    have hη := η.naturality f
    change (H.map f ▷ B) ≫ η.app j = η.app i ≫ H'.map f at hη
    simp only [Category.assoc]
    rw [hη]

/-- 係数のパラメータ付き変換から得られる、重み付き end の実際の射。 -/
def weightedSectionsParameterMap (W : I ⥤ SSet.{u}) {H H' : I ⥤ SSet.{u}}
    {B : SSet.{u}} (η : H ⋙ tensorRight B ⟶ H') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H ⊗ B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H' :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (weightedSectionParameterTransform
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H))) η)

/-- パラメータ付き end の射を uncurry すると普遍切断のパラメータ付き後合成に戻る。 -/
lemma weightedSectionsParameterMap_uncurry (W : I ⥤ SSet.{u})
    {H H' : I ⥤ SSet.{u}} {B : SSet.{u}} (η : H ⋙ tensorRight B ⟶ H') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (weightedSectionsParameterMap W η) =
      weightedSectionParameterTransform
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H))) η :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_lift _

/-- パラメータ付き end の射の各係数の評価公式。 -/
lemma weightedSectionsParameterMap_evaluation (W : I ⥤ SSet.{u})
    {H H' : I ⥤ SSet.{u}} {B : SSet.{u}} (η : H ⋙ tensorRight B ⟶ H') (i : I) :
    W.obj i ◁ weightedSectionsParameterMap W η ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H' i) =
      (α_ (W.obj i) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H) B).inv ≫
        (uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H i) ▷ B) ≫ η.app i := by
  rw [← uncurry_natural_left, weightedSectionsParameterMap,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_π, uncurry_curry]
  dsimp only [weightedSectionParameterTransform, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry]
  erw [Category.id_comp]

/-- 係数図式の等式による end の移送は成分の評価と可換。 -/
lemma weightedSections_diagram_eq_evaluation (W : I ⥤ SSet.{u})
    {H H' : I ⥤ SSet.{u}} (e : H = H') (i : I) :
    W.obj i ◁ eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W) e) ≫
        uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H' i) =
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H i) ≫ eqToHom (congrArg (fun D ↦ D.obj i) e) := by
  cases e
  simp

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
