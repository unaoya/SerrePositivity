module

public import SerrePositivity.KST.Spectra.WeightedParameterNaturality

/-!
概要：weighted end の作用の、係数とパラメータを同時に動かす自然性。
方針：パラメータの射を係数自然変換へ吸収し、係数自然性に適用する。
規約：全て元の共有のパラメータ作用について述べる。使われ方：edgewise 両端の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.WeightedParameterNaturality
variable {I : Type u} [SmallCategory I]

/-- パラメータの射の前合成による、係数のパラメータ付き自然変換の制限。 -/
def preParameter {B C : SSet.{u}} {H E : I ⥤ SSet.{u}}
    (b : B ⟶ C) (θ : H ⋙ tensorRight C ⟶ E) : H ⋙ tensorRight B ⟶ E where
  app i := H.obj i ◁ b ≫ θ.app i
  naturality i j f := by
    change H.map f ▷ B ≫ H.obj j ◁ b ≫ θ.app j =
      (H.obj i ◁ b ≫ θ.app i) ≫ E.map f
    rw [← whisker_exchange_assoc, Category.assoc]
    have ht := θ.naturality f
    change H.map f ▷ C ≫ θ.app j = θ.app i ≫ E.map f at ht
    rw [ht]

/-- weighted end の全パラメータ作用は、パラメータ自体の射にも自然。 -/
lemma parameter_natural (W : I ⥤ SSet.{u}) {B C : SSet.{u}} {H E : I ⥤ SSet.{u}}
    (b : B ⟶ C) (θ : H ⋙ tensorRight C ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H ◁ b ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap W θ =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap W (preParameter b θ) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  apply uncurry_injective
  rw [Category.assoc, uncurry_natural_left, uncurry_natural_left,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap_evaluation, associator_inv_naturality_right_assoc,
    whisker_exchange_assoc]
  conv_rhs => rw [uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap_evaluation]
  rfl

/-- 係数・値・パラメータを同時に動かす可換四角形は、weighted end 上でも可換。 -/
lemma joint_natural (W : I ⥤ SSet.{u}) {H H' E E' : I ⥤ SSet.{u}} {B C : SSet.{u}}
    (α : H ⟶ H') (β : E ⟶ E') (b : B ⟶ C) (η : H ⋙ tensorRight B ⟶ E)
    (θ : H' ⋙ tensorRight C ⟶ E')
    (h : ∀ i, (α.app i ⊗ₘ b) ≫ θ.app i = η.app i ≫ β.app i) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W α ⊗ₘ b) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap W θ =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap W η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W β := by
  have hn := natural W α β η (preParameter b θ) (fun i ↦ by
    change α.app i ▷ B ≫ H'.obj i ◁ b ≫ θ.app i = _
    rw [← Category.assoc, ← tensorHom_def]
    exact h i)
  rw [tensorHom_def, Category.assoc, parameter_natural, hn]

end SerrePositivity.KST.Spectra.WeightedParameterNaturality
