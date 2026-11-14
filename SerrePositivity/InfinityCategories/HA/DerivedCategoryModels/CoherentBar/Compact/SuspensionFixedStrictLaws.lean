module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SuspensionFixedCoherenceTypes
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSuspensionCanonicalMapData

/-!
概要：固定 data の cone 作用の厳密則を、同じ実懸垂入力射の厳密則へ移す。
方針：resolved は同じ comparisonFunctor であることを使い、data 全体を比較する。
規約：cone 作用の恒等・合成等号は明示入力であり、代表選択から推論しない。
使われ方：厳密則が成立する場合の固定単位・合成比較への供給路。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded KST.SConstruction KST.NonConnective
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ)
variable (A : PerfDGInput.{u, max (u + 1) v} R)

/-- 固定 cone の恒等等号から、正本 resolved・商を通して同じ入力射の恒等を得る。 -/
lemma dgSuspensionFixedUnitInputEqOfConeEq
    (h : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ (𝟙 A)).cone = DGFunctor.id _) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalInputMap R κ hκ (𝟙 A) =
      𝟙 (dgKappaSuspensionKInput R A
        (dgKappaUnconditionalStageProvider.{u, v} R κ hκ A).cone) := by
  have hd : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ (𝟙 A) =
      DGKappaSuspensionMapData.id R A
        (dgKappaUnconditionalStageProvider.{u, v} R κ hκ A).cone := by
    apply DGKappaSuspensionMapData.ext
    · exact h
    · change DGCategoryCellResolution.comparisonFunctor R _ _
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ (𝟙 A)).cone = DGFunctor.id _
      rw [h, DGCategoryCellResolution.comparisonFunctor_identity]
  change dgKappaSuspensionInputMap R A A _ _ _ = _
  rw [hd, dgKappaSuspensionInputMap_id]

variable {A} {B C : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) (g : B ⟶ C)

/-- 固定 cone の合成等号から、正本 resolved・商を通して同じ入力射の合成を得る。 -/
lemma dgSuspensionFixedCompositionInputEqOfConeEq
    (h : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ (f ≫ g)).cone =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ f).cone.comp
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ g).cone) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalInputMap R κ hκ (f ≫ g) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalInputMap R κ hκ f ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalInputMap R κ hκ g := by
  have hd : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ (f ≫ g) =
      DGKappaSuspensionMapData.comp R A B _ _
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ f)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ g) := by
    apply DGKappaSuspensionMapData.ext
    · exact h
    · change DGCategoryCellResolution.comparisonFunctor R _ _
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ (f ≫ g)).cone =
          (DGCategoryCellResolution.comparisonFunctor R _ _
            (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ f).cone).comp
              (DGCategoryCellResolution.comparisonFunctor R _ _
                (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ g).cone)
      rw [h, DGCategoryCellResolution.comparisonFunctor_composition]
  change dgKappaSuspensionInputMap R A C _ _ _ = _
  rw [hd, dgKappaSuspensionInputMap_comp]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
