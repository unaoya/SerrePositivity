module

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedConeSectionEquivalence

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedConePrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedCosliceComparison
public import SerrePositivity.InfinityCategories.Core.UniverseSSetMaps

/-!
概要：weighted な係数と反転した豊穣 Hom の全パラメータから、実際の coslice の族を作る。
方針：係数の前合成を coherent な cone simplex の比較へ合成し、底上の性質を保つ。
規約：元の図式上の錐の族であり、構成済みの錐の図式全体上の族はまだ主張しない。
使われ方：HTT 4.2.4.1 の end の豊穣後合成と native な錐の切断の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- 全ての反転 Hom パラメータで weighted な係数を前合成し、実際の coslice へ写す族。 -/
def weightedCoslicePrecompositionFamily (F : I ⥤ C) (x z : C) :
    (SSet.uliftFunctor.{v, u}).obj
        (weightedNerve (simplicialHomDiagram F z ⋙ SSet.opFunctor)) ⊗
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op ⟶
        sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex x)) :=
  (uliftTensorIso _ _).inv ≫
    (SSet.uliftFunctor.{v, u}).map (weightedConePrecompositionMap F x z) ≫
      weightedCosliceComparison F x

/-- coslice の前合成族は元の図式の底を全パラメータで保つ。 -/
lemma weightedCoslicePrecompositionFamily_over (F : I ⥤ C) (x z : C) :
    weightedCoslicePrecompositionFamily F x z ≫
        sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)) =
      fst _ _ ≫ (SSet.uliftFunctor.{v, u}).map
        (weightedNerveProjection (simplicialHomDiagram F z ⋙ SSet.opFunctor)) ≫
          strictCoherentDiagram F := by
  rw [weightedCoslicePrecompositionFamily, Category.assoc, Category.assoc,
    weightedCosliceComparison_over, ← Functor.map_comp_assoc,
    weightedConePrecompositionMap_projection, Functor.map_comp]
  rfl

/-- 底の図式を保つ前合成族を、coherent な錐の全空間へ持ち上げる。 -/
def weightedCoherentConePrecompositionFamily (F : I ⥤ C) (x z : C) :
    (SSet.uliftFunctor.{v, u}).obj
        (weightedNerve (simplicialHomDiagram F z ⋙ SSet.opFunctor)) ⊗
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op ⟶
        coherentConeTotal (strictCoherentDiagram F) (coherentNerveVertex x) :=
  pullback.lift (weightedCoslicePrecompositionFamily F x z)
    (fst _ _ ≫ (SSet.uliftFunctor.{v, u}).map
      (weightedNerveProjection (simplicialHomDiagram F z ⋙ SSet.opFunctor)))
    (weightedCoslicePrecompositionFamily_over F x z)

/-- 錐の全空間へ持ち上げた族も同じ射列の上にある。 -/
lemma weightedCoherentConePrecompositionFamily_over (F : I ⥤ C) (x z : C) :
    weightedCoherentConePrecompositionFamily F x z ≫
        coherentConeProjection (strictCoherentDiagram F) (coherentNerveVertex x) =
      fst _ _ ≫ (SSet.uliftFunctor.{v, u}).map
        (weightedNerveProjection (simplicialHomDiagram F z ⋙ SSet.opFunctor)) :=
  pullback.lift_snd _ _ _

end
end SerrePositivity.InfinityCategories.HomotopyLimits
