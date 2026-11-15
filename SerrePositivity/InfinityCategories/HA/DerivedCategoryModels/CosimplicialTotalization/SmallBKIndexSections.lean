module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedNormalizedBKSmallSections
/-!
概要：BK切断の二重反対添字を同じAsSmallの元の添字へ戻す。
方針：指定down・二重反対・upで普遍切断を制限し、全射影で逆則を照合する。
規約：IS-W2 A12の添字移送の証明分割。頂点も全単体作用素も変えない。
使われ方：HA 1.2.4、元の余単体図式の反転BK比較への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
/-- 元の小添字から同じ二重反対の小添字への指定関手。 -/
def smallBKIndexToDouble : AsSmall.{u} SimplexCategory ⥤ AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ) :=
  AsSmall.down ⋙ (opOpEquivalence SimplexCategory).inverse ⋙ AsSmall.up
/-- 二重反対の小添字を元の小添字へ戻す指定関手。 -/
def smallBKIndexFromDouble : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ) ⥤ AsSmall.{u} SimplexCategory :=
  AsSmall.down ⋙ (opOpEquivalence SimplexCategory).functor ⋙ AsSmall.up
/-- 同じ普遍切断を指定添字関手で制限する。 -/
def smallBKIndexSectionsMap {I J : Type u} [SmallCategory I] [SmallCategory J]
    (F : J ⥤ I) (W H : I ⥤ SSet.{u}) :
    weightedSections W H ⟶ weightedSections (F ⋙ W) (F ⋙ H) :=
  weightedSectionsLift (Functor.whiskerLeft F (weightedSectionsUncurry (𝟙 (weightedSections W H))))
/-- 制限した普遍切断の射影は元の同じ対象での射影。 -/
theorem smallBKIndexSectionsMap_π {I J : Type u} [SmallCategory I] [SmallCategory J]
    (F : J ⥤ I) (W H : I ⥤ SSet.{u}) (j : J) :
    smallBKIndexSectionsMap F W H ≫ weightedSectionsπ (F ⋙ W) (F ⋙ H) j =
      weightedSectionsπ W H (F.obj j) := by
  rw [smallBKIndexSectionsMap, weightedSectionsLift_π]
  change curry (uncurry (𝟙 _ ≫ weightedSectionsπ W H (F.obj j))) = _
  rw [curry_uncurry, Category.id_comp]
/-- 指定二重反対添字の制限は同じ全切断空間の厳密な同型。 -/
def smallBKIndexSectionsIso (W H : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ) ⥤ SSet.{u}) :
    weightedSections W H ≅
      weightedSections (smallBKIndexToDouble ⋙ W) (smallBKIndexToDouble ⋙ H) where
  hom := smallBKIndexSectionsMap smallBKIndexToDouble W H
  inv := smallBKIndexSectionsMap smallBKIndexFromDouble
    (smallBKIndexToDouble ⋙ W) (smallBKIndexToDouble ⋙ H)
  hom_inv_id := by
    apply weightedSections_hom_ext
    intro j
    have h := smallBKIndexSectionsMap_π smallBKIndexFromDouble
      (smallBKIndexToDouble ⋙ W) (smallBKIndexToDouble ⋙ H) j
    change smallBKIndexSectionsMap smallBKIndexFromDouble
      (smallBKIndexToDouble ⋙ W) (smallBKIndexToDouble ⋙ H) ≫ weightedSectionsπ W H j = _ at h
    rw [Category.assoc, h]
    exact (smallBKIndexSectionsMap_π smallBKIndexToDouble W H
      (smallBKIndexFromDouble.obj j)).trans (Category.id_comp _).symm
  inv_hom_id := by
    apply weightedSections_hom_ext
    intro j
    rw [Category.assoc, smallBKIndexSectionsMap_π smallBKIndexToDouble W H j]
    have h := smallBKIndexSectionsMap_π smallBKIndexFromDouble
      (smallBKIndexToDouble ⋙ W) (smallBKIndexToDouble ⋙ H) (smallBKIndexToDouble.obj j)
    change smallBKIndexSectionsMap smallBKIndexFromDouble
      (smallBKIndexToDouble ⋙ W) (smallBKIndexToDouble ⋙ H) ≫
        weightedSectionsπ W H (smallBKIndexToDouble.obj j) = _ at h
    exact h.trans (Category.id_comp _).symm
end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
