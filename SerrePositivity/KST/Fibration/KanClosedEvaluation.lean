module
public import SerrePositivity.KST.SConstruction.ExInfinityPointedEnrichedFunctor
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedMaps
public import SerrePositivity.KST.Comparison.ExInfinityMonoidal

/-! # 元の閉 Hom の Ex∞ 評価と、点つき Kan の全 Hom の忘却 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
namespace SerrePositivity.KST.Fibration

/-- 基点だけを忘れ、同じ Kan 値と全基点固定 Hom の包含を保持する。 -/
def pointedKanForgetEnriched :
    EnrichedFunctor SSet.{u} PointedKanObject.{u} KanObject.{u} where
  obj X := ⟨X.obj.right, inferInstance⟩
  map X Y := PointedObject.basedHomι X.obj Y.obj
  map_id X := pointedClosedHomInclusion_id X.obj
  map_comp X Y Z := pointedClosedHomInclusion_comp X.obj Y.obj Z.obj

/-- 元の全閉 Hom を持つ Ex∞ の Kan 値への厳密豊穣関手。 -/
def exInfinityClosedKanEnrichedFunctor :
    EnrichedFunctor SSet.{u} SSetInternalObject.{u} KanObject.{u} where
  obj X := ⟨exInfinity.obj X.obj, exInfinity_kanComplex X.obj⟩
  map X Y := (coaugmentedClosedEnrichedFunctor exInfinity exInfinityUnit).map X Y
  map_id X := (coaugmentedClosedEnrichedFunctor exInfinity exInfinityUnit).map_id X
  map_comp X Y Z :=
    (coaugmentedClosedEnrichedFunctor exInfinity exInfinityUnit).map_comp X Y Z

/-- 元の通常射の閉 Hom 表示は、同じ Ex∞ 射の Kan 表示へ送られる。 -/
theorem exInfinityClosedKanEnrichedFunctor_hom {X Y : SSetInternalObject.{u}} (f : X ⟶ Y) :
    eHomEquiv SSet f ≫ exInfinityClosedKanEnrichedFunctor.map X Y =
      eHomEquiv SSet (show exInfinityClosedKanEnrichedFunctor.obj X ⟶
        exInfinityClosedKanEnrichedFunctor.obj Y from exInfinity.map f) :=
  coaugmentedClosedFamilyMap_hom exInfinity exInfinityUnit f

/-- 点つき Ex∞ の基点を忘れると、元の閉 Hom の同じ Ex∞ 作用になる。 -/
theorem exInfinityPointedKan_forget :
    exInfinityPointedKanEnrichedFunctor.comp SSet pointedKanForgetEnriched =
      pointedSSetObjectClosedForget.comp SSet exInfinityClosedKanEnrichedFunctor := by
  apply EnrichedFunctor.ext SSet
  case h_obj =>
    intro X
    rfl
  case h_map =>
    intro X Y
    simp only [eqToHom_refl, Category.comp_id]
    exact (coaugmentedPointedFamilyMap_inclusion exInfinity exInfinityUnit X Y).trans
      (curry_uncurry _)

end SerrePositivity.KST.Fibration
