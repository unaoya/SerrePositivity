module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.EnrichedOrdinaryFunctorWhisker
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison

/-!
概要：全高次 Hom に自然な比較は、元の通常の射の像にも厳密に自然。
方針：同じ通常の射の豊穣表示を全パラメーターの評価へ代入する。
規約：元の豊穣関手と比較成分を保持する。
使われ方：全局所 Hom の同型比較を底全体の図式比較へ束ねる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 通常の射の豊穣表示を同じ評価へ代入すると、元の通常の関手像を回収する。 -/
lemma quasicategoryEnrichedOrdinary_map_action
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}) {X Y : C} (f : X ⟶ Y) :
    (ρ_ (F.obj X).obj).inv ≫ (F.obj X).obj ◁ eHomEquiv SSet.{u} f ≫ uncurry (F.map X Y) =
      (show (F.obj X).obj ⟶ (F.obj Y).obj from (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.enrichedOrdinaryFunctor SSet.{u} F).map f) := by
  rw [← uncurry_natural_left, ← _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.enrichedOrdinaryFunctor_map_unit]
  change (ρ_ (F.obj X).obj).inv ≫ uncurry (curry'
    (show (F.obj X).obj ⟶ (F.obj Y).obj from
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.enrichedOrdinaryFunctor SSet.{u} F).map f)) = _
  rw [curry', uncurry_curry, Iso.inv_hom_id_assoc]

/-- 元の全高次 Hom に自然な比較は、同じ通常の射の像と厳密に可換。 -/
lemma quasicategoryEnrichedComparison_ordinary_naturality
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison F G) {X Y : C} (f : X ⟶ Y) :
    (show (F.obj X).obj ⟶ (F.obj Y).obj from
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.enrichedOrdinaryFunctor SSet.{u} F).map f) ≫ η.val Y =
    η.val X ≫ (show (G.obj X).obj ⟶ (G.obj Y).obj from
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.enrichedOrdinaryFunctor SSet.{u} G).map f) := by
  let t := eHomEquiv SSet.{u} f
  let H := SimplicialCategory.sHom X Y
  calc
    _ = (ρ_ (F.obj X).obj).inv ≫ (F.obj X).obj ◁ t ≫ uncurry (F.map X Y) ≫ η.val Y := by
      simpa only [Category.assoc] using congrArg (fun m ↦ m ≫ η.val Y)
        (quasicategoryEnrichedOrdinary_map_action F f).symm
    _ = (ρ_ (F.obj X).obj).inv ≫ (F.obj X).obj ◁ t ≫
        (η.val X ▷ H) ≫ uncurry (G.map X Y) :=
      congrArg (fun m ↦ (ρ_ (F.obj X).obj).inv ≫ (F.obj X).obj ◁ t ≫ m)
        (η.property X Y).symm
    _ = η.val X ≫ (ρ_ (G.obj X).obj).inv ≫ (G.obj X).obj ◁ t ≫ uncurry (G.map X Y) := by
      rw [← Category.assoc ((F.obj X).obj ◁ t) (η.val X ▷ H), whisker_exchange]
      simp only [Category.assoc]
      rw [← rightUnitor_inv_naturality_assoc]
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun m ↦ η.val X ≫ m)
        (quasicategoryEnrichedOrdinary_map_action G f)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
