module
public import SerrePositivity.KST.SConstruction.QuasicategoryEnrichedCoreAction

/-! # 全 Kan 入力を保つ実 core 値の厳密豊穣関手
概要：局所 Kan な入力からの Quasi 値豊穣関手を、同じ値の実 core へ送る。
方針：元の全パラメータ作用の core 持ち上げを curry し、単位・合成を反映する。
規約：入力を離散化しない。使われ方：実 core S_n と core S• 全体の関手性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories

private lemma uncurry_parameter_point {X Y P : SSet.{u}}
    (a : P ⟶ (ihom X).obj Y) (p : 𝟙_ SSet.{u} ⟶ P) (g : X ⟶ Y)
    (h : p ≫ a = curry' g) :
    (𝟙 X ⊗ₘ p) ≫ uncurry a = (ρ_ X).hom ≫ g := by
  have hh := congrArg (fun q : 𝟙_ SSet.{u} ⟶ (ihom X).obj Y => uncurry q) h
  rw [uncurry_natural_left, curry', uncurry_curry] at hh
  simpa only [id_tensorHom] using hh

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  [∀ X Y : C, KanComplex (X ⟶[SSet.{u}] Y)]
  (F : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u})

/-- 元の全 Kan 入力を保持し、元の Quasi 値の実 core を取る厳密豊穣関手。 -/
def quasicategoryEnrichedCoreFunctor : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj := quasicategoryEnrichedCoreValue F
  map X Y := curry (quasicategoryEnrichedCoreAction F X Y)
  map_id X := by
    change eId SSet.{u} X ≫ curry (quasicategoryEnrichedCoreAction F X X) =
      MonoidalClosed.id (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (F.obj X).obj : SSet.{u})
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, MonoidalClosed.id_eq,
      uncurry_curry, ← id_tensorHom]
    exact quasicategoryEnrichedCoreAction_unit F X
  map_comp X Y Z :=
    (rightActionCurry_comp _ _ _ _ (quasicategoryEnrichedCoreAction_comp F X Y Z)).symm

/-- 実 core 値の包含後には、同じ元の全パラメータ関手族の制限を回収する。 -/
lemma quasicategoryEnrichedCoreFunctor_inclusion (X Y : C) :
    (quasicategoryEnrichedCoreFunctor F).map X Y ≫
        (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (F.obj X).obj : SSet.{u})).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (F.obj Y).obj).ι =
      F.map X Y ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (F.obj X).obj).ι).app (F.obj Y).obj := by
  change curry (quasicategoryEnrichedCoreAction F X Y) ≫
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (F.obj X).obj : SSet.{u})).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (F.obj Y).obj).ι = _
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_pre_app, uncurry_curry]
  exact quasicategoryEnrichedCoreAction_inclusion F X Y

/-- 同じ通常の入力射の像を、同じ元の core 射として厳密に回収する。 -/
lemma quasicategoryEnrichedCoreFunctor_hom {X Y : C} (f : X ⟶ Y)
    (g : (F.obj X).obj ⟶ (F.obj Y).obj)
    (h : eHomEquiv SSet.{u} f ≫ F.map X Y = curry' g) :
    eHomEquiv SSet.{u} f ≫ (quasicategoryEnrichedCoreFunctor F).map X Y =
      curry' (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap g) := by
  have hu := uncurry_parameter_point (F.map X Y) (eHomEquiv SSet.{u} f) g h
  change eHomEquiv SSet.{u} f ≫ curry (quasicategoryEnrichedCoreAction F X Y) = _
  apply uncurry_injective
  rw [uncurry_natural_left, curry', uncurry_curry, uncurry_curry]
  ext n p
  apply Subtype.ext
  exact congrArg (fun q => q.app n (p.1.val, p.2)) hu

end SerrePositivity.KST.SConstruction
