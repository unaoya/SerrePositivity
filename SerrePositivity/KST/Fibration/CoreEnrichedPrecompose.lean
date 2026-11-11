module
public import SerrePositivity.KST.SConstruction.QuasicategoryEnrichedCoreFunctor

/-! # 元の全 Kan 入力を保つ core 作用と豊穣前合成の整合性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w z t
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 豊穣関手の括弧の変更は、元の同じ全 Hom 合成を保持する。 -/
theorem enrichedFunctor_comp_assoc {B : Type v} {C : Type w} {D : Type z} {E : Type t}
    [EnrichedCategory SSet.{u} B] [EnrichedCategory SSet.{u} C]
    [EnrichedCategory SSet.{u} D] [EnrichedCategory SSet.{u} E]
    (F : EnrichedFunctor SSet.{u} B C) (G : EnrichedFunctor SSet.{u} C D)
    (H : EnrichedFunctor SSet.{u} D E) :
    (F.comp SSet G).comp SSet H = F.comp SSet (G.comp SSet H) := by
  apply EnrichedFunctor.ext SSet
  case h_obj => intro X; rfl
  case h_map =>
    intro X Y
    simp only [eqToHom_refl, Category.comp_id]
    exact Category.assoc _ _ _

/-- core 値の元の全 Hom 作用は、同じ豊穣関手による前合成と可換。 -/
theorem coreEnrichedPrecompose_map {C : Type v} {D : Type w}
    [Category.{u} C] [Category.{u} D] [SimplicialCategory C] [SimplicialCategory D]
    [∀ X Y : C, KanComplex (X ⟶[SSet.{u}] Y)]
    [∀ X Y : D, KanComplex (X ⟶[SSet.{u}] Y)]
    (R : EnrichedFunctor SSet.{u} C D)
    (F : EnrichedFunctor SSet.{u} D _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}) (X Y : C) :
    R.map X Y ≫ (quasicategoryEnrichedCoreFunctor F).map (R.obj X) (R.obj Y) =
      (quasicategoryEnrichedCoreFunctor (R.comp SSet F)).map X Y := by
  apply (cancel_mono ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (F.obj (R.obj X)).obj : SSet.{u})).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (F.obj (R.obj Y)).obj).ι)).mp
  rw [Category.assoc, quasicategoryEnrichedCoreFunctor_inclusion]
  exact (Category.assoc _ _ _).symm.trans
    (quasicategoryEnrichedCoreFunctor_inclusion (R.comp SSet F) X Y).symm

/-- 中間の包含を持つ元の全 core 作用も、括弧を変えずに前合成できる。 -/
theorem coreEnrichedPrecompose_assoc_map {C : Type v} {D : Type w} {E : Type z}
    [Category.{u} C] [Category.{u} D] [SimplicialCategory C] [SimplicialCategory D]
    [EnrichedCategory SSet.{u} E]
    [∀ X Y : C, KanComplex (X ⟶[SSet.{u}] Y)]
    [∀ X Y : D, KanComplex (X ⟶[SSet.{u}] Y)]
    (R : EnrichedFunctor SSet.{u} C D) (I : EnrichedFunctor SSet.{u} D E)
    (F : EnrichedFunctor SSet.{u} E _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}) (X Y : C) :
    R.map X Y ≫ (quasicategoryEnrichedCoreFunctor (I.comp SSet F)).map (R.obj X) (R.obj Y) =
      (quasicategoryEnrichedCoreFunctor ((R.comp SSet I).comp SSet F)).map X Y := by
  change R.map X Y ≫ curry (quasicategoryEnrichedCoreAction (I.comp SSet F)
    (R.obj X) (R.obj Y)) =
      curry (quasicategoryEnrichedCoreAction ((R.comp SSet I).comp SSet F) X Y)
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, uncurry_curry]
  ext n p
  apply Subtype.ext
  rfl

end SerrePositivity.KST.Fibration
