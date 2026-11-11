module
public import SerrePositivity.KST.SConstruction.QuasicategoryEnrichedActionLaws
public import SerrePositivity.KST.SConstruction.KanSourceCoreMap
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedPrismEvaluation

/-! # 実 core 値への元の全 Kan パラメータ作用
概要：局所 Kan な入力からの実作用を、値の実 core へ全単体のまま持ち上げる。
方針：core 値と入力 Hom の積の Kan 性を使い、包含後に元の単位・合成を反映する。
規約：源の小ささを要求しない。使われ方：全 native dg 入力に対する core S•。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  [∀ X Y : C, KanComplex (X ⟶[SSet.{u}] Y)]
  (F : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u})

/-- 元の Quasi 値の同じ実 core を、実 Kan 複体として保持する。 -/
def quasicategoryEnrichedCoreValue (X : C) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (F.obj X).obj : SSet.{u}), inferInstance⟩

/-- 元の全 Kan 入力族を、同じ実 core 値に作用させる。 -/
def quasicategoryEnrichedCoreAction (X Y : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (F.obj X).obj : SSet.{u}) ⊗ (X ⟶[SSet.{u}] Y) ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (F.obj Y).obj : SSet.{u}) := by
  let : KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (F.obj X).obj : SSet.{u}) ⊗ (X ⟶[SSet.{u}] Y)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismParameterProduct_kanComplex _ _
  exact kanSourceCoreMap
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (F.obj X).obj).ι ⊗ₘ 𝟙 _) ≫ uncurry (F.map X Y))

/-- 実 core 包含の後では、元の同じ値と全パラメータの実作用を回収する。 -/
lemma quasicategoryEnrichedCoreAction_inclusion (X Y : C) :
    quasicategoryEnrichedCoreAction F X Y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (F.obj Y).obj).ι =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (F.obj X).obj).ι ⊗ₘ 𝟙 _) ≫ uncurry (F.map X Y) := rfl

/-- 元の豊穣恒等入力は、同じ実 core 値上でも恒等作用を与える。 -/
lemma quasicategoryEnrichedCoreAction_unit (X : C) :
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (F.obj X).obj : SSet.{u}) ⊗ₘ eId SSet.{u} X) ≫
        quasicategoryEnrichedCoreAction F X X =
      (ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (F.obj X).obj : SSet.{u})).hom := by
  ext n p
  apply Subtype.ext
  exact congrArg (fun f => f.app n (p.1.val, p.2)) (quasicategoryEnrichedAction_unit F X)

/-- 同じ実 core 値への二回の作用は、元の豊穣合成による作用と全単体で一致する。 -/
lemma quasicategoryEnrichedCoreAction_comp (X Y Z : C) :
    (quasicategoryEnrichedCoreAction F X Y ⊗ₘ 𝟙 (Y ⟶[SSet.{u}] Z)) ≫
        quasicategoryEnrichedCoreAction F Y Z =
      (α_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (F.obj X).obj : SSet.{u})
        (X ⟶[SSet.{u}] Y) (Y ⟶[SSet.{u}] Z)).hom ≫
          (𝟙 _ ⊗ₘ eComp SSet.{u} X Y Z) ≫ quasicategoryEnrichedCoreAction F X Z := by
  ext n p
  apply Subtype.ext
  exact congrArg (fun f => f.app n ((p.1.1.val, p.1.2), p.2))
    (quasicategoryEnrichedAction_comp F X Y Z)

end SerrePositivity.KST.SConstruction
