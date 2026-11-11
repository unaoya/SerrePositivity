module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftPointHomEnriched
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ReversePointHomAction

/-!
概要：任意のパラメーター付き Kan 値の作用を、反転した豊穣合成そのものへ移す。
方針：元の射を反転して curry し、パラメーターの二重反転を戻して同じ Hom に入れる。
規約：パラメーターの Kan 性は要求しない。係数の同型と反転を明示する。
使われ方：実際の pointed 輸送の合成作用を直接の Kan 作用で記述する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 元のパラメーター付き射を、同じ反転した豊穣 Hom のパラメーターへ写す。 -/
def leftPointHomReverseParameter {X Y T : SSet.{u}} (f : X ⊗ T ⟶ Y) :
    (SSet.uliftFunctor.{u + 1, u}).obj T ⟶
      ((SSet.uliftFunctor.{u + 1, u}).obj ((ihom X.op).obj Y.op)).op :=
  (SSet.uliftFunctor.{u + 1, u}).map
    ((SSet.opFunctorCompOpFunctorIso.app T).inv ≫
      SSet.opFunctor.map (curry
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.oppositeTensorIso X T).inv ≫ SSet.opFunctor.map f))) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso ((ihom X.op).obj Y.op)).hom

/-- 元の内部 Hom への射で評価を制限しても、同じ反転 Hom のパラメーターを回収する。 -/
lemma leftPointHomReverseParameter_uncurry {X Y H : SSet.{u}}
    (g : H ⟶ (ihom X).obj Y) :
    (SSet.uliftFunctor.{u + 1, u}).map g ≫
      leftPointHomReverseParameter (uncurry (𝟙 ((ihom X).obj Y))) =
        leftPointHomReverseParameter (uncurry g) := by
  have h (A : SSet.{u}) (k : A ⟶ (ihom X).obj Y) :
      curry ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.oppositeTensorIso X A).inv ≫
        SSet.opFunctor.map (uncurry k)) =
      SSet.opFunctor.map k ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso X Y).hom := by
    apply uncurry_injective
    rw [uncurry_curry, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeInternalHom_map_uncurry]
    rfl
  rw [leftPointHomReverseParameter, leftPointHomReverseParameter, h, h]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 反転した一点 Hom の直接の作用は、同じパラメーターでの豊穣合成と厳密に一致する。 -/
lemma leftPointHomParameterizedMap_reverseComposition {X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} {T : SSet.{u}}
    (f : X.obj ⊗ T ⟶ Y.obj) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso
      (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj X))).hom ⊗ₘ
      leftPointHomReverseParameter f) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentReverseHomComposition (Opposite.op (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj Y))
        (Opposite.op (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj X)) (Opposite.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject) =
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso
      (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj X)).op T).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftPointHomParameterizedMap f) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso
        (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj Y))).hom := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  apply SSet.opObjEquiv.injective
  apply ULift.ext
  apply Functor.HomObj.ext
  funext m α
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 標準係数の同型を通すと、反転した一点 Hom の作用は元の Kan 値の射となる。 -/
lemma leftPointHomParameterizedMap_coefficient {X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} {T : SSet.{u}}
    (f : X.obj ⊗ T ⟶ Y.obj) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceLeftCoefficientIso X).hom ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftPointHomParameterizedMap f =
      f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceLeftCoefficientIso Y).hom := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceLeftCoefficientIso Y).inv).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftPointHomParameterizedMap_comparison, ← Category.assoc,
    ← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight, Category.id_comp,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 同じ反転した豊穣合成を標準係数で評価すると、元の Kan 作用を回収する。 -/
lemma leftPointHomReverseComposition_coefficient {X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} {T : SSet.{u}}
    (f : X.obj ⊗ T ⟶ Y.obj) :
    (((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceLeftCoefficientIso X).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso
        (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj X))).hom) ⊗ₘ
      leftPointHomReverseParameter f) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentReverseHomComposition (Opposite.op (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj Y))
        (Opposite.op (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj X)) (Opposite.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject) =
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso X.obj T).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map f ≫
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceLeftCoefficientIso Y).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso
        (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj Y))).hom := by
  have h₀ :
      (((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceLeftCoefficientIso X).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso
          (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj X))).hom) ⊗ₘ
        leftPointHomReverseParameter f) =
      ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceLeftCoefficientIso X).hom ▷
        (SSet.uliftFunctor.{u + 1, u}).obj T) ≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso
          (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj X))).hom ⊗ₘ
          leftPointHomReverseParameter f) := rfl
  have h₁ :
      ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceLeftCoefficientIso X).hom ▷
        (SSet.uliftFunctor.{u + 1, u}).obj T) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso
          (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj X)).op T).inv =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso X.obj T).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceLeftCoefficientIso X).hom ▷ T) := rfl
  rw [h₀, Category.assoc, leftPointHomParameterizedMap_reverseComposition,
    ← Category.assoc, h₁]
  have h₂ := congrArg (SSet.uliftFunctor.{u + 1, u}).map
    (leftPointHomParameterizedMap_coefficient f)
  have h₃ := congrArg (fun k ↦ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso X.obj T).inv ≫ k ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso
      (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj Y))).hom) h₂
  simpa only [Functor.map_comp, Category.assoc] using h₃

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
