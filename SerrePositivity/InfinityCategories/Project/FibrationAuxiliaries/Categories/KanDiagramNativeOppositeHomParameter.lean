module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseDualityLeftEndpoint
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.KanDiagramOppositeHomIntervalComparison

/-!
概要：反転後の左区間族を、元の strict Hom の右端パラメーターから直接表す。
方針：双対後の左端の式と二重反転の逆同型により係数反転を元の Hom へ戻す。
規約：左右の端点射影を同一視せず、表示変更の射を明示する。
使われ方：weighted Hom の右端作用と同じパラメーター上で pointed prism を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

variable {I : Type u} [SmallCategory I]

/-- 元の Hom を、反転した二図式の左 Hom の係数へ直接写す。 -/
def kanDiagramNativeOppositeHomParameter (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) :
    SimplicialCategory.sHom F G ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace
        ((F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
        ((G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)).op :=
  (SSet.opFunctorCompOpFunctorIso.app (SimplicialCategory.sHom F G)).inv ≫
    SSet.opFunctor.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictDiagramOppositeHom (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))

/-- 反転後の左端は、元の右端と同じ native な係数反転の射の合成。 -/
lemma kanDiagramOppositeHomParameter_left (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramOppositeHomParameter F G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (SimplicialCategory.sHom F G) ≫
        kanDiagramNativeOppositeHomParameter F G := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramOppositeHomParameter, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft_naturality,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseDuality_left, Category.assoc]
  rfl

/-- 同じ左区間族の共通パラメーターは、weighted 作用が用いる元の Hom の右端。 -/
lemma kanDiagramOppositeLeftHomInterval_eq_native (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramOppositeLeftHomInterval F G =
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (SimplicialCategory.sHom F G)) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (kanDiagramNativeOppositeHomParameter F G) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramLeftHomInterval (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramUniversalEnriched I)
            (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I from ⟨F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor, trivial⟩)
            (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I from ⟨G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor, trivial⟩) rfl rfl := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramOppositeLeftHomInterval, ← Category.assoc, ← Functor.map_comp,
    kanDiagramOppositeHomParameter_left, Functor.map_comp, Category.assoc]

/-- 一成分での native な係数反転は、同じ成分の内部 Hom の二重反転と反転同型。 -/
lemma kanDiagramNativeOppositeHomParameter_component
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (i : I) :
    kanDiagramNativeOppositeHomParameter F G ≫
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent
        ((F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
        ((G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) i) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) i ≫
      (SSet.opFunctorCompOpFunctorIso.app
        ((ihom (F.val.obj i).obj).obj (G.val.obj i).obj)).inv ≫
      SSet.opFunctor.map
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso (F.val.obj i).obj (G.val.obj i).obj).hom := by
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent
    (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) i
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictDiagramOppositeHom_component
    (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) i
  have h := congrArg SSet.opFunctor.map hc
  have hn := SSet.opFunctorCompOpFunctorIso.inv.naturality c
  change c ≫ (SSet.opFunctorCompOpFunctorIso.app
      ((ihom (F.val.obj i).obj).obj (G.val.obj i).obj)).inv =
    (SSet.opFunctorCompOpFunctorIso.app (SimplicialCategory.sHom F G)).inv ≫
      SSet.opFunctor.map (SSet.opFunctor.map c) at hn
  have h' := congrArg
    (fun f => (SSet.opFunctorCompOpFunctorIso.app (SimplicialCategory.sHom F G)).inv ≫ f) h
  simp only [Functor.map_comp] at h'
  have hn' := congrArg (fun f => f ≫ SSet.opFunctor.map
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso (F.val.obj i).obj (G.val.obj i).obj).hom) hn
  simp only [Category.assoc] at hn'
  calc
    _ = (SSet.opFunctorCompOpFunctorIso.app (SimplicialCategory.sHom F G)).inv ≫
        SSet.opFunctor.map (SSet.opFunctor.map c) ≫ SSet.opFunctor.map
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso (F.val.obj i).obj (G.val.obj i).obj).hom := by
      convert h' using 1 <;> rfl
    _ = _ := by
      convert hn'.symm using 1

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
