module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.KanDiagramNativeOppositeHomParameter
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftPointHomReverseComposition

/-!
概要：native な係数反転の対象ごとの値を、元の Kan 作用の反転パラメーターへ戻す。
方針：反転した内部 Hom の curry と、二重反転の自然性を厳密に照合する。
規約：元の strict Hom の全単体を保持し、その Kan 性は要求しない。
使われ方：weighted pointed prism の底と、実際の係数の同時評価との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories


/-- 元の作用を反転したパラメーターは、内部 Hom の標準反転で厳密に表せる。 -/
lemma leftPointHomReverseParameter_uncurry_eq {X Y H : SSet.{u}}
    (g : H ⟶ (ihom X).obj Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftPointHomReverseParameter (uncurry g) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (g ≫ (SSet.opFunctorCompOpFunctorIso.app ((ihom X).obj Y)).inv ≫
          SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso X Y).hom) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso ((ihom X.op).obj Y.op)).hom := by
  have hc : curry ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.oppositeTensorIso X H).inv ≫ SSet.opFunctor.map (uncurry g)) =
      SSet.opFunctor.map g ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso X Y).hom := by
    apply uncurry_injective
    rw [uncurry_curry, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeInternalHom_map_uncurry]
    rfl
  have hn := SSet.opFunctorCompOpFunctorIso.inv.naturality g
  change g ≫ (SSet.opFunctorCompOpFunctorIso.app ((ihom X).obj Y)).inv =
    (SSet.opFunctorCompOpFunctorIso.app H).inv ≫
      SSet.opFunctor.map (SSet.opFunctor.map g) at hn
  have hb : (SSet.opFunctorCompOpFunctorIso.app H).inv ≫
      SSet.opFunctor.map (SSet.opFunctor.map g ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso X Y).hom) =
      g ≫ (SSet.opFunctorCompOpFunctorIso.app ((ihom X).obj Y)).inv ≫
        SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso X Y).hom := by
    rw [SSet.opFunctor.map_comp, ← Category.assoc, ← hn, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftPointHomReverseParameter, hc, hb]

/-- native な係数反転の各値は、元の変換の評価を反転した同じパラメーター。 -/
lemma kanDiagramNativeOppositeHomParameter_pointwise
    {I : Type u} [SmallCategory I] (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (i : I) :
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramNativeOppositeHomParameter F G) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent ((F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
          ((G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) i)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso ((ihom (F.val.obj i).obj.op).obj (G.val.obj i).obj.op)).hom =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftPointHomReverseParameter (uncurry
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) i)) := by
  rw [← Category.assoc, ← Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramNativeOppositeHomParameter_component]
  exact (leftPointHomReverseParameter_uncurry_eq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
      (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) i)).symm

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
