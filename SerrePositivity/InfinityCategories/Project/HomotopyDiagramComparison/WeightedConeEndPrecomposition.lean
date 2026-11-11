module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedNerveParameterEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCoslicePrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ReflectedStrictConeEvaluation

/-!
概要：反転した Hom の end の作用を weighted nerve と実際の coslice の作用へ接続する。
方針：係数図式のパラメータ付き変換に普遍評価の可換式を適用する。
規約：元の図式上の coherent な錐の切断を扱う。錐の図式全体への延長は別工程。
使われ方：HTT 4.2.4.1 の普遍切断点から得られる比較族の幾何的照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- 反転した Hom の係数の前合成を、Bousfield–Kan の end の全パラメータの作用にする。 -/
def weightedConeEndPrecomposition (F : I ⥤ C) (x z : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z ⋙ SSet.opFunctor) ⊗
        (SimplicialCategory.sHom x z).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedHomPrecompositionDiagram F x z)

/-- end の前合成と weighted nerve の実際の前合成は、普遍評価で厳密に一致する。 -/
lemma weightedConeEndPrecomposition_evaluation (F : I ⥤ C) (x z : C) :
    (nerve I ◁ weightedConeEndPrecomposition F x z) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) =
      (α_ (nerve I) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z ⋙ SSet.opFunctor))
        (SimplicialCategory.sHom x z).op).inv ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z ⋙ SSet.opFunctor) ▷
          (SimplicialCategory.sHom x z).op) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedConePrecompositionMap F x z := by
  simpa only [weightedConeEndPrecomposition, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedConePrecompositionMap, Category.assoc]
    using _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanWeightedNerveEvaluation_parameter_map
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedHomPrecompositionDiagram F x z)

/-- Hom の end の前合成を既存の比較で評価して得られる、実際の coslice の族。 -/
def weightedCosliceEndPrecompositionEvaluation (F : I ⥤ C) (x z : C) :
    (SSet.uliftFunctor.{v, u}).obj
      (nerve I ⊗ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z ⋙ SSet.opFunctor) ⊗
        (SimplicialCategory.sHom x z).op)) ⟶
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) :=
  (SSet.uliftFunctor.{v, u}).map ((nerve I ◁ weightedConeEndPrecomposition F x z) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceComparison F x

/-- end の前合成を評価した族は、係数から構成した coslice の前合成族そのもの。 -/
lemma weightedCosliceEndPrecompositionEvaluation_eq_family (F : I ⥤ C) (x z : C) :
    weightedCosliceEndPrecompositionEvaluation F x z =
      (SSet.uliftFunctor.{v, u}).map
        ((α_ (nerve I) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z ⋙ SSet.opFunctor))
          (SimplicialCategory.sHom x z).op).inv ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z ⋙ SSet.opFunctor) ▷
            (SimplicialCategory.sHom x z).op)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedCoslicePrecompositionFamily F x z := by
  simp only [weightedCosliceEndPrecompositionEvaluation,
    weightedConeEndPrecomposition_evaluation, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedCoslicePrecompositionFamily,
    Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- 既存の coherent 錐の切断比較を前合成して評価すると、同じ coslice の族を回収する。 -/
lemma reflectedHomHolimConeComparison_precomposition_uncurry (F : I ⥤ C) (x z : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
        ((SSet.uliftFunctor.{v, u}).map (weightedConeEndPrecomposition F x z) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison F x) =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso _ _).inv ≫ weightedCosliceEndPrecompositionEvaluation F x z := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.relativeFunctorUncurry_parameter, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_uncurry]
  rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
