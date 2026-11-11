module
public import SerrePositivity.KST.Fibration.VerdierFullSLowerCanonicalBoundary
public import SerrePositivity.KST.Fibration.QuotientSKernelTriangles

/-!
概要：指定 Verdier の元の全下側二胞体を、元の商核四角形の全下側二胞体へ比較する。
方針：最大化の実二射列を端点込みの短辺データで元の Kan 包含・商へ同定する。
規約：元の全下側二胞体と指定二射を保持する。上側と共有対角で貼る比較は別途必要。
使われ方：K-6 c4 の全四角形比較の、下側の指定全二胞体比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

private theorem compStruct_eq_of_arrowData {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {X Y Z A B E : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : A ⟶ B) (b : B ⟶ E)
    (hf : (⟨X, Y, f⟩ : Σ V W : C, V ⟶ W) = ⟨A, B, a⟩)
    (hg : (⟨Y, Z, g⟩ : Σ V W : C, V ⟶ W) = ⟨B, E, b⟩) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g).simplex = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct a b).simplex := by
  have hX := congrArg (fun t : Σ V W : C, V ⟶ W => t.1) hf
  have hY := congrArg (fun t : Σ V W : C, V ⟶ W => t.2.1) hf
  have hZ := congrArg (fun t : Σ V W : C, V ⟶ W => t.2.1) hg
  cases hX
  cases hY
  cases hZ
  have hf' : f = a := by simpa using hf
  have hg' : g = b := by simpa using hg
  cases hf'
  cases hg'
  rfl

variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})

/-- 同じ最大化の全二胞体は、元の実 Kan 包含と商の標準合成二胞体そのもの。 -/
theorem verdierFullSLowerMaximalization_eq_kernelCompStruct :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (stableCoreSingleKanMap d.inclusion)
        (stableCoreSingleKanMap d.projection)).simplex := by
  let f := (verdierFullSLowerStrictDiagram d).map (homOfLE
    (show (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 1 from by decide))
  let g := (verdierFullSLowerStrictDiagram d).map (homOfLE
    (show (ULift.up (1 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 2 from by decide))
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g
  have h := verdierFullSLowerMaximalization_eq_compStruct d
  have hf := (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData
    ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ 2) h).trans t.d₂)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_of_arrow f)
  have hg := (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData
    ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ 0) h).trans t.d₀)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_of_arrow g)
  exact h.trans (compStruct_eq_of_arrowData f g
    (stableCoreSingleKanMap d.inclusion) (stableCoreSingleKanMap d.projection)
    (hf.symm.trans (verdierFullSLowerCanonical_first_data d))
    (hg.symm.trans (verdierFullSLowerCanonical_last_data d)))

/-- 同じ最大化の全二胞体の射は、元の商核四角形の下側二胞体そのもの。 -/
theorem verdierFullSLowerMaximalization_kernel :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ quotientSKernelInfinitySquare d.inclusion d.projection :=
  (congrArg SSet.yonedaEquiv.symm (verdierFullSLowerMaximalization_eq_kernelCompStruct d)).trans
    (quotientSKernelInfinitySquare_lower d.inclusion d.projection).symm

/-- 元の指定全下側二胞体から、元の商核全下側二胞体への同じ三角柱による全関手同型。 -/
def verdierFullSLowerKernelIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ quotientSKernelInfinitySquare d.inclusion d.projection) :=
  (congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))) f)
    (verdierFullSLowerMaximalization_kernel d)).mp (verdierFullSLowerDeformationIso d)

end SerrePositivity.KST.Fibration
