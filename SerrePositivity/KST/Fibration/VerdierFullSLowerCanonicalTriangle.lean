module
public import SerrePositivity.KST.Fibration.VerdierFullSLowerStrictArrows

/-!
概要：指定 Verdier 下側二胞体の最大化を、同じ通常の二射の標準合成二胞体へ同定する。
方針：同じ最大 path 図式を三点の実射列として読み、F1 の全 Hom strict 化公式を使う。
規約：全二胞体の等号であり、短辺だけの同定ではない。上側との共有対角比較は別途必要。
使われ方：K-6 c4 の商核側の標準合成二胞体と、指定下側二胞体との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})

/-- 同じ最大 path 図式の、元の三頂点を順に持つ実二射列。 -/
def verdierFullSLowerStrictChain : ComposableArrows _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} 2 :=
  (⟨ULift.up, fun _ _ h => h⟩ : Fin 3 →o ULift.{u} (Fin 3)).toFunctor ⋙
    verdierFullSLowerStrictDiagram d

/-- 同じ実二射列は、同じ最大 path 図式の二つの実短辺そのもの。 -/
theorem verdierFullSLowerStrictChain_eq :
    verdierFullSLowerStrictChain d = ComposableArrows.mk₂
      ((verdierFullSLowerStrictDiagram d).map (homOfLE
        (show (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 1 from by decide)))
      ((verdierFullSLowerStrictDiagram d).map (homOfLE
        (show (ULift.up (1 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 2 from by decide))) := by
  refine ComposableArrows.ext₂ ?_ ?_ ?_ ?_ ?_
  all_goals rfl

/-- 同じ最大化の全二胞体は、同じ実二射列の coherent 表示そのもの。 -/
theorem verdierFullSLowerMaximalization_eq_strictChain :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).app (Opposite.op ⦋2⦌)
        (verdierFullSLowerStrictChain d) := by
  have hF : verdierFullSLowerStrictDiagram d =
      (⟨ULift.down, fun _ _ h => h⟩ : ULift.{u} (Fin 3) →o Fin 3).toFunctor ⋙
        verdierFullSLowerStrictChain d := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro x y f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram (verdierFullSLowerStrictDiagram d) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization_eq_strictDiagram _
    _ = _ := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram hF

/-- 同じ最大化の全下側二胞体は、同じ二短辺の標準 coherent 合成二胞体に厳密一致。 -/
theorem verdierFullSLowerMaximalization_eq_compStruct :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct
        ((verdierFullSLowerStrictDiagram d).map (homOfLE
          (show (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 1 from by decide)))
        ((verdierFullSLowerStrictDiagram d).map (homOfLE
          (show (ULift.up (1 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 2 from by decide)))).simplex := by
  have h := congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).app (Opposite.op ⦋2⦌))
    (verdierFullSLowerStrictChain_eq d)
  exact (verdierFullSLowerMaximalization_eq_strictChain d).trans h

end SerrePositivity.KST.Fibration
