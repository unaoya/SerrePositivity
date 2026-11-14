module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKConeZeroRow
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConeLegSimplex
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardLeg
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeConeTopEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedEdges
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentLowComparison

/-!
概要：元の積Totのnative錐の指定脚を、第0頂点による標準脚と照合する。
方針：同じweighted一単体の実比較を閉零射の成分で評価する。
規約：IS-W2 C01。型と元の脚を固定する。
使われ方：HA 1.2.4、D(A)への同じ指定錐の輸送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 元のTot錐の脚は、第0頂点を通る同じ標準閉射の一次単体。 -/
theorem nativeDGCone_standardLeg (X : CosimplicialObject (Complex A)) (n : SimplexCategory) :
    (derivedConeLeg (nativeDGCone X) (ULift.up (nerveVertex (AsSmall.up.obj n)))).edge =
      (dgClosedEdge A (Complex A)
        ((SerrePositivity.EInfinity.ComplexLimits.complexToClosed A).map
          (standardLeg A X n))).edge := by
  rw [nativeDGCone_leg_simplex]
  apply Simplex.edgeEquiv.injective
  dsimp only [Simplex.edgeEquiv, Equiv.coe_fn_mk]
  refine Sigma.ext ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    change ((coherentComparison (R := A) (D := Complex A)).app (Opposite.op ⦋1⦌) _).edgeHom
      (0 : Fin 2) (1 : Fin 2) (by decide) = _
    rw [coherentComparison_edgeHom]
    change standardTopEval (R := A) (D := Complex A) ((productTotalFunctor A).obj X)
      (X.obj n) 0
      (((liftedEnrichedBousfieldKanCone X).app (AsSmall.up.obj n)).app
        (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 (AsSmall.up.obj n))))) =
      (closedHomEquiv A (Complex A) _ _
        ((SerrePositivity.EInfinity.ComplexLimits.complexToClosed A).map
          (standardLeg A X n))).val
    let j := Opposite.op (Opposite.op n)
    let s : (((Functor.flip (SimplicialObject.opFunctor.obj bousfieldKanSetWeight)) ⋙
        SSet.uliftFunctor.{u,0}).obj j) _⦋0⦌ :=
      ULift.up (nerveVertex (Over.mk (𝟙 n)))
    let T := (productTotalFunctor A).obj X
    let e := Functor.isoWhiskerRight
      (standardDoldKanModuleIso (R := A) (D := Complex A) T (X.obj n))
        (forget (ModuleCat A))
    let g := (reversedWeightPointwiseBousfieldKanCone X).app j ≫ e.inv
    change standardTopEval T (X.obj n) 0 (g.app (Opposite.op ⦋0⦌) s) = _
    have h := reflectedBKFreeCone_generator_top X j 0 s
    erw [← h]
    have hc : CochainComplex.HomComplex.Cochain.ofHom (standardLeg A X n) =
        (closedHomEquiv A (Complex A) _ _
          ((SerrePositivity.EInfinity.ComplexLimits.complexToClosed A).map
            (standardLeg A X n))).val := by
      have h := complexClosedHomEquiv_cochain A T (X.obj n)
        ((SerrePositivity.EInfinity.ComplexLimits.complexToClosed A).map (standardLeg A X n))
      have hf := SerrePositivity.EInfinity.ComplexLimits.complexToClosed_map A (standardLeg A X n)
      change complexClosedHomEquiv A T (X.obj n)
        ((SerrePositivity.EInfinity.ComplexLimits.complexToClosed A).map (standardLeg A X n)) =
          standardLeg A X n at hf
      rw [hf] at h
      exact h
    exact (reflectedBKCone_zero_generator X n).trans hc

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
