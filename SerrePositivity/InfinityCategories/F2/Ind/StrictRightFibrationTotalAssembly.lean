module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightFibrationDiagramColimit
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveConstantEvaluation
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveConstantNaturality
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveCocartesianFibration

/-!
概要：strict right fibration 図式の weighted 全空間を、元の全空間の通常の余極限へ送る。
方針：元の余極限の全脚を weighted nerve に写し、定値係数を評価する。
規約：比較射の cofinality は別工程。使われ方：各段と全空間の密度余極限の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C)

/-- 元の全空間の weighted nerve から、同じ通常の全空間余極限への実際の比較。 -/
def strictRightFibrationTotalAssembly :
    weightedNerve (rightFibrationTotalDiagram F) ⟶ colimit (rightFibrationTotalDiagram F) :=
  weightedNerveMap (colimit.cocone (rightFibrationTotalDiagram F)).ι ≫
    weightedNerveConstantEvaluation I (colimit (rightFibrationTotalDiagram F))

/-- 全比較の各単体は、元の最後の係数を同じ余極限の脚で写す。 -/
lemma strictRightFibrationTotalAssembly_app {n : ℕ}
    (s : weightedNerveSimplex (rightFibrationTotalDiagram F) n) :
    (strictRightFibrationTotalAssembly F).app (Opposite.op ⦋n⦌) s =
      SSet.yonedaEquiv (s.2.app (Fin.last n) ≫
        colimit.ι (rightFibrationTotalDiagram F) (s.1.obj (Fin.last n))) := rfl

/-- 同じ比較を各段の fiber に制限すると、元の通常の余極限の脚そのもの。 -/
lemma strictRightFibrationTotalAssembly_coefficient (i : I) :
    weightedNerveConstantLift (rightFibrationTotalDiagram F) i ≫
      strictRightFibrationTotalAssembly F = colimit.ι (rightFibrationTotalDiagram F) i := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  change SSet.yonedaEquiv ((stdSimplex.map (simplexPrefixInclusion n n _) ≫
    SSet.yonedaEquiv.symm x) ≫ colimit.ι (rightFibrationTotalDiagram F) i) = _
  rw [simplexPrefixInclusion_id, CategoryTheory.Functor.map_id, Category.id_comp,
    SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- 同じ全比較は、元の各段の射影が定める同じ weighted な底への射を保つ。 -/
lemma strictRightFibrationTotalAssembly_projection :
    strictRightFibrationTotalAssembly F ≫ strictRightFibrationColimitProjection F =
      weightedNerveMap (rightFibrationProjectionCocone F).ι ≫
        weightedNerveConstantEvaluation I C := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change (strictRightFibrationColimitProjection F).app (Opposite.op ⦋n⦌)
      (SSet.yonedaEquiv (s.2.app (Fin.last n) ≫
        colimit.ι (rightFibrationTotalDiagram F) (s.1.obj (Fin.last n)))) =
    SSet.yonedaEquiv (s.2.app (Fin.last n) ≫ (F.obj (s.1.obj (Fin.last n))).val.hom)
  rw [← SSet.yonedaEquiv_comp, Category.assoc, strictRightFibrationColimitProjection_ι]
  rfl

/-- 元の底が quasicategory なら、同じ weighted 全空間も quasicategory。 -/
instance strictRightFibrationWeightedTotal_quasicategory [Quasicategory C] :
    Quasicategory (weightedNerve (rightFibrationTotalDiagram F)) := by
  have (i : I) : Quasicategory ((rightFibrationTotalDiagram F).obj i) :=
    quasicategory_of_innerFibration (F.obj i).val.hom
  exact quasicategory_of_innerFibration (weightedNerveProjection (rightFibrationTotalDiagram F))

end SerrePositivity.InfinityCategories.F2.Ind
