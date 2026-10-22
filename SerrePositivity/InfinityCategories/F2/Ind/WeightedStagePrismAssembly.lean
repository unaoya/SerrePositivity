module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightFibrationTotalAssembly
public import SerrePositivity.InfinityCategories.F1.WeightedNerveTransportPrism

/-!
概要：元の二段間の weighted 輸送円柱は、元の全空間余極限での値を厳密に保つ。
方針：under-category の最後の構造射による係数輸送を元の余錐の自然性で消す。
規約：遷移射の可逆性は不要。使われ方：coslice 全図式の後続段への輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C)

/-- under の全係数評価は元の余極限への脚を厳密に保持する。 -/
lemma weightedNerveUnderEvaluation_assembly (i : I) :
    weightedNerveUnderEvaluation (rightFibrationTotalDiagram F) i ≫
      strictRightFibrationTotalAssembly F =
        snd (nerve (Under i)) ((F.obj i).val.left) ≫ colimit.ι (rightFibrationTotalDiagram F) i := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, x⟩
  change SSet.yonedaEquiv (((stdSimplex.map (simplexPrefixInclusion n n _) ≫
    SSet.yonedaEquiv.symm x) ≫ (rightFibrationTotalDiagram F).map (σ.obj (Fin.last n)).hom) ≫
    colimit.ι (rightFibrationTotalDiagram F) (σ.obj (Fin.last n)).right) =
      (colimit.ι (rightFibrationTotalDiagram F) i).app (Opposite.op ⦋n⦌) x
  rw [simplexPrefixInclusion_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.assoc, colimit.w, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- 元の遷移に沿う同じ輸送円柱は、全空間余極限への射を厳密に固定する。 -/
lemma weightedNerveTransportPrism_assembly {i j : I} (v : i ⟶ j) :
    weightedNerveTransportPrism (rightFibrationTotalDiagram F) v ≫
      strictRightFibrationTotalAssembly F =
        snd (Δ[1] : SSet.{u}) ((F.obj i).val.left) ≫ colimit.ι (rightFibrationTotalDiagram F) i := by
  rw [weightedNerveTransportPrism, Category.assoc, weightedNerveUnderEvaluation_assembly,
    ← Category.assoc]
  exact congrArg (fun h => h ≫ colimit.ι (rightFibrationTotalDiagram F) i)
    (whiskerRight_snd _ ((F.obj i).val.left))

end SerrePositivity.InfinityCategories.F2.Ind
