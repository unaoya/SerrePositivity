module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StrictRightFibrationTotalAssembly
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveTransportPrism

/-!
概要：元の二段間の weighted 輸送円柱は、元の全空間余極限での値を厳密に保つ。
方針：under-category の最後の構造射による係数輸送を元の余錐の自然性で消す。
規約：遷移射の可逆性は不要。使われ方：coslice 全図式の後続段への輸送。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {C : SSet.{u}} {I : Type u} [SmallCategory I] (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject C)

/-- under の全係数評価は元の余極限への脚を厳密に保持する。 -/
lemma weightedNerveUnderEvaluation_assembly (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveUnderEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F) i ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationTotalAssembly F =
        snd (nerve (Under i)) ((F.obj i).val.left) ≫ colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F) i := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, x⟩
  change SSet.yonedaEquiv (((stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n n _) ≫
    SSet.yonedaEquiv.symm x) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F).map (σ.obj (Fin.last n)).hom) ≫
    colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F) (σ.obj (Fin.last n)).right) =
      (colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F) i).app (Opposite.op ⦋n⦌) x
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.assoc, colimit.w, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- 元の遷移に沿う同じ輸送円柱は、全空間余極限への射を厳密に固定する。 -/
lemma weightedNerveTransportPrism_assembly {i j : I} (v : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveTransportPrism (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F) v ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationTotalAssembly F =
        snd (Δ[1] : SSet.{u}) ((F.obj i).val.left) ≫ colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F) i := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveTransportPrism, Category.assoc, weightedNerveUnderEvaluation_assembly,
    ← Category.assoc]
  exact congrArg (fun h => h ≫ colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F) i)
    (whiskerRight_snd _ ((F.obj i).val.left))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
