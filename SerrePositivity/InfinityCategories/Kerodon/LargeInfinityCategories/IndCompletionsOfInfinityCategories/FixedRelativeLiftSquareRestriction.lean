module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FixedRelativeLiftRestriction

/-!
概要：指定領域の固定を、同じ底上の可換な制限正方形を通じて回収する。
方針：内部 Hom の包含後で制限を比較し、元の相対 fiber へ等式を戻す。
規約：固定図式の表示変更を仮定しない。使われ方：元の sourceTip の全族の固定。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 指定領域の固定条件は、可換正方形で表示した同じ部分領域にも全次数で戻る。 -/
lemma relativeLiftFixedBoundaryInclusion_square {A T U K E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : T ⟶ A) (f : A ⟶ E) (hf : f ≫ p = b)
    (j : U ⟶ A) (a : K ⟶ U) (k : K ⟶ T) (he : a ≫ j = k ≫ i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeLiftFixedBoundaryInclusion p b i f hf ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p b j ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p (j ≫ b) a =
        SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (a ≫ (j ≫ b)) (a ≫ (j ≫ f))
          (by rw [Category.assoc, Category.assoc, hf])) := by
  have h := congrArg (fun r => r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom K).map p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((k ≫ i) ≫ b)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeLiftFixedBoundaryInclusion_restrict p b i f hf k)
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre_ι, SSet.const_comp] at h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeLiftFixedBoundaryInclusion p b i f hf ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b) ≫ (pre (k ≫ i)).app E =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((k ≫ i) ≫ f)) at h
  have hm : (pre j).app E ≫ (pre a).app E = (pre (k ≫ i)).app E := by
    rw [← NatTrans.comp_app, ← pre_map, he]
  have ht : (k ≫ i) ≫ f = a ≫ (j ≫ f) := by rw [← he, Category.assoc]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom K).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (a ≫ (j ≫ b)))
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre_ι, SSet.const_comp]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeLiftFixedBoundaryInclusion p b i f hf ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b) ≫ (pre j).app E ≫ (pre a).app E =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (a ≫ (j ≫ f)))
  rw [hm]
  exact h.trans (congrArg (fun r => SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex r)) ht)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
