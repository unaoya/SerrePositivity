module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IndBaseResolution

/-!
概要：Ind 模型での固定入力上の比較同型を元の底へ反映する。
方針：共通解像の自明 Kan 射で同型を回収し、元の底への射影と厳密な切断を相殺する。
規約：入力と標的の全図式を保つ。
使われ方：元の引き戻し内の compact 成分対の厳密化。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：Ind 模型へ送った入力付き頂点の同型は元の底の同じ入力上の同型へ戻る。
方針：Ind 射影の二重 slice 後合成の充満忠実性で同型を取り、元の底への射影で戻す。
規約：元の二つの頂点と全入力を厳密に回収する。
使われ方：相対交互構成で得た最終比較同型の元の底への降下。 -/
lemma IndBaseResolution.nonempty_inputVertexIso_of_comparison
    {μ : Cardinal.{u}} {B K : SSet.{u + 1}} [Quasicategory B]
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IndBaseResolution μ B) (q : K ⟶ B) (z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q)
    {u v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q)).symm z)) _⦋0⦌}
    (e : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp q R.comparison (q ≫ R.comparison) rfl z
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone R.comparison z) rfl).app (Opposite.op ⦋0⦌) u)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp q R.comparison (q ≫ R.comparison) rfl z
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone R.comparison z) rfl).app (Opposite.op ⦋0⦌) v))) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso u v) := by
  let qt := q ≫ R.toResolution
  let zt := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone R.toResolution z
  let qm := q ≫ R.comparison
  let zm := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone R.comparison z
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp q R.toResolution qt rfl z zt rfl
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp qt R.toModel qm (Category.assoc q R.toResolution R.toModel)
    zt zm (Category.assoc z.val R.toResolution R.toModel)
  have hq : qt ≫ R.toBase = q := by
    dsimp only [qt]
    rw [Category.assoc, R.section_property, Category.comp_id]
  have hz : zt.val ≫ R.toBase = z.val := by
    change (z.val ≫ R.toResolution) ≫ R.toBase = z.val
    rw [Category.assoc, R.section_property, Category.comp_id]
  let U := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp qt R.toBase q hq zt z hz
  have hTS : T ≫ S = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp q R.comparison qm rfl z zm rfl := by
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp_comp q R.toResolution qt rfl R.toModel qm
      (Category.assoc q R.toResolution R.toModel) z zt zm rfl
      (Category.assoc z.val R.toResolution R.toModel)
  have hTU : T ≫ U = 𝟙 _ := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp_comp q R.toResolution qt rfl R.toBase q hq z zt z rfl hz
    simpa only [R.section_property, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp_id] using h
  have hS : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration S :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp_trivialKanFibration qt R.toModel qm
      (Category.assoc q R.toResolution R.toModel) zt zm
      (Category.assoc z.val R.toResolution R.toModel)
  have hu (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q)).symm z)) _⦋0⦌) :
      U.app (Opposite.op ⦋0⦌) (T.app (Opposite.op ⦋0⦌) x) = x := by
    exact congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x) hTU
  obtain ⟨e⟩ := e
  have e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((T ≫ S).app (Opposite.op ⦋0⦌) u)
      ((T ≫ S).app (Opposite.op ⦋0⦌) v) := by
    rw [hTS]
    exact e
  let e₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration S).isFullyFaithful.preimageVertexIso e'
  have e₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e₀ U
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (U.app (Opposite.op ⦋0⦌) (T.app (Opposite.op ⦋0⦌) u))
    (U.app (Opposite.op ⦋0⦌) (T.app (Opposite.op ⦋0⦌) v)) at e₁
  exact ⟨by simpa only [hu] using e₁⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
