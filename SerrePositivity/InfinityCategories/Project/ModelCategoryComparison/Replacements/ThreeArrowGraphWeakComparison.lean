module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ThreeArrowCompositeWeakComparison

/-!
# 元の三列の graph から全語の余極限への標準射の弱同値性

概要：元の graphInclusion at threeArrow 自身は弱ホモトピー同値となる。
方針：padding の左逆から前合成の全射性、元の合成の単射性から単射性を得る。
規約：全 Kan 標的への元の Hom の π₀ で検査し、元の標準射を保持する。
使われ方：元の Map^h と hammock・DK Hom の高次比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra _root_.SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{v} C] [ModelCategory C] (X Y : C)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

include cof in
lemma paddingColimitMap_isWeakHomotopyEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingColimitMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y)) := by
  intro Z hZ
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y
  let K := _root_.SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.homComponents Z
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (weakEquivalences C) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingColimitMap H
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingColimitRetraction H
  have hcomp := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.threeArrowPaddingComposite_isWeakHomotopyEquivalence X Y cof Z
  change Function.Bijective (K.map (i ≫ p).op) at hcomp
  have hc : Function.Bijective (fun x => (K.map i.op) ((K.map p.op) x)) := by
    change Function.Bijective (K.map p.op ≫ K.map i.op)
    rw [← K.map_comp]
    exact hcomp
  have hr : K.map r.op ≫ K.map p.op = 𝟙 _ := by
    rw [← K.map_comp]
    change K.map (p ≫ r).op = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingColimitMap_retraction]
    exact K.map_id _
  change Function.Bijective (K.map p.op)
  constructor
  · intro x y hxy
    apply hc.1
    exact congrArg (K.map i.op) hxy
  · intro x
    exact ⟨(K.map r.op) x, congrArg (fun f => f x) hr⟩

include cof in
lemma threeArrowGraphInclusion_isWeakHomotopyEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (weakEquivalences C) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow) :=
  (paddingColimitMap_isWeakHomotopyEquivalence X Y cof).cancel_right
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.threeArrowPaddingComposite_isWeakHomotopyEquivalence X Y cof)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
