module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ThreeArrowLeftReplacement
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ThreeArrowRightReplacement
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection

/-!
# 特殊な三本矢と弱同値の両脚を持つ三本矢の比較

概要：元の特殊な三本矢の包含の nerve そのものが弱ホモトピー同値となる。
方針：左脚と右脚の関手的置換による二つの充満忠実な包含の反転性を合成。
規約：元のモデル圏と指定した関手的分解を使い、元の対象の cofibrancy は要求しない。
使われ方：Low 命題3.5 の特殊な三本矢から一般の三本矢への工程。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory _root_.HomotopicalAlgebra

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialThreeArrowComparison
open _root_.SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- 元の両脚・中間射・全縦射を保持する特殊な三本矢からの包含。 -/
abbrev inclusion (X Y : C) : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y ⥤ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.inclusion (fun _ _ _ h => h.2) (fun _ _ _ h => h.2)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialThreeArrowComparison (inclusion)


/-- 二つの片脚の包含の合成は同じ元の包含。 -/
lemma inclusion_fac (X Y : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.specialInclusion : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y ⥤ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y) ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.leftInclusion =
      inclusion X Y := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialThreeArrowComparison (inclusion_fac)


/-- 元の特殊な三本矢の包含の nerve そのものは anodyne 局所化で可逆。 -/
lemma inclusion_localized_isIso
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X Y : C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (inclusion X Y))) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement.inclusion_localized_isIso cof (X := X) (Y := Y)
  have := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement.inclusion_localized_isIso fib (X := X) (Y := Y)
  rw [← inclusion_fac]
  change IsIso (AnodyneHomotopy.anodyneQ.map
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.specialInclusion : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y ⥤ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y) ≫
      nerveMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.leftInclusion))
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialThreeArrowComparison (inclusion_localized_isIso)


/-- 同じ元の包含は、元の両 nerve の Kan 性なしで弱ホモトピー同値。 -/
lemma inclusion_isWeakHomotopyEquivalence
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (nerveMap (inclusion X Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _ (inclusion_localized_isIso cof fib X Y)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialThreeArrowComparison (inclusion_isWeakHomotopyEquivalence)


end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialThreeArrowComparison
