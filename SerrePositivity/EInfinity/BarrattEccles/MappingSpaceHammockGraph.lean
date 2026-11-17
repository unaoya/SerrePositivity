module

public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceWeakThreeArrow
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ThreeArrowEquivalence

/-!
# 元の Map^h と三列の hammock graph の比較

概要：任意の可換環上で、同じ元の共通始域から三列の hammock graph へ比較する。
方針：弱同値の両脚を持つ三本矢との比較と、固定語の明示的な圏同値を合成。
規約：これは固定語の graph との比較であり、全語の余極限との比較は後続。
使われ方：既存 Map^h から実際の hammock 局所化への高次比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory _root_.HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 実際の同じ E 代数の弱同値を使う固定語の hammock graph。 -/
abbrev algebraHammockGraph (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : (operad A).Algebra) : SSet.{u + 1} :=
  let := modelCategory A
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph (weakEquivalences (operad A).Algebra) w X Y

/-- 同じ元の全単体の共通始域から三列の graph へ入れる比較。 -/
def mappingSpaceHammockGraphNerveMap (X Y : (operad A).Algebra) :
    nerve (ULiftHom.{u + 1} (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      algebraHammockGraph A _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow X Y := by
  let := modelCategory A
  exact mappingSpaceWeakThreeArrowNerveMap A X Y ≫ nerveMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor

/-- 元の三列の graph への比較そのものも anodyne 局所化で可逆。 -/
lemma mappingSpaceHammockGraphNerveMap_localized_isIso (X Y : (operad A).Algebra) :
    IsIso (AnodyneHomotopy.anodyneQ.map (mappingSpaceHammockGraphNerveMap A X Y)) := by
  let := modelCategory A
  have := mappingSpaceWeakThreeArrowNerveMap_localized_isIso A X Y
  have := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.nerveMap_localized_isIso X Y
  dsimp only [mappingSpaceHammockGraphNerveMap]
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

/-- 同じ元の比較は、graph の Kan 性を追加仮定せず弱ホモトピー同値。 -/
lemma mappingSpaceHammockGraphNerveMap_isWeakHomotopyEquivalence
    (X Y : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (mappingSpaceHammockGraphNerveMap A X Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (mappingSpaceHammockGraphNerveMap_localized_isIso A X Y)

/-- 同じ共通始域の二射による Map^h と三列の graph の局所化後の同型。 -/
def mappingSpaceHammockGraphComparisonIso (X Y : (operad A).Algebra) :
    AnodyneHomotopy.anodyneQ.obj
        (SSet.uliftFunctor.{u + 1, u}.obj (((mappingSpace A).obj (op X)).obj Y)) ≅
      AnodyneHomotopy.anodyneQ.obj (algebraHammockGraph A _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow X Y) := by
  let := modelCategory A
  have := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.nerveMap_localized_isIso X Y
  exact mappingSpaceWeakThreeArrowComparisonIso A X Y ≪≫
    asIso (AnodyneHomotopy.anodyneQ.map (nerveMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor))

/-- 同じ元の左射の後の同型は、同じ graph への右射を回収する。 -/
lemma mappingSpaceHammockGraphComparisonIso_fac (X Y : (operad A).Algebra) :
    AnodyneHomotopy.anodyneQ.map (mappingSpaceIndexAugmentation A X Y) ≫
        (mappingSpaceHammockGraphComparisonIso A X Y).hom =
      AnodyneHomotopy.anodyneQ.map (mappingSpaceHammockGraphNerveMap A X Y) := by
  let := modelCategory A
  change AnodyneHomotopy.anodyneQ.map (mappingSpaceIndexAugmentation A X Y) ≫
    ((mappingSpaceWeakThreeArrowComparisonIso A X Y).hom ≫
      AnodyneHomotopy.anodyneQ.map (nerveMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor)) = _
  rw [← Category.assoc, mappingSpaceWeakThreeArrowComparisonIso_fac,
    ← CategoryTheory.Functor.map_comp]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
