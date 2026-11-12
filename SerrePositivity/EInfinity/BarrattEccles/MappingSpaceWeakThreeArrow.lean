module

public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceSpecialHammockComparison
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialThreeArrowComparison

/-!
# 元の Map^h と弱同値の両脚を持つ三本矢の比較

概要：任意の可換環上で、同じ共通始域から一般の三本矢へ入れる比較を反転する。
方針：元の二つの関手的分解を三本矢の包含へ代入し、同じ元の右射と合成。
規約：元の代数の cofibrancy・単体集合モデル・hammock 比較を追加入力にしない。
使われ方：Map^h と実際の hammock 局所化への高次比較の次の工程。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 元の E 代数の弱同値の両脚を持つ三本矢の圏。 -/
abbrev algebraWeakThreeArrow (X Y : (operad A).Algebra) :=
  let := modelCategory A
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y

/-- 同じ元の特殊な三本矢を、弱同値の三本矢へ入れる nerve の射。 -/
def algebraSpecialThreeArrowInclusionNerveMap (X Y : (operad A).Algebra) :
    nerve (algebraSpecialHammock A X Y) ⟶ nerve (algebraWeakThreeArrow A X Y) := by
  let := modelCategory A
  exact nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialThreeArrowComparison.inclusion X Y)

/-- 同じ元の三本矢の包含を実際の分解で反転する。 -/
lemma algebraSpecialThreeArrowInclusionNerveMap_localized_isIso
    (X Y : (operad A).Algebra) :
    IsIso (AnodyneHomotopy.anodyneQ.map (algebraSpecialThreeArrowInclusionNerveMap A X Y)) := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialThreeArrowComparison.inclusion_localized_isIso
    (mappingCofibrantFactorization A) (mappingFibrantFactorization A) X Y

/-- 同じ元の全単体の共通始域から弱同値の三本矢へ送る比較。 -/
def mappingSpaceWeakThreeArrowNerveMap (X Y : (operad A).Algebra) :
    nerve (ULiftHom.{u + 1} (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      nerve (algebraWeakThreeArrow A X Y) :=
  mappingSpaceSpecialHammockNerveMap A X Y ≫ algebraSpecialThreeArrowInclusionNerveMap A X Y

/-- 元の共通始域から同じ弱同値の三本矢への比較そのものも反転される。 -/
lemma mappingSpaceWeakThreeArrowNerveMap_localized_isIso (X Y : (operad A).Algebra) :
    IsIso (AnodyneHomotopy.anodyneQ.map (mappingSpaceWeakThreeArrowNerveMap A X Y)) := by
  have := mappingSpaceSpecialHammockNerveMap_localized_isIso A X Y
  have := algebraSpecialThreeArrowInclusionNerveMap_localized_isIso A X Y
  dsimp only [mappingSpaceWeakThreeArrowNerveMap]
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

/-- 同じ元の比較射は、元の三本矢の nerve の Kan 性なしで弱ホモトピー同値。 -/
lemma mappingSpaceWeakThreeArrowNerveMap_isWeakHomotopyEquivalence
    (X Y : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (mappingSpaceWeakThreeArrowNerveMap A X Y) :=
  FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (mappingSpaceWeakThreeArrowNerveMap_localized_isIso A X Y)

/-- 元の同じ二射から定める、Map^h と一般の三本矢の局所化後の同型。 -/
def mappingSpaceWeakThreeArrowComparisonIso (X Y : (operad A).Algebra) :
    AnodyneHomotopy.anodyneQ.obj
        (SSet.uliftFunctor.{u + 1, u}.obj (((mappingSpace A).obj (op X)).obj Y)) ≅
      AnodyneHomotopy.anodyneQ.obj (nerve (algebraWeakThreeArrow A X Y)) := by
  have := algebraSpecialThreeArrowInclusionNerveMap_localized_isIso A X Y
  exact mappingSpaceSpecialHammockComparisonIso A X Y ≪≫
    asIso (AnodyneHomotopy.anodyneQ.map (algebraSpecialThreeArrowInclusionNerveMap A X Y))

/-- 元の左射との合成は、元の同じ一般の三本矢への右射を回収。 -/
lemma mappingSpaceWeakThreeArrowComparisonIso_fac (X Y : (operad A).Algebra) :
    AnodyneHomotopy.anodyneQ.map (mappingSpaceIndexAugmentation A X Y) ≫
        (mappingSpaceWeakThreeArrowComparisonIso A X Y).hom =
      AnodyneHomotopy.anodyneQ.map (mappingSpaceWeakThreeArrowNerveMap A X Y) := by
  change AnodyneHomotopy.anodyneQ.map (mappingSpaceIndexAugmentation A X Y) ≫
    ((mappingSpaceSpecialHammockComparisonIso A X Y).hom ≫ AnodyneHomotopy.anodyneQ.map
      (algebraSpecialThreeArrowInclusionNerveMap A X Y)) = _
  rw [← Category.assoc, mappingSpaceSpecialHammockComparisonIso_fac,
    ← CategoryTheory.Functor.map_comp]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
