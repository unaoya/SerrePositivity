module

public import SerrePositivity.EInfinity.BarrattEccles.MappingRightHomBarInclusion
public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceSpanComparison

/-!
# 元の Map^h と同じ全単体添字から全右脚の bar への比較

概要：元の fibrant 置換の右脚に値の包含を代入し、同じ Map^h の射を反転する。
方針：全右脚での定理を適用し、既存の共通添字 augmentation と合成する。
規約：元の Map^h・関手的分解・右脚・共通添字を変更しない。
使われ方：元の三本矢の nerve への右射と bar 比較を照合するための入力。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.SimplicialModel

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 元の Map^h に使う同じ fibrant 置換の右脚。 -/
def mappingFibrantRightLeg (Y : (operad A).Algebra) : algebraRightSpanBase A Y := by
  let := modelCategory A
  exact MorphismProperty.Under.mk ⊤ ((fibrantTargetComparison
    (mappingFibrantFactorization A)).app Y)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fibrantTargetComparison_trivialCofibration (mappingFibrantFactorization A) Y)

/-- 同じ Map^h から、元の右脚の全 Hom 図式の bar への値の包含。 -/
def mappingSpaceBarInclusion (X Y : (operad A).Algebra) :
    SSet.uliftFunctor.{u + 1, u}.obj (((mappingSpace A).obj (op X)).obj Y) ⟶
      (BarConstruction.functor (algebraRightSpanBase A Y)).obj
        (mappingRightHomDiagram A X Y) := by
  let := modelCategory A
  exact mappingRightHomBarInclusion A X Y (mappingFibrantRightLeg A Y)

/-- 全次数で元の単体を、同じ置換の右脚で一定の射列に送る。 -/
lemma mappingSpaceBarInclusion_app (X Y : (operad A).Algebra)
    (n : SimplexCategoryᵒᵖ) (x : (((mappingSpace A).obj (op X)).obj Y).obj n) :
    (mappingSpaceBarInclusion A X Y).app n (ULift.up x) =
      (Functor.const _).obj (((mappingRightHomDiagram A X Y).flip.obj n).elementsMk
        (mappingFibrantRightLeg A Y) x) := rfl

/-- 同じ元の Map^h から全右脚の bar への射そのものは局所化で可逆。 -/
lemma mappingSpaceBarInclusion_localized_isIso (X Y : (operad A).Algebra) :
    IsIso (AnodyneHomotopy.anodyneQ.map (mappingSpaceBarInclusion A X Y)) := by
  let := modelCategory A
  exact mappingRightHomBarInclusion_localized_isIso A X Y (mappingFibrantRightLeg A Y)

/-- 元の全単体の同じ共通始域から、全右脚の bar への比較射。 -/
def mappingSpaceIndexBarMap (X Y : (operad A).Algebra) :
    nerve (ULiftHom.{u + 1} (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      (BarConstruction.functor (algebraRightSpanBase A Y)).obj
        (mappingRightHomDiagram A X Y) :=
  mappingSpaceIndexAugmentation A X Y ≫ mappingSpaceBarInclusion A X Y

/-- 元の共通添字から同じ bar への合成も局所化で可逆。 -/
lemma mappingSpaceIndexBarMap_localized_isIso (X Y : (operad A).Algebra) :
    IsIso (AnodyneHomotopy.anodyneQ.map (mappingSpaceIndexBarMap A X Y)) := by
  have := mappingSpaceIndexAugmentation_localized_isIso A X Y
  have := mappingSpaceBarInclusion_localized_isIso A X Y
  dsimp only [mappingSpaceIndexBarMap]
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.EInfinity.BarrattEccles
