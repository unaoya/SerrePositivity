module

public import SerrePositivity.EInfinity.BarrattEccles.AlgebraRelativeHammockWeak
public import SerrePositivity.EInfinity.BarrattEccles.ReducedHammockWeakComparison

/-!
# 元の cofibrant DK 入力から全代数の hammock への実際の包含

概要：同じ元の包含で全 zigzag を送り、元の全代数の reduced hammock への弱同値を得る。
方針：同じ Hom の宇宙での相対比較と、元の ULift の厳密な逆を合成する。
規約：元の cofibrant 代数と全代数の射・単体を保持する。
使われ方：実 DK Hom と既存 Map^h の高次比較の共通 hammock。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory _root_.HomotopicalAlgebra
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]
def algebraHammockHomLiftIso (X Y : (operad A).Algebra) :
    Hammock.reducedSimplicialSet (algebraRelativeCategory A).weakEquivalences
      (ULiftHom.objUp.{u + 1, u + 1} X) (ULiftHom.objUp.{u + 1, u + 1} Y) ≅ algebraReducedHammock A
        X Y := by
  let := modelCategory A
  exact Hammock.HomLift.reducedIso (C := (operad A).Algebra)
    (weakEquivalences (operad A).Algebra) X Y
variable (X Y : (cofibrantAlgebraRelativeCategory A).category)
def cofibrantAlgebraHammockInclusionMap :
    Hammock.reducedSimplicialSet (cofibrantAlgebraRelativeCategory A).weakEquivalences X Y ⟶
      algebraReducedHammock A ((cofibrantAlgebraDKInclusion A).obj X)
        ((cofibrantAlgebraDKInclusion A).obj Y) :=
  Hammock.Relative.reducedMap (cofibrantToAlgebraDKRelative A) X Y ≫
    (algebraHammockHomLiftIso A ((cofibrantAlgebraDKInclusion A).obj X)
      ((cofibrantAlgebraDKInclusion A).obj Y)).hom
lemma cofibrantAlgebraHammockInclusionMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantAlgebraHammockInclusionMap A X Y) :=
  (cofibrantToAlgebraDK_reducedMap_weak A X Y).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
      (algebraHammockHomLiftIso A ((cofibrantAlgebraDKInclusion A).obj X)
        ((cofibrantAlgebraDKInclusion A).obj Y))).isWeakHomotopyEquivalence

def cofibrantAlgebraHammockGraphInclusionMap (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph (cofibrantAlgebraRelativeCategory A).weakEquivalences w X Y ⟶
      algebraHammockGraph A w ((cofibrantAlgebraDKInclusion A).obj X)
        ((cofibrantAlgebraDKInclusion A).obj Y) := by
  let := modelCategory A
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagramMap (cofibrantToAlgebraDKRelative A) X Y).app w ≫
    (Hammock.HomLift.graphIso (C := (operad A).Algebra) (weakEquivalences (operad A).Algebra)
      w ((cofibrantAlgebraDKInclusion A).obj X) ((cofibrantAlgebraDKInclusion A).obj Y)).hom
lemma cofibrantAlgebraHammockGraphInclusionMap_app (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (n : SimplexCategoryᵒᵖ)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph (cofibrantAlgebraRelativeCategory A).weakEquivalences w X Y).obj n) :
    let := modelCategory A
    (cofibrantAlgebraHammockGraphInclusionMap A X Y w).app n σ =
      σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (cofibrantAlgebraDKInclusionRelative A) := by
  let := modelCategory A
  rfl
end SerrePositivity.EInfinity.BarrattEccles
