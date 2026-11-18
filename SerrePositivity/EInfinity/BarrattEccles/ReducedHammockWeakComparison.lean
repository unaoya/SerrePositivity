module

public import SerrePositivity.EInfinity.BarrattEccles.HammockColimitWeakComparison
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ThreeArrowReducedWeakComparison

/-!
# 任意可換環の元の Map^h と reduced hammock の弱比較

概要：元の Map^h の同じ共通始域から reduced hammock への右射を構成し、弱同値を証明。
方針：元の全語の余極限への右射に、元の縮約同型を合成する。
規約：元の augmentation への回収式を保持する。既存 DK Hom との比較は後続。
使われ方：自由相対解像と hammock の比較に用いる元の高次の弱比較。
-/

@[expose] public section
universe u
noncomputable section
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory _root_.HomotopicalAlgebra SerrePositivity.InfinityCategories Opposite

variable (A : Type u) [CommRing A]

def algebraReducedHammock (X Y : (operad A).Algebra) : SSet.{u + 1} := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedSimplicialSet (weakEquivalences (operad A).Algebra) X Y

def algebraHammockReductionIso (X Y : (operad A).Algebra) :
    algebraHammockColimitGraph A X Y ≅ algebraReducedHammock A X Y := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso (weakEquivalences (operad A).Algebra) X Y

def mappingSpaceReducedHammockNerveMap (X Y : (operad A).Algebra) :
    nerve (ULiftHom.{u + 1} (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      algebraReducedHammock A X Y :=
  mappingSpaceHammockColimitNerveMap A X Y ≫ (algebraHammockReductionIso A X Y).hom

lemma mappingSpaceReducedHammockNerveMap_augmentation (X Y : (operad A).Algebra) :
    mappingSpaceReducedHammockNerveMap A X Y ≫ (algebraHammockReductionIso A X Y).inv =
      mappingSpaceHammockColimitNerveMap A X Y := by
  simp only [mappingSpaceReducedHammockNerveMap, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

lemma mappingSpaceReducedHammockNerveMap_isWeakHomotopyEquivalence
    (X Y : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (mappingSpaceReducedHammockNerveMap A X Y) := by
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (algebraHammockReductionIso A X Y).hom :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _ (by infer_instance)
  exact (mappingSpaceHammockColimitNerveMap_isWeakHomotopyEquivalence A X Y).comp hi

end SerrePositivity.EInfinity.BarrattEccles
