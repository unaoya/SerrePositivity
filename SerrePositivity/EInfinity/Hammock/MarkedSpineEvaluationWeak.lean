module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineProductsIso
public import SerrePositivity.EInfinity.Hammock.MarkedValueSpineProductsIso
public import SerrePositivity.EInfinity.Hammock.MarkedSpineGluingExtraction

/-!
# 元の全因子列の指定因子の評価の弱同値性

概要：元の hammock の全因子を同じ自由 groupoid の値へ評価する写像は弱同値。
方針：元の全因子列を生成列ごとの有限直積の和へ戻し、同じ全評価を比較する。
規約：元の射自身と長さ零の終端因子も保持する。
使われ方：通常の局所化への元の右比較の全自由次数。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (Y : Paths C)
  {n : SimplexCategoryᵒᵖ}

lemma evaluatePoint_unpack (X : Paths C) (gs : List (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W))
    (p : (products W (AllMarked.nativeSpace W) Y X gs).obj n) :
    evaluatePoint (unpack X gs p) = unpackValue X gs
      ((productsMap W (AllMarked.nativeValue W) Y X gs).app n p) := by
  induction gs generalizing X with
  | nil => rfl
  | cons g gs ih =>
    exact congrArg (ValueSpine.cons X g ((AllMarked.nativeValue W X g.val.left).app n p.1))
      (ih g.val.right p.2)

lemma productsIso_evaluation (X : Paths C) :
    (productsIso W Y X).hom ≫ evaluation W Y X =
      sumProductsMap W (AllMarked.nativeValue W) Y X ≫ (valueProductsIso W Y X).hom := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  exact evaluatePoint_unpack W Y X s.1 s.2

lemma evaluation_isWeakHomotopyEquivalence (X : Paths C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (evaluation W Y X) := by
  have hw := sumProductsMap_weak W (AllMarked.nativeValue W)
    (AllMarked.nativeValue_isWeakHomotopyEquivalence W) Y X
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (productsIso W Y X)).isWeakHomotopyEquivalence.cancel_left
  rw [productsIso_evaluation]
  exact hw.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (valueProductsIso W Y X)).isWeakHomotopyEquivalence

def hammockEvaluation (X : Paths C) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y ⟶ valueSpace W Y X :=
  (markedSpineIso W Y X).hom ≫ evaluation W Y X

lemma hammockEvaluation_isWeakHomotopyEquivalence (X : Paths C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (hammockEvaluation W Y X) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (markedSpineIso W Y X)).isWeakHomotopyEquivalence.comp
    (evaluation_isWeakHomotopyEquivalence W Y X)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
