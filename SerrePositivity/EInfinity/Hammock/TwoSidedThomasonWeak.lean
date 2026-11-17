module

public import SerrePositivity.EInfinity.Hammock.TwoSidedThomasonLeftFactorization
public import SerrePositivity.EInfinity.Hammock.TwoSidedWeightedLeftWeak
public import SerrePositivity.EInfinity.Hammock.DoubleSimplicialWeak

/-!
# 元の二方向 Thomason 比較射自身の弱同値性

概要：任意の反変・共変 Cat 値図式の元の二方向 bar から全圏の nerve への射は弱同値。
方針：元の各右ラベル次数の左比較を対角へ送り、同じ元の一方向比較との因子化を使う。
規約：元の比較射を保ち、単体集合モデル・fiber の Kan 性・遷移の不変性は仮定しない。
使われ方：DK9.5と単体的な二方向 Grothendieck 比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedThomason
open CategoryTheory Opposite SerrePositivity.InfinityCategories

variable {W : Type u} [Category.{u} W]
  (F : Wᵒᵖ ⥤ Cat.{u, u}) (G : W ⥤ Cat.{u, u})

lemma weightedLeft_diagonalMap_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (TwoSidedWeightedLeft.diagonalMap F G) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (TwoSidedWeightedLeft.diagonalSourceIso F G).symm).isWeakHomotopyEquivalence.comp
      (DoubleSimplicial.diagonalFunctor_map_weak (TwoSidedWeightedLeft.rowMap F G)
        (fun n => TwoSidedWeightedLeft.map_isWeakHomotopyEquivalence F
          ((G ⋙ nerveFunctor).flip.obj n)))

lemma map_isWeakHomotopyEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (map F G) := by
  rw [← weightedLeft_map_factorization F G]
  exact (weightedLeft_diagonalMap_isWeakHomotopyEquivalence F G).comp
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.map_isWeakHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection F ⋙ G))

end SerrePositivity.EInfinity.Hammock.TwoSidedThomason
