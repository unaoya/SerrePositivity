module

public import SerrePositivity.EInfinity.Hammock.DoubleSimplicialWeak
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarPointwiseInvariance

/-!
# 元の二重単体集合の列ごとの弱同値から対角へ

概要：元の二重単体集合を転置した各行の弱同値は、元の対角射自身の弱同値を与える。
方針：既存の対角交換同型とその自然性で元の行ごとの判定へ戻す。
規約：元の対角射を保持し、単体集合のモデル構造を要求しない。
使われ方：DK の二方向 bar と多重単体的比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.DoubleSimplicial
open CategoryTheory SerrePositivity.InfinityCategories

lemma diagonalFunctor_map_weak_of_columns {B D : SimplicialObject SSet.{u}} (f : B ⟶ D)
    (hf : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (((flipFunctor _ _ _).map f).app n)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map f) := by
  have h := diagonalFunctor_map_weak ((flipFunctor _ _ _).map f) hf
  have hB := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.diagonalFlipIso B)).isWeakHomotopyEquivalence
  have hD := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.diagonalFlipIso D)).isWeakHomotopyEquivalence
  have hc := h.comp hD
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    (SerrePositivity.BisimplicialModel.diagonal.map ((flipFunctor _ _ _).map f) ≫
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.diagonalFlipIso D).hom) at hc
  rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.diagonalFlipIso_naturality f] at hc
  exact hB.cancel_left hc

end SerrePositivity.EInfinity.Hammock.DoubleSimplicial
