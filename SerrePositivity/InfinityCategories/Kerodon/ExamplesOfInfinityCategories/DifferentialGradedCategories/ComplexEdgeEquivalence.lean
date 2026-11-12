module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomotopyCategory
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import Mathlib.Algebra.Homology.QuasiIso

/-! # dg nerve の同型な辺と複体のホモトピー同値

概要：複体 dg nerve のホモトピー圏で同型となる辺は、実際の chain map のホモトピー同値を与える。
方針：N3 の H⁰ 比較、既存の複体ホモトピー圏との比較、Mathlib の同型の特徴づけを合成する。
規約：HA §1.3.1、Kerodon §2.5.3（Tag 00PK）。使われ方：極限錐の比較辺から擬同型を得る。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A]

/-- 概要：複体 dg nerve の端点付き辺を通常の chain map に変換する。
方針：辺の閉零射と非有界複体の閉零射・chain map の同値を合成する。
規約：HA Example 1.3.1.8。使われ方：錐の比較辺の実際の複体の射。 -/
def edgeChainMap {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)) _⦋0⦌}
    (f : SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A (Complex A)) x y) : x.obj 0 ⟶ y.obj 0 :=
  _root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv A _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed f)

/-- 概要：辺の chain map のホモトピー商は、辺の類を H⁰ と複体ホモトピー圏へ送ったものに等しい。
方針：N3 の代表元の式と複体比較の商関手との可換性を使う。
規約：Kerodon §2.5.3（Tag 00PK）。使われ方：同型射の像を実際の chain map のホモトピー類と同定する。 -/
lemma edgeChainMap_quotient {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)) _⦋0⦌}
    (f : SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A (Complex A)) x y) :
    (_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap f) =
      (_root_.SerrePositivity.DifferentialGraded.complexHomotopyComparison A).map ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 A (Complex A)).map
        (SSet.Truncated.HomotopyCategory₂.homMk f)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0_homMk]
  change ((closedToComplex A) ⋙ _root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).map
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed f) =
    ((toHomotopy A (Complex A)) ⋙ complexHomotopyComparison A).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed f)
  rfl

/-- 概要：辺のホモトピー類が同型なら、その chain map はホモトピー同値。
方針：二つの比較関手で同型を保ち、Mathlib のホモトピー商における同型の特徴づけを使う。
規約：HA §1.3.1。使われ方：引き戻しの比較射が擬同型であることの直前の段階。 -/
lemma edgeChainMap_homotopyEquivalence {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)) _⦋0⦌}
    (f : SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A (Complex A)) x y)
    (hf : IsIso (SSet.Truncated.HomotopyCategory₂.homMk f)) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} A) (.up ℤ) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap f) := by
  have := hf
  apply (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences _).mp
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap_quotient]
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
