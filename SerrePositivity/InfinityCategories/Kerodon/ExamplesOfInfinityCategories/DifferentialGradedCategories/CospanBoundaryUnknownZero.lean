module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanBoundaryZeroData

/-! # 零未知境界データの全未知成分

概要：実際の境界から組み立てた零未知データは先頭集合を含む全成分で零。
方針：その集合は選んだどの面にも含まれず、組み立ての零の分岐になる。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：三角形の残差を右辺の負へ移す。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：左の零未知境界データは先頭集合を含む全ての成分で零。
方針：被覆面を選べないことから組み立ての未知分岐を評価する。
規約：HA Proposition 1.3.1.10。使われ方：左の三つの未知残差を各右辺の負へ変える。 -/
lemma cospanBoundaryLeftZeroData_unknownHom {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (I : Finset (Fin (n + 4))) (hprefix : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n ⊆ I)
    (a b : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData F).hom I a b k hI ha hb hk = 0 := by
  have hn : ¬ ∃ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n, j ∉ I := by
    rintro ⟨j, hj, hjI⟩
    exact hjI (hprefix hj)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftData, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceAssembly.assembleData,
    dite_eq_right hn]

/-- 概要：右の零未知境界データは先頭集合を含む全ての成分で零。
方針：被覆面を選べないことから組み立ての未知分岐を評価する。
規約：HA Proposition 1.3.1.10。使われ方：右の三つの未知残差を各右辺の負へ変える。 -/
lemma cospanBoundaryRightZeroData_unknownHom {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (I : Finset (Fin (n + 4))) (hprefix : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n ⊆ I)
    (a b : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData F).hom I a b k hI ha hb hk = 0 := by
  have hn : ¬ ∃ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n, j ∉ I := by
    rintro ⟨j, hj, hjI⟩
    exact hjI (hprefix hj)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightData, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceAssembly.assembleData,
    dite_eq_right hn]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
