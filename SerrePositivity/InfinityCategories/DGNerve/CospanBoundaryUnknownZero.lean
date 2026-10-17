module
public import SerrePositivity.InfinityCategories.DGNerve.CospanBoundaryZeroData

/-! # 零未知境界データの全未知成分

概要：実際の境界から組み立てた零未知データは先頭集合を含む全成分で零。
方針：その集合は選んだどの面にも含まれず、組み立ての零の分岐になる。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：三角形の残差を右辺の負へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：左の零未知境界データは先頭集合を含む全ての成分で零。
方針：被覆面を選べないことから組み立ての未知分岐を評価する。
規約：HA Proposition 1.3.1.10。使われ方：左の三つの未知残差を各右辺の負へ変える。 -/
lemma cospanBoundaryLeftZeroData_unknownHom {n : ℕ}
    (F : join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ dgNerve A D)
    (I : Finset (Fin (n + 4))) (hprefix : cospanPrefixFaces n ⊆ I)
    (a b : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (cospanBoundaryLeftZeroData F).hom I a b k hI ha hb hk = 0 := by
  have hn : ¬ ∃ j ∈ cospanPrefixFaces n, j ∉ I := by
    rintro ⟨j, hj, hjI⟩
    exact hjI (hprefix hj)
  simp only [cospanBoundaryLeftZeroData, cospanBoundaryLeftData, SelectedFaces.assembleData,
    dite_eq_right hn]

/-- 概要：右の零未知境界データは先頭集合を含む全ての成分で零。
方針：被覆面を選べないことから組み立ての未知分岐を評価する。
規約：HA Proposition 1.3.1.10。使われ方：右の三つの未知残差を各右辺の負へ変える。 -/
lemma cospanBoundaryRightZeroData_unknownHom {n : ℕ}
    (F : join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ dgNerve A D)
    (I : Finset (Fin (n + 4))) (hprefix : cospanPrefixFaces n ⊆ I)
    (a b : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (cospanBoundaryRightZeroData F).hom I a b k hI ha hb hk = 0 := by
  have hn : ¬ ∃ j ∈ cospanPrefixFaces n, j ∉ I := by
    rintro ⟨j, hj, hjI⟩
    exact hjI (hprefix hj)
  simp only [cospanBoundaryRightZeroData, cospanBoundaryRightData, SelectedFaces.assembleData,
    dite_eq_right hn]

end SerrePositivity.InfinityCategories.DGNerve
