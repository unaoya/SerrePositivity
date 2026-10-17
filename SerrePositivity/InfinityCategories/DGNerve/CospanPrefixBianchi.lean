module
public import SerrePositivity.InfinityCategories.DGNerve.CospanIndexGeometry
public import SerrePositivity.InfinityCategories.DGNerve.CospanBoundaryAssembly
public import SerrePositivity.InfinityCategories.DGNerve.ProperEquationBianchi

/-! # cospan の先頭の未知成分の右辺の閉性

概要：実際の境界から回収したデータで、先頭の未知成分の方程式の右辺は閉じている。
方針：先頭の真部分集合は既知なので、Bianchi の全ての残差が消える。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：N7c の δr₀=0 の実装。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：先頭集合の真部分集合は既知集合。
方針：真包含の非等号性と、逆の包含がある場合の反対称性を使う。
規約：HA Proposition 1.3.1.10。使われ方：Bianchi の真部分集合の方程式の回収。 -/
lemma cospanPrefix_proper_known {n : ℕ} (J : Finset (Fin (n + 4)))
    (hJ : J ⊂ cospanPrefixFaces n) : ¬ cospanPrefixFaces n ⊆ J := by
  obtain ⟨hsub, hne⟩ := Finset.ssubset_iff_subset_ne.mp hJ
  intro h
  exact hne (Finset.Subset.antisymm hsub h)

namespace SimplexData

/-- 概要：既知集合で方程式を満たすデータでは先頭の右辺は閉じている。
方針：先頭の全ての真部分集合を既知集合として、真部分集合版 Bianchi を使う。
規約：HA Proposition 1.3.1.10。使われ方：未知の先頭成分の閉じた右辺。 -/
lemma differential_rhs_cospanPrefix {n : ℕ} (s : SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ cospanPrefixFaces n ⊆ I → s.Equation I)
    (a b : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (cospanPrefixFaces n).card)
    (ha : a = (cospanPrefixFaces n).min' (Index.nonempty hI))
    (hb : b = (cospanPrefixFaces n).max' (Index.nonempty hI))
    (hk : k = 2 - ((cospanPrefixFaces n).card : ℤ)) :
    differential A (s.rhs (cospanPrefixFaces n) a b k hI ha hb hk) = 0 :=
  s.differential_rhs_zero_of_proper_equations _
    (fun J hJ => hknown J (cospanPrefix_proper_known J hJ)) a b k hI ha hb hk

end SimplexData

/-- 概要：実際の境界からの左データの先頭の右辺は閉じている。
方針：全既知方程式の回収と先頭集合の Bianchi の閉性を合成する。
規約：HA Proposition 1.3.1.10。使われ方：左側で δr₀=0 を得る。 -/
lemma cospanBoundaryLeftData_prefix_rhs_closed {n : ℕ}
    (F : join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ dgNerve A D)
    (unknown : HomFamily A D (SelectedFaces.vertexObj _ (cospanPrefixFaces_covers n)
      (cospanBoundaryLeft F)))
    (a b : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (cospanPrefixFaces n).card)
    (ha : a = (cospanPrefixFaces n).min' (Index.nonempty hI))
    (hb : b = (cospanPrefixFaces n).max' (Index.nonempty hI))
    (hk : k = 2 - ((cospanPrefixFaces n).card : ℤ)) :
    differential A ((cospanBoundaryLeftData F unknown).rhs
      (cospanPrefixFaces n) a b k hI ha hb hk) = 0 :=
  (cospanBoundaryLeftData F unknown).differential_rhs_cospanPrefix
    (cospanBoundaryLeftData_equation F unknown) a b k hI ha hb hk

/-- 概要：実際の境界からの右データの先頭の右辺は閉じている。
方針：全既知方程式の回収と先頭集合の Bianchi の閉性を合成する。
規約：HA Proposition 1.3.1.10。使われ方：右側で δr₀=0 を得る。 -/
lemma cospanBoundaryRightData_prefix_rhs_closed {n : ℕ}
    (F : join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ dgNerve A D)
    (unknown : HomFamily A D (SelectedFaces.vertexObj _ (cospanPrefixFaces_covers n)
      (cospanBoundaryRight F)))
    (a b : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (cospanPrefixFaces n).card)
    (ha : a = (cospanPrefixFaces n).min' (Index.nonempty hI))
    (hb : b = (cospanPrefixFaces n).max' (Index.nonempty hI))
    (hk : k = 2 - ((cospanPrefixFaces n).card : ℤ)) :
    differential A ((cospanBoundaryRightData F unknown).rhs
      (cospanPrefixFaces n) a b k hI ha hb hk) = 0 :=
  (cospanBoundaryRightData F unknown).differential_rhs_cospanPrefix
    (cospanBoundaryRightData_equation F unknown) a b k hI ha hb hk

end SerrePositivity.InfinityCategories.DGNerve
