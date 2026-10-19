module
public import SerrePositivity.InfinityCategories.Derived.SpanBoundaryAssembly
public import SerrePositivity.InfinityCategories.DGNerve.ProperEquationBianchi

/-! # span の後続の未知成分の右辺の閉性

概要：実際の境界から回収したデータで、後続の未知成分の方程式の右辺は閉じている。
方針：後続の真部分集合は既知なので、Bianchi の全ての残差が消える。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：D7 の δr₀=0 の実装。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories

open CategoryTheory Opposite DifferentialGraded DGNerve
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：後続集合の真部分集合は既知集合。
方針：真包含の非等号性と、逆の包含がある場合の反対称性を使う。
規約：HA Proposition 1.3.1.10。使われ方：Bianchi の真部分集合の方程式の回収。 -/
lemma spanSuffix_proper_known {n : ℕ} (J : Finset (Fin (n + 4)))
    (hJ : J ⊂ spanSuffixFaces n) : ¬ spanSuffixFaces n ⊆ J := by
  obtain ⟨hsub, hne⟩ := Finset.ssubset_iff_subset_ne.mp hJ
  intro h
  exact hne (Finset.Subset.antisymm hsub h)

namespace DGNerve.SimplexData

/-- 概要：既知集合で方程式を満たすデータでは後続の右辺は閉じている。
方針：後続の全ての真部分集合を既知集合として、真部分集合版 Bianchi を使う。
規約：HA Proposition 1.3.1.10。使われ方：未知の後続成分の閉じた右辺。 -/
lemma differential_rhs_spanSuffix {n : ℕ} (s : SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ spanSuffixFaces n ⊆ I → s.Equation I)
    (a b : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (spanSuffixFaces n).card)
    (ha : a = (spanSuffixFaces n).min' (Index.nonempty hI))
    (hb : b = (spanSuffixFaces n).max' (Index.nonempty hI))
    (hk : k = 2 - ((spanSuffixFaces n).card : ℤ)) :
    differential A (s.rhs (spanSuffixFaces n) a b k hI ha hb hk) = 0 :=
  s.differential_rhs_zero_of_proper_equations _
    (fun J hJ => hknown J (spanSuffix_proper_known J hJ)) a b k hI ha hb hk

end DGNerve.SimplexData

/-- 概要：実際の境界からの左データの後続の右辺は閉じている。
方針：全既知方程式の回収と後続集合の Bianchi の閉性を合成する。
規約：HA Proposition 1.3.1.10。使われ方：左側で δr₀=0 を得る。 -/
lemma spanBoundaryLeftData_suffix_rhs_closed {n : ℕ}
    (F : join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ dgNerve A D)
    (unknown : HomFamily A D (SelectedFaces.vertexObj _ (spanSuffixFaces_covers n)
      (spanBoundaryLeft F)))
    (a b : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (spanSuffixFaces n).card)
    (ha : a = (spanSuffixFaces n).min' (Index.nonempty hI))
    (hb : b = (spanSuffixFaces n).max' (Index.nonempty hI))
    (hk : k = 2 - ((spanSuffixFaces n).card : ℤ)) :
    differential A ((spanBoundaryLeftData F unknown).rhs
      (spanSuffixFaces n) a b k hI ha hb hk) = 0 :=
  (spanBoundaryLeftData F unknown).differential_rhs_spanSuffix
    (spanBoundaryLeftData_equation F unknown) a b k hI ha hb hk

/-- 概要：実際の境界からの右データの後続の右辺は閉じている。
方針：全既知方程式の回収と後続集合の Bianchi の閉性を合成する。
規約：HA Proposition 1.3.1.10。使われ方：右側で δr₀=0 を得る。 -/
lemma spanBoundaryRightData_suffix_rhs_closed {n : ℕ}
    (F : join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ dgNerve A D)
    (unknown : HomFamily A D (SelectedFaces.vertexObj _ (spanSuffixFaces_covers n)
      (spanBoundaryRight F)))
    (a b : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (spanSuffixFaces n).card)
    (ha : a = (spanSuffixFaces n).min' (Index.nonempty hI))
    (hb : b = (spanSuffixFaces n).max' (Index.nonempty hI))
    (hk : k = 2 - ((spanSuffixFaces n).card : ℤ)) :
    differential A ((spanBoundaryRightData F unknown).rhs
      (spanSuffixFaces n) a b k hI ha hb hk) = 0 :=
  (spanBoundaryRightData F unknown).differential_rhs_spanSuffix
    (spanBoundaryRightData_equation F unknown) a b k hI ha hb hk

end SerrePositivity.InfinityCategories
