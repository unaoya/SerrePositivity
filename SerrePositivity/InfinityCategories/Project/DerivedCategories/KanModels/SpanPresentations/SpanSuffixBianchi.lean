module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanBoundaryAssembly
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ProperEquationBianchi

/-! # span の後続の未知成分の右辺の閉性

概要：実際の境界から回収したデータで、後続の未知成分の方程式の右辺は閉じている。
方針：後続の真部分集合は既知なので、Bianchi の全ての残差が消える。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：D7 の δr₀=0 の実装。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 概要：後続集合の真部分集合は既知集合。
方針：真包含の非等号性と、逆の包含がある場合の反対称性を使う。
規約：HA Proposition 1.3.1.10。使われ方：Bianchi の真部分集合の方程式の回収。 -/
lemma spanSuffix_proper_known {n : ℕ} (J : Finset (Fin (n + 4)))
    (hJ : J ⊂ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) : ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ J := by
  obtain ⟨hsub, hne⟩ := Finset.ssubset_iff_subset_ne.mp hJ
  intro h
  exact hne (Finset.Subset.antisymm hsub h)

namespace DGNerve.SimplexData

/-- 概要：既知集合で方程式を満たすデータでは後続の右辺は閉じている。
方針：後続の全ての真部分集合を既知集合として、真部分集合版 Bianchi を使う。
規約：HA Proposition 1.3.1.10。使われ方：未知の後続成分の閉じた右辺。 -/
lemma differential_rhs_spanSuffix {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I → s.Equation I)
    (a b : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).card)
    (ha : a = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).card : ℤ)) :
    differential A (s.rhs (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) a b k hI ha hb hk) = 0 :=
  s.differential_rhs_zero_of_proper_equations _
    (fun J hJ => hknown J (spanSuffix_proper_known J hJ)) a b k hI ha hb hk

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData (differential_rhs_spanSuffix)


end DGNerve.SimplexData

/-- 概要：実際の境界からの左データの後続の右辺は閉じている。
方針：全既知方程式の回収と後続集合の Bianchi の閉性を合成する。
規約：HA Proposition 1.3.1.10。使われ方：左側で δr₀=0 を得る。 -/
lemma spanBoundaryLeftData_suffix_rhs_closed {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (unknown : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.vertexObj _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_covers n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeft F)))
    (a b : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).card)
    (ha : a = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).card : ℤ)) :
    differential A ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftData F unknown).rhs
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) a b k hI ha hb hk) = 0 :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftData F unknown).differential_rhs_spanSuffix
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftData_equation F unknown) a b k hI ha hb hk

/-- 概要：実際の境界からの右データの後続の右辺は閉じている。
方針：全既知方程式の回収と後続集合の Bianchi の閉性を合成する。
規約：HA Proposition 1.3.1.10。使われ方：右側で δr₀=0 を得る。 -/
lemma spanBoundaryRightData_suffix_rhs_closed {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (unknown : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.vertexObj _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_covers n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRight F)))
    (a b : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).card)
    (ha : a = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).card : ℤ)) :
    differential A ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightData F unknown).rhs
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) a b k hI ha hb hk) = 0 :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightData F unknown).differential_rhs_spanSuffix
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightData_equation F unknown) a b k hI ha hb hk

end SerrePositivity.InfinityCategories.Project.DerivedCategories
