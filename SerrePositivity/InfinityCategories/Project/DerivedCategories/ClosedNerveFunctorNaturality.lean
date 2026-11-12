module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.NerveInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedEdges

/-! # 閉 nerve の包含と dg 関手の全単体的自然性

概要：元の閉零圏の nerve 包含は、dg 関手による全高次単体の写像と厳密に可換。
方針：次数零で閉射の像を照合し、他の次数の零を保つことから単体の全成分を比較する。
規約：対象と Hom の独立宇宙を保つ。使われ方：商側の厳密屋根の実屋根への写像。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]

/-- 閉 nerve の次数 k の成分は、dg 関手の元の次数 k の線形写像で写る。 -/
lemma dgFunctor_closedNerveHom (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) {x y : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D}
    (f : x ⟶ y) (k : ℤ) :
    (F.map x y).f k (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom f k) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (F.onClosed.map f) k := by
  by_cases hk : k = 0
  · subst k
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_zero, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_zero]
    exact (congrArg Subtype.val (F.closedHomEquiv_map f)).symm
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_of_ne _ k hk, map_zero, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_of_ne _ k hk]

/-- 閉射列の dg 単体化と dg 関手による写像は全次元で可換。 -/
lemma dgFunctor_closedNerveSimplex (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) {n : ℕ}
    (s : ComposableArrows (_root_.SerrePositivity.DifferentialGraded.ClosedCategory A D) n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex s).map F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (s ⋙ F.onClosed) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext rfl ?_
  apply heq_of_eq
  funext I a b k hI ha hb hk
  exact dgFunctor_closedNerveHom A D E F _ k

/-- 元の通常の閉 nerve の包含は、元の dg 関手の nerve と厳密に可換。 -/
lemma closedNerveInclusion_dgFunctor (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveInclusion A D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F =
      nerveMap F.onClosed ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveInclusion A E := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  exact dgFunctor_closedNerveSimplex A D E F s

end SerrePositivity.InfinityCategories.Project.DerivedCategories
