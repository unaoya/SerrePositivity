module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.InputHomotopyClassComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomotopyTriangleFillingCriterion
/-! # 元入力を二次元全体で固定する指定三辺の比較

概要：同じ入力を全時間で保つ三変形を、その三辺を変えずに相対二次元比較へ充填する。
方針：内部 Hom の自明 Kan 射影に、指定三角形境界と基底の定値二単体を持ち上げる。
規約：三辺の代表と二次元全体の基底像を厳密に保持する。
使われ方：共通補正端からの二変形を、選択済みの第一・第二変形へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
lemma dgGluingInputHomotopyDiagram_constant {K E B : SSet.{u}} (p : E ⟶ B)
    {f g : K ⟶ E} (H : SSet.Homotopy f g) (a : K ⟶ B)
    (hH : H.h ≫ p = fst K (Δ[1] : SSet.{u}) ≫ a) :
    curry H.h ≫ (ihom K).map p =
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) : (Δ[1] : SSet.{u}) ⟶ _) := by
  rw [← curry_natural_right]
  apply uncurry_injective
  rw [uncurry_curry, hH, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
lemma dgGluingInputHomotopyTriangle_relative_filling {K E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    {f g h : K ⟶ E} (l : SSet.Homotopy f g) (r : SSet.Homotopy g h)
    (d : SSet.Homotopy f h) (a : K ⟶ B)
    (hl : l.h ≫ p = fst K (Δ[1] : SSet.{u}) ≫ a)
    (hr : r.h ≫ p = fst K (Δ[1] : SSet.{u}) ≫ a)
    (hd : d.h ≫ p = fst K (Δ[1] : SSet.{u}) ≫ a) :
    ∃ T : (Δ[2] : SSet.{u}) ⟶ (ihom K).obj E,
      (boundary 2).ι ≫ T = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleBoundary l r d ∧
      T ≫ (ihom K).map p = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) := by
  have hb : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleBoundary l r d ≫ (ihom K).map p =
      (boundary 2).ι ≫ (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) : Δ[2] ⟶ _) := by
    apply boundary.hom_ext
    intro i
    fin_cases i
    · erw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleBoundary_zero,
        dgGluingInputHomotopyDiagram_constant p r a hr,
        ← Category.assoc, boundary.ι_ι, SSet.comp_const]
    · erw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleBoundary_one,
        dgGluingInputHomotopyDiagram_constant p d a hd,
        ← Category.assoc, boundary.ι_ι, SSet.comp_const]
    · erw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleBoundary_two,
        dgGluingInputHomotopyDiagram_constant p l a hl,
        ← Category.assoc, boundary.ι_ι, SSet.comp_const]
  have : HasLiftingProperty (boundary 2).ι ((ihom K).map p) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary ((ihom K).map p)).1 inferInstance 2
  let sq : CommSq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleBoundary l r d) (boundary 2).ι
      ((ihom K).map p) (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)) := ⟨hb⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
