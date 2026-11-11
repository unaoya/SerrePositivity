module
public import SerrePositivity.KST.SConstruction.FamilyCompositeImageClasses

/-! # 実合成三角形を元のパラメータ付き二次元写像に戻す
概要：三つの指定円柱を持つ内部 Hom の全二単体を実写像にし、三面を厳密に回収する。
方針：Yoneda と uncurry の自然性を同じ二単体の各面へ適用する。
規約：三角形を選び直さず、三円柱の全時刻の写像を保持する。
使われ方：保存済み段円柱の構造適合を単射源の相対持ち上げに渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {U E : SSet.{u}} {a b c : U ⟶ E}
  {first : SSet.Homotopy a b} {second : SSet.Homotopy b c} {direct : SSet.Homotopy a c}
  (t : SSet.Edge.CompStruct
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy first))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy second))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy direct)))

/-- 同じ実二単体を、元の全パラメータを持つ全三角形へ復号する。 -/
def familyCompStructRealization : U ⊗ (Δ[2] : SSet.{u}) ⟶ E :=
  uncurry (SSet.yonedaEquiv.symm t.simplex)

/-- 第一面は指定した元の第一円柱の全写像。 -/
lemma familyCompStructRealization_first :
    (U ◁ stdSimplex.δ 2) ≫ familyCompStructRealization t = first.h := by
  rw [familyCompStructRealization, ← uncurry_natural_left,
    stdSimplex.δ_comp_yonedaEquiv_symm, t.d₂]
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry first.h))) = first.h
  rw [Equiv.symm_apply_apply, uncurry_curry]

/-- 第二面は指定した元の第二円柱の全写像。 -/
lemma familyCompStructRealization_second :
    (U ◁ stdSimplex.δ 0) ≫ familyCompStructRealization t = second.h := by
  rw [familyCompStructRealization, ← uncurry_natural_left,
    stdSimplex.δ_comp_yonedaEquiv_symm, t.d₀]
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry second.h))) = second.h
  rw [Equiv.symm_apply_apply, uncurry_curry]

/-- 合成面も指定した元の直接円柱の全写像。 -/
lemma familyCompStructRealization_direct :
    (U ◁ stdSimplex.δ 1) ≫ familyCompStructRealization t = direct.h := by
  rw [familyCompStructRealization, ← uncurry_natural_left,
    stdSimplex.δ_comp_yonedaEquiv_symm, t.d₁]
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry direct.h))) = direct.h
  rw [Equiv.symm_apply_apply, uncurry_curry]

end SerrePositivity.KST.SConstruction
