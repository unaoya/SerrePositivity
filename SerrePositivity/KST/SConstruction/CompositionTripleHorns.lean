module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleRightTetrahedron
public import SerrePositivity.KST.SConstruction.HornHomExt

/-! # 元の全三合成面を保持する二向きの結合替えホーン
概要：左右の結合替えの全指定三面を同じ実ホーンへ束ね、後合成との可換性を回収する。
方針：既存の三次内ホーンの貼り合わせと、全標準面による等号判定を使う。
規約：元の全三面を保持し、標的の Kan 性や新しい面の選択を要求しない。
使われ方：指定全基底四面体を保つ、六結合替えの相対持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial
variable {E : SSet.{u}} {w x y z : E _⦋0⦌}
  {a : E.Edge w x} {b : E.Edge x y} {c : E.Edge y z}
  {ab : E.Edge w y} {bc : E.Edge x z} {abc : E.Edge w z}
  (first : SSet.Edge.CompStruct a b ab) (second : SSet.Edge.CompStruct b c bc)

/-- 元の右結合面を持つ、左結合を回収するための同じ全第一内ホーン。 -/
def compositionTripleHorn (right : SSet.Edge.CompStruct a bc abc) :=
  (horn₃₁.exists_desc (SSet.yonedaEquiv.symm second.simplex)
    (SSet.yonedaEquiv.symm right.simplex) (SSet.yonedaEquiv.symm first.simplex)
    (by simp) (by simp) (by simp)).choose

/-- 第一内ホーンの零面は元の同じ後二射全面。 -/
lemma compositionTripleHorn_zero (right : SSet.Edge.CompStruct a bc abc) :
    horn₃₁.ι₀ ≫ compositionTripleHorn first second right =
      SSet.yonedaEquiv.symm second.simplex :=
  (horn₃₁.exists_desc _ _ _ (by simp) (by simp) (by simp)).choose_spec.1

/-- 第一内ホーンの第二面は元の同じ右結合全面。 -/
lemma compositionTripleHorn_two (right : SSet.Edge.CompStruct a bc abc) :
    horn₃₁.ι₂ ≫ compositionTripleHorn first second right =
      SSet.yonedaEquiv.symm right.simplex :=
  (horn₃₁.exists_desc _ _ _ (by simp) (by simp) (by simp)).choose_spec.2.1

/-- 第一内ホーンの第三面は元の同じ前二射全面。 -/
lemma compositionTripleHorn_three (right : SSet.Edge.CompStruct a bc abc) :
    horn₃₁.ι₃ ≫ compositionTripleHorn first second right =
      SSet.yonedaEquiv.symm first.simplex :=
  (horn₃₁.exists_desc _ _ _ (by simp) (by simp) (by simp)).choose_spec.2.2

/-- 元の左結合面を持つ、右結合を回収するための同じ全第二内ホーン。 -/
def compositionTripleRightHorn (left : SSet.Edge.CompStruct ab c abc) :=
  (horn₃₂.exists_desc (SSet.yonedaEquiv.symm second.simplex)
    (SSet.yonedaEquiv.symm left.simplex) (SSet.yonedaEquiv.symm first.simplex)
    (by simp) (by simp) (by simp)).choose

/-- 第二内ホーンの零面は元の同じ後二射全面。 -/
lemma compositionTripleRightHorn_zero (left : SSet.Edge.CompStruct ab c abc) :
    horn₃₂.ι₀ ≫ compositionTripleRightHorn first second left =
      SSet.yonedaEquiv.symm second.simplex :=
  (horn₃₂.exists_desc _ _ _ (by simp) (by simp) (by simp)).choose_spec.1

/-- 第二内ホーンの第一面は元の同じ左結合全面。 -/
lemma compositionTripleRightHorn_one (left : SSet.Edge.CompStruct ab c abc) :
    horn₃₂.ι₁ ≫ compositionTripleRightHorn first second left =
      SSet.yonedaEquiv.symm left.simplex :=
  (horn₃₂.exists_desc _ _ _ (by simp) (by simp) (by simp)).choose_spec.2.1

/-- 第二内ホーンの第三面は元の同じ前二射全面。 -/
lemma compositionTripleRightHorn_three (left : SSet.Edge.CompStruct ab c abc) :
    horn₃₂.ι₃ ≫ compositionTripleRightHorn first second left =
      SSet.yonedaEquiv.symm first.simplex :=
  (horn₃₂.exists_desc _ _ _ (by simp) (by simp) (by simp)).choose_spec.2.2

/-- 指定三面を持つ元の全四面体は同じ全第一内ホーンを厳密に回収する。 -/
lemma compositionTripleHorn_fac {right : SSet.Edge.CompStruct a bc abc}
    (R : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleTetrahedron first second right) :
    (horn 3 (1 : Fin 4)).ι ≫ SSet.yonedaEquiv.symm R.simplex =
      compositionTripleHorn first second right := by
  apply hornHomExt
  intro j hj
  rcases (show j = 0 ∨ j = 2 ∨ j = 3 by fin_cases j <;> simp_all) with rfl | rfl | rfl
  · rw [← Category.assoc, horn.ι_ι, stdSimplex.δ_comp_yonedaEquiv_symm, R.second_face,
      compositionTripleHorn_zero]
  · rw [← Category.assoc, horn.ι_ι, stdSimplex.δ_comp_yonedaEquiv_symm, R.right_face,
      compositionTripleHorn_two]
  · rw [← Category.assoc, horn.ι_ι, stdSimplex.δ_comp_yonedaEquiv_symm, R.first_face,
      compositionTripleHorn_three]

/-- 指定三面を持つ元の全四面体は同じ全第二内ホーンを厳密に回収する。 -/
lemma compositionTripleRightHorn_fac {left : SSet.Edge.CompStruct ab c abc}
    (R : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleRightTetrahedron first second left) :
    (horn 3 (2 : Fin 4)).ι ≫ SSet.yonedaEquiv.symm R.simplex =
      compositionTripleRightHorn first second left := by
  apply hornHomExt
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 3 by fin_cases j <;> simp_all) with rfl | rfl | rfl
  · rw [← Category.assoc, horn.ι_ι, stdSimplex.δ_comp_yonedaEquiv_symm, R.second_face,
      compositionTripleRightHorn_zero]
  · rw [← Category.assoc, horn.ι_ι, stdSimplex.δ_comp_yonedaEquiv_symm, R.left_face,
      compositionTripleRightHorn_one]
  · rw [← Category.assoc, horn.ι_ι, stdSimplex.δ_comp_yonedaEquiv_symm, R.first_face,
      compositionTripleRightHorn_three]

/-- 元の全三面を保つ第一内ホーンの後合成は、同じ全面の後合成からのホーン。 -/
lemma compositionTripleHorn_post {B : SSet.{u}} (p : E ⟶ B)
    (right : SSet.Edge.CompStruct a bc abc) :
    compositionTripleHorn first second right ≫ p =
      compositionTripleHorn (first.map p) (second.map p) (right.map p) := by
  apply hornHomExt
  intro j hj
  rcases (show j = 0 ∨ j = 2 ∨ j = 3 by fin_cases j <;> simp_all) with rfl | rfl | rfl
  · rw [← Category.assoc, compositionTripleHorn_zero, compositionTripleHorn_zero]
    exact SSet.yonedaEquiv_symm_comp _ _
  · rw [← Category.assoc, compositionTripleHorn_two, compositionTripleHorn_two]
    exact SSet.yonedaEquiv_symm_comp _ _
  · rw [← Category.assoc, compositionTripleHorn_three, compositionTripleHorn_three]
    exact SSet.yonedaEquiv_symm_comp _ _

/-- 元の全三面を保つ第二内ホーンの後合成も、同じ全面の後合成からのホーン。 -/
lemma compositionTripleRightHorn_post {B : SSet.{u}} (p : E ⟶ B)
    (left : SSet.Edge.CompStruct ab c abc) :
    compositionTripleRightHorn first second left ≫ p =
      compositionTripleRightHorn (first.map p) (second.map p) (left.map p) := by
  apply hornHomExt
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 3 by fin_cases j <;> simp_all) with rfl | rfl | rfl
  · rw [← Category.assoc, compositionTripleRightHorn_zero, compositionTripleRightHorn_zero]
    exact SSet.yonedaEquiv_symm_comp _ _
  · rw [← Category.assoc, compositionTripleRightHorn_one, compositionTripleRightHorn_one]
    exact SSet.yonedaEquiv_symm_comp _ _
  · rw [← Category.assoc, compositionTripleRightHorn_three, compositionTripleRightHorn_three]
    exact SSet.yonedaEquiv_symm_comp _ _

end SerrePositivity.KST.SConstruction
