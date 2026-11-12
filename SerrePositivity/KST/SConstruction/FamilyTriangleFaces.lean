module
public import SerrePositivity.KST.SConstruction.FamilyTriangleStripComparison

/-! # 元の全三角形から端点の合う三円柱を取り出す
概要：パラメータ付き二単体の三面を、元の全区間を保つ三円柱と実合成構造にする。
方針：三つの共有頂点を標準単体で照合し、元の全二単体を curry する。
規約：三角形・面を選び直さず、実写像全体を回収する。
使われ方：元の合成適合三角形と全交換列を同じ辺路比較へ渡す。
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

/-- 三角形の最初の辺の終点は、第二辺の始点そのもの。 -/
lemma familyTriangleCorner_middle (U : SSet.{u}) :
    SSet.ι₁ ≫ (U ◁ stdSimplex.δ (2 : Fin 3)) =
      SSet.ι₀ ≫ (U ◁ stdSimplex.δ (0 : Fin 3)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 合成辺と第一辺は同じ始点を持つ。 -/
lemma familyTriangleCorner_source (U : SSet.{u}) :
    SSet.ι₀ ≫ (U ◁ stdSimplex.δ (1 : Fin 3)) =
      SSet.ι₀ ≫ (U ◁ stdSimplex.δ (2 : Fin 3)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 合成辺と第二辺は同じ終点を持つ。 -/
lemma familyTriangleCorner_target (U : SSet.{u}) :
    SSet.ι₁ ≫ (U ◁ stdSimplex.δ (1 : Fin 3)) =
      SSet.ι₁ ≫ (U ◁ stdSimplex.δ (0 : Fin 3)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 元の全三角形の第一面を、第二面の始点と端点が合う実円柱として取り出す。 -/
def familyTriangleFirst {U E : SSet.{u}} (T : U ⊗ (Δ[2] : SSet.{u}) ⟶ E) :
    SSet.Homotopy (SSet.ι₀ ≫ (U ◁ stdSimplex.δ 2) ≫ T)
      (SSet.ι₀ ≫ (U ◁ stdSimplex.δ 0) ≫ T) where
  h := (U ◁ stdSimplex.δ 2) ≫ T
  h₀ := rfl
  h₁ := by
    rw [← Category.assoc, familyTriangleCorner_middle, Category.assoc]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 元の合成面を、同じ始点と第二面の終点を持つ実円柱として取り出す。 -/
def familyTriangleDirect {U E : SSet.{u}} (T : U ⊗ (Δ[2] : SSet.{u}) ⟶ E) :
    SSet.Homotopy (SSet.ι₀ ≫ (U ◁ stdSimplex.δ 2) ≫ T)
      (SSet.ι₁ ≫ (U ◁ stdSimplex.δ 0) ≫ T) where
  h := (U ◁ stdSimplex.δ 1) ≫ T
  h₀ := by
    rw [← Category.assoc, familyTriangleCorner_source, Category.assoc]
    rfl
  h₁ := by
    rw [← Category.assoc, familyTriangleCorner_target, Category.assoc]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 全三角形の curry の各面は元の同じ面円柱の curry。 -/
lemma familyTriangleCurry_face {U E : SSet.{u}} (T : U ⊗ (Δ[2] : SSet.{u}) ⟶ E)
    (i : Fin 3) :
    ((ihom U).obj E).δ i (SSet.yonedaEquiv (curry T)) =
      SSet.yonedaEquiv (curry ((U ◁ stdSimplex.δ i) ≫ T)) := by
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← curry_natural_left]

/-- 元の全二単体を保持した、同じ三面の実合成構造。 -/
def familyTriangleCompStruct {U E : SSet.{u}} (T : U ⊗ (Δ[2] : SSet.{u}) ⟶ E) :
    SSet.Edge.CompStruct
      (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (familyTriangleFirst T)))
      (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (familyCylinder ((U ◁ stdSimplex.δ 0) ≫ T))))
      (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (familyTriangleDirect T))) :=
  SSet.Edge.CompStruct.mk (SSet.yonedaEquiv (curry T))
    (familyTriangleCurry_face T 2) (familyTriangleCurry_face T 0) (familyTriangleCurry_face T 1)

/-- 実合成構造を復号すると、入力した元の全三角形を厳密に回収する。 -/
lemma familyTriangleCompStruct_map {U E : SSet.{u}} (T : U ⊗ (Δ[2] : SSet.{u}) ⟶ E) :
    uncurry (SSet.yonedaEquiv.symm (familyTriangleCompStruct T).simplex) = T := by
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry T))) = T
  rw [Equiv.symm_apply_apply, uncurry_curry]

end SerrePositivity.KST.SConstruction
