module
public import SerrePositivity.KST.SConstruction.RawBoundaryEdgeCases

/-! # 元の境界商の基本亜群の唯一の対象での道の計算
概要：基本亜群の全ての射を、元の境界商の同じ基点の自己射として扱う。
方針：頂点の一意性から対象の一意性を得て、等号射による端点の輸送を計算する。
規約：新しい対象や道を選ばない。使われ方：辺・逆・合成の帰納法による K 類の生成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 対象が一つの圏の射を、指定した対象の自己射へ等号射で輸送する。 -/
def singletonCategoryHom {C : Type u} [Category.{v} C] [Subsingleton C]
    (b : C) {x y : C} (f : x ⟶ y) : b ⟶ b :=
  eqToHom (Subsingleton.elim b x) ≫ f ≫ eqToHom (Subsingleton.elim y b)

/-- 同じ対象の自己射の輸送は元の射に等しい。 -/
lemma singletonCategoryHom_self {C : Type u} [Category.{v} C] [Subsingleton C]
    (b : C) (f : b ⟶ b) : singletonCategoryHom b f = f := by
  simp only [singletonCategoryHom, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 一意な対象への輸送は合成を保つ。 -/
lemma singletonCategoryHom_comp {C : Type u} [Category.{v} C] [Subsingleton C]
    (b : C) {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    singletonCategoryHom b (f ≫ g) = singletonCategoryHom b f ≫ singletonCategoryHom b g := by
  have hx : x = b := Subsingleton.elim _ _
  have hy : y = b := Subsingleton.elim _ _
  have hz : z = b := Subsingleton.elim _ _
  subst x y z
  rw [singletonCategoryHom_self, singletonCategoryHom_self, singletonCategoryHom_self]

/-- 一意な対象への輸送は亜群の逆射を保つ。 -/
lemma singletonCategoryHom_inv {C : Type u} [Category.{v} C] [IsGroupoid C] [Subsingleton C]
    (b : C) {x y : C} (f : x ⟶ y) :
    singletonCategoryHom b (inv f) = inv (singletonCategoryHom b f) := by
  have hx : x = b := Subsingleton.elim _ _
  have hy : y = b := Subsingleton.elim _ _
  subst x y
  rw [singletonCategoryHom_self, singletonCategoryHom_self]

/-- 元の境界商の基本亜群の全ての対象は元の基点と等しい。 -/
lemma boundaryFundamentalGroupoid_obj_eq (X : StableModel.{u})
    (a : boundaryFundamentalGroupoid X) : a = boundaryFundamentalBasepoint X := by
  obtain ⟨b, rfl⟩ := FreeGroupoid.of_obj_bijective.surjective a
  obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective b
  exact congrArg (fun x => FreeGroupoid.mk (SSet.HomotopyCategory.mk x))
    (boundaryReducedRealization_vertex_eq X x)

/-- 元の境界商の基本亜群には対象が一つだけある。 -/
instance boundaryFundamentalGroupoid_subsingleton (X : StableModel.{u}) :
    Subsingleton (boundaryFundamentalGroupoid X) where
  allEq a b := (boundaryFundamentalGroupoid_obj_eq X a).trans
    (boundaryFundamentalGroupoid_obj_eq X b).symm

/-- 任意の元の辺の射を基点へ輸送すると、同じ元の辺の基点の道を回収する。 -/
lemma singletonCategoryHom_boundary_edge (X : StableModel.{u})
    {x y : (boundaryReducedRealization 0 X).right _⦋0⦌}
    (e : (boundaryReducedRealization 0 X).right.Edge x y) :
    singletonCategoryHom (boundaryFundamentalBasepoint X)
      (FreeGroupoid.homMk (SSet.HomotopyCategory.homMk e)) = rawBoundaryPath X e.edge := by
  have hx := boundaryReducedRealization_vertex_eq X x
  have hy := boundaryReducedRealization_vertex_eq X y
  subst x y
  have he : e.toTruncated = fundamentalLoopEdge (rawBoundaryLoopSimplex X e.edge) := by
    apply SSet.Truncated.Edge.ext
    exact (SSet.yonedaEquiv.apply_symm_apply e.edge).symm
  rw [singletonCategoryHom_self]
  exact congrArg (fun e => FreeGroupoid.homMk (SSet.Truncated.HomotopyCategory.homMk e)) he

end SerrePositivity.KST.SConstruction
