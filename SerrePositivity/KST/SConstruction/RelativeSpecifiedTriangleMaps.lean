module
public import SerrePositivity.KST.SConstruction.RelativeSpecifiedTriangleFamilies

/-! # 指定した実二単体族からの全三辺固定延長
概要：既存の部分パラメータの実二単体族と三円柱の面条件から、全体の族を構成する。
方針：curry で全三辺の境界データへ移し、指定全三角形の持ち上げを使う。
規約：部分族の全二単体と全体の元の三円柱を全時刻で回収する。
使われ方：元の K 比較三角形の指定頂点から、全精密化上の比較へ移る。
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
variable {T U E : SSet.{u}} (j : T ⟶ U) {F G H : U ⟶ E}
  (a : SSet.Homotopy F G) (b : SSet.Homotopy G H) (c : SSet.Homotopy F H)
  (t : T ⊗ (Δ[2] : SSet.{u}) ⟶ E)
  (ht₂ : (T ◁ stdSimplex.δ 2) ≫ t = (j ▷ (Δ[1] : SSet.{u})) ≫ a.h)
  (ht₀ : (T ◁ stdSimplex.δ 0) ≫ t = (j ▷ (Δ[1] : SSet.{u})) ≫ b.h)
  (ht₁ : (T ◁ stdSimplex.δ 1) ≫ t = (j ▷ (Δ[1] : SSet.{u})) ≫ c.h)

/-- 元の部分二単体族は、内部 Hom の元の三つの制限辺の実合成構造を与える。 -/
def specifiedTriangleFamilyBoundaryData : SSet.Edge.CompStruct
    ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a)).map ((pre j).app E))
    ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b)).map ((pre j).app E))
    ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy c)).map ((pre j).app E)) := by
  refine SSet.Edge.CompStruct.mk (SSet.yonedaEquiv (curry t)) ?_ ?_ ?_
  · change ((ihom T).obj E).δ 2 (SSet.yonedaEquiv (curry t)) =
      ((pre j).app E).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry a.h))
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← SSet.yonedaEquiv_comp]
    apply congrArg SSet.yonedaEquiv
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_pre_app, uncurry_curry]
    exact ht₂
  · change ((ihom T).obj E).δ 0 (SSet.yonedaEquiv (curry t)) =
      ((pre j).app E).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry b.h))
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← SSet.yonedaEquiv_comp]
    apply congrArg SSet.yonedaEquiv
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_pre_app, uncurry_curry]
    exact ht₀
  · change ((ihom T).obj E).δ 1 (SSet.yonedaEquiv (curry t)) =
      ((pre j).app E).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry c.h))
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← SSet.yonedaEquiv_comp]
    apply congrArg SSet.yonedaEquiv
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_pre_app, uncurry_curry]
    exact ht₁

/-- 指定した部分族と、元の全三円柱を同時に保つ全二単体族。 -/
def relativeSpecifiedTriangleMap [KanComplex E] (hj : anodyneExtensions j) :
    U ⊗ (Δ[2] : SSet.{u}) ⟶ E :=
  relativeSpecifiedTriangleFamily j hj a b c
    (specifiedTriangleFamilyBoundaryData j a b c t ht₂ ht₀ ht₁)

/-- 元の部分パラメータ上の全二単体族を厳密に回収する。 -/
lemma relativeSpecifiedTriangleMap_boundary [KanComplex E] (hj : anodyneExtensions j) :
    (j ▷ (Δ[2] : SSet.{u})) ≫ relativeSpecifiedTriangleMap j a b c t ht₂ ht₀ ht₁ hj = t := by
  rw [relativeSpecifiedTriangleMap, relativeSpecifiedTriangleFamily_boundary]
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry t))) = _
  rw [Equiv.symm_apply_apply, uncurry_curry]

/-- 全体の 01 面は元の第一円柱。 -/
lemma relativeSpecifiedTriangleMap_first [KanComplex E] (hj : anodyneExtensions j) :
    (U ◁ stdSimplex.δ 2) ≫ relativeSpecifiedTriangleMap j a b c t ht₂ ht₀ ht₁ hj = a.h :=
  relativeSpecifiedTriangleFamily_first _ _ _ _ _ _

/-- 全体の 12 面は元の第二円柱。 -/
lemma relativeSpecifiedTriangleMap_second [KanComplex E] (hj : anodyneExtensions j) :
    (U ◁ stdSimplex.δ 0) ≫ relativeSpecifiedTriangleMap j a b c t ht₂ ht₀ ht₁ hj = b.h :=
  relativeSpecifiedTriangleFamily_second _ _ _ _ _ _

/-- 全体の 02 面も元の合成円柱を変更しない。 -/
lemma relativeSpecifiedTriangleMap_composite [KanComplex E] (hj : anodyneExtensions j) :
    (U ◁ stdSimplex.δ 1) ≫ relativeSpecifiedTriangleMap j a b c t ht₂ ht₀ ht₁ hj = c.h :=
  relativeSpecifiedTriangleFamily_composite _ _ _ _ _ _

end SerrePositivity.KST.SConstruction
