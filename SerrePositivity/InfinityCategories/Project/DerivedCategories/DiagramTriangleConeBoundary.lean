module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.TriangleConeOfFace

/-! # 図式二単体と三つの辺錐が指定する三次境界

概要：同じ頂点脚を持つ三つの辺錐と元の図式二単体は、六つの共通辺上で一致する。
方針：零面は図式の自然性、残る三つは単体恒等式と頂点脚の共有を使う。
規約：三次充填は主張しない。使われ方：実 over の三次境界と元の四次外ホーン。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 三次境界を指定する四つの実二単体と、その六つの共通実辺の厳密一致。 -/
structure ThreeSimplexFaceBoundary (X : SSet.{u}) where
  face : Fin 4 → X _⦋2⦌
  h01 : X.δ 0 (face 0) = X.δ 0 (face 1)
  h02 : X.δ 1 (face 0) = X.δ 0 (face 2)
  h03 : X.δ 2 (face 0) = X.δ 0 (face 3)
  h12 : X.δ 1 (face 1) = X.δ 1 (face 2)
  h13 : X.δ 2 (face 1) = X.δ 1 (face 3)
  h23 : X.δ 2 (face 2) = X.δ 2 (face 3)

variable {K : SSet.{u}} {X : SSet.{u}} (f : K ⟶ X) (σ : K _⦋2⦌)
variable (leg : K _⦋0⦌ → X _⦋1⦌) (T : Fin 3 → X _⦋2⦌)

/-- 元の二単体と、同じ頂点脚を共有する三辺の合成二単体を三次境界へ束ねる。 -/
def diagramTriangleConeBoundary
    (h₀ : ∀ i, X.δ 0 (T i) = f.app _ (K.δ i σ))
    (h₁ : ∀ i, X.δ 1 (T i) = leg (K.δ 0 (K.δ i σ)))
    (h₂ : ∀ i, X.δ 2 (T i) = leg (K.δ 1 (K.δ i σ))) :
    ThreeSimplexFaceBoundary X where
  face i := if i = 0 then f.app _ σ else if i = 1 then T 0 else if i = 2 then T 1 else T 2
  h01 := by
    change X.δ 0 (f.app _ σ) = X.δ 0 (T 0)
    exact (ConcreteCategory.congr_hom (f.naturality (SimplexCategory.δ (0 : Fin 3)).op)
      σ).symm.trans (h₀ 0).symm
  h02 := by
    change X.δ 1 (f.app _ σ) = X.δ 0 (T 1)
    exact (ConcreteCategory.congr_hom (f.naturality (SimplexCategory.δ (1 : Fin 3)).op)
      σ).symm.trans (h₀ 1).symm
  h03 := by
    change X.δ 2 (f.app _ σ) = X.δ 0 (T 2)
    exact (ConcreteCategory.congr_hom (f.naturality (SimplexCategory.δ (2 : Fin 3)).op)
      σ).symm.trans (h₀ 2).symm
  h12 := by
    change X.δ 1 (T 0) = X.δ 1 (T 1)
    rw [h₁ 0, h₁ 1]
    exact congrArg leg (ConcreteCategory.congr_hom
      (SimplicialObject.δ_comp_δ K (i := (0 : Fin 2)) (j := (0 : Fin 2))
        (by decide)) σ).symm
  h13 := by
    change X.δ 2 (T 0) = X.δ 1 (T 2)
    rw [h₂ 0, h₁ 2]
    exact congrArg leg (ConcreteCategory.congr_hom
      (SimplicialObject.δ_comp_δ K (i := (0 : Fin 2)) (j := (1 : Fin 2))
        (by decide)) σ).symm
  h23 := by
    change X.δ 2 (T 1) = X.δ 2 (T 2)
    rw [h₂ 1, h₂ 2]
    exact congrArg leg (ConcreteCategory.congr_hom
      (SimplicialObject.δ_comp_δ K (i := (1 : Fin 2)) (j := (1 : Fin 2))
        (by decide)) σ).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
