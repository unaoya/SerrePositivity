module

public import SerrePositivity.EInfinity.BarrattEccles.MappingSpacePiZero

/-!
# 元の E 代数射の導来写像空間の連結成分

概要：Hovey §5 の Map^h の π₀ に元の代数射を送り、局所化で同じ射になることを証明する。
方針：始域 frame の零次比較と終域の fibrant 比較で元の射を挟む。
規約：実際の零単体の類を使い、Hom の同値だけから任意の逆像を選ばない。
使われ方：E2a-5 の比較の計算則と元の代数射の解釈。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

variable (A : Type u) [CommRing A]

attribute [local implicit_reducible] CofibrantResolutionFamily.atObject
attribute [local irreducible] mappingCofibrantFactorization mappingFibrantFactorization

/-- 概要：元の E 代数射を導来写像空間の連結成分へ送る（Hovey §5）。
方針：frame の零次 augmentation と fibrant 比較を元の射へ合成する。
規約：元の射に対応する具体的な零単体の類。
使われ方：Ho(Alg_E) の元の射の π₀ での表示。 -/
def mappingSpaceClass {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    SSet.π₀ (((mappingSpace A).obj (op X)).obj Y) := by
  let := modelCategory A
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  let r := mappingFibrantFactorization A
  exact SSet.π₀.mk ((q.augmentation.app X).app (SimplexCategory.mk 0) ≫
    f ≫ (fibrantTargetComparison r).app Y)

/-- 概要：元の射の π₀ の類は局所化で同じ射になる（Hovey §5）。
方針：零単体の比較公式で frame と fibrant 比較の逆を相殺する。
規約：任意の普通の局所化と具体的な E 代数モデル。
使われ方：Map^h の π₀ と Ho(Alg_E) の Hom の比較の正規化。 -/
lemma mappingSpacePiZeroEquiv_class
    {H : Type w} [Category.{v} H] (L : (operad A).Algebra ⥤ H)
    {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    let := modelCategory A
    ∀ [L.IsLocalization (weakEquivalences (operad A).Algebra)],
      mappingSpacePiZeroEquiv A L (op X) Y (mappingSpaceClass A f) = L.map f := by
  let := modelCategory A
  dsimp only
  intro hL
  have := hL
  let c := mappingCofibrantFactorization A
  let r := mappingFibrantFactorization A
  let q := cosimplicialResolutionFamily c
  change chosenResolutionHomPiZeroEquiv L c r (op X) Y
    (SSet.π₀.mk ((q.augmentation.app X).app (SimplexCategory.mk 0) ≫
      f ≫ (fibrantTargetComparison r).app Y)) = L.map f
  rw [chosenResolutionHomPiZeroEquiv_mk, L.map_comp, L.map_comp]
  let e₀ := resolutionZeroLocalizationIso L (q.atObject X)
  let e₁ := fibrantTargetLocalizationIso L r Y
  change e₀.inv ≫ (e₀.hom ≫ (L.map f ≫ e₁.hom)) ≫ e₁.inv = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.EInfinity.BarrattEccles
