module
public import SerrePositivity.KST.SConstruction.MultiSExactEnrichedFunctor

/-! # 元の全方向の多単体制限を持つ完全射
概要：元の有限反復 S の全方向の面退化を、同じ実完全射として保持する。
方針：既存の多単体自己関手の同じ成分と保存条件を使う。
規約：独立な全方向を同時に動かす。使われ方：全高次比較の実多単体図式。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

/-- 元の多単体図式の全方向の添字制限を、同じ実完全射として保持する。 -/
def multiSExactRestriction (r : ℕ) {d e : Fin r → SimplexCategoryᵒᵖ}
    (θ : d ⟶ e) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (multiSExactCategory r d C) (multiSExactCategory r e C) := by
  let f := ((multiSEndofunctor r).map θ).app (stableCategoryModel C)
  exact ⟨f.val, ⟨f.property.1, fun t ht => f.property.2 t ht⟩⟩

/-- 恒等の全方向制限は、元の同じ反復値の恒等完全射。 -/
lemma multiSExactRestriction_id (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ)
    (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) : multiSExactRestriction r (𝟙 d) C =
      𝟙 (multiSExactCategory r d C) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext
  exact congrArg (fun η => (η.app (stableCategoryModel C)).val)
    ((multiSEndofunctor r).map_id d)

/-- 全方向の制限の合成は、元の同じ多単体図式の厳密な合成。 -/
lemma multiSExactRestriction_comp (r : ℕ) {d e f : Fin r → SimplexCategoryᵒᵖ}
    (θ : d ⟶ e) (φ : e ⟶ f) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    multiSExactRestriction r (θ ≫ φ) C =
      (show multiSExactCategory r d C ⟶ multiSExactCategory r e C from
        multiSExactRestriction r θ C) ≫ multiSExactRestriction r φ C := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext
  exact congrArg (fun η => (η.app (stableCategoryModel C)).val)
    ((multiSEndofunctor r).map_comp θ φ)

/-- 元の全方向制限は、先頭の制限と残りの制限の S_n 像に厳密に分解する。 -/
lemma multiSExactRestriction_succ (r : ℕ) {d e : Fin (r + 1) → SimplexCategoryᵒᵖ}
    (θ : d ⟶ e) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    (multiSExactRestriction (r + 1) θ C).hom =
      (sExactRestriction (θ 0).unop.toOrderHom
        (multiSExactCategory r (fun i => d i.succ) C)).hom ≫
      (sExactMap (e 0).unop.len
        (multiSExactRestriction r (fun i => θ i.succ) C)).hom := rfl

end SerrePositivity.KST.SConstruction
