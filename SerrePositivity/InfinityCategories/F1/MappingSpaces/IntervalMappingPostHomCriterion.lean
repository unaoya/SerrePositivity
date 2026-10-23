module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostIso
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.RightIntervalEquivalence

/-!
概要：端点を正規化した実際の区間作用の同値性を、同じ写像の pinched Hom 作用へ戻す。
方針：二つの模型の後合成の自然性を全単体で証明し、既存の模型比較の同値を消去する。
規約：端点の厳密な等式による輸送を省略しない。
使われ方：共同実現の実際の写像空間作用の充満忠実性の判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- pinched 模型と区間模型の実際の後合成は、指定した端点の正規化を含めて厳密に可換。 -/
lemma pinchedHomToIntervalMappingSpace_postOfEq {X Y : SSet.{u}} (f : X ⟶ Y)
    (x y : X _⦋0⦌) {x' y' : Y _⦋0⦌} (hx : f.app _ x = x') (hy : f.app _ y = y') :
    (pinchedHomMap f x y ≫ eqToHom (congrArg₂ (fun a b => pinchedHom a b) hx hy)) ≫
      pinchedHomToIntervalMappingSpace x' y' =
    pinchedHomToIntervalMappingSpace x y ≫ intervalMappingPostOfEq f x y hx hy := by
  subst x'
  subst y'
  simp only [eqToHom_refl, Category.comp_id]
  apply intervalMappingUncurry_injective _ _
  rw [pinchedHomToIntervalMappingSpace_uncurry, intervalMappingPostOfEq_uncurry]
  have hu := pinchedHomToIntervalMappingSpace_uncurry (𝟙 (pinchedHom x y))
  have hp := pinchedHomUncurry_postcomp (𝟙 (pinchedHom x y)) f
  simp only [Category.id_comp] at hu hp
  rw [hu, hp, Category.assoc]

/-- 正規化した実際の区間作用の同値性から、同じ写像の pinched Hom 作用の同値性が従う。 -/
lemma pinchedHomMap_isQCatEquivalence_of_intervalPost
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y)
    (x y : X _⦋0⦌) {x' y' : Y _⦋0⦌} (hx : f.app _ x = x') (hy : f.app _ y = y')
    (h : IsQCatEquivalence
      (pinchedHomToIntervalMappingSpace x y ≫ intervalMappingPostOfEq f x y hx hy)) :
    IsQCatEquivalence (pinchedHomMap f x y) := by
  have hh : IsQCatEquivalence
      ((pinchedHomMap f x y ≫ eqToHom (congrArg₂ (fun a b => pinchedHom a b) hx hy)) ≫
        pinchedHomToIntervalMappingSpace x' y') := by
    rw [pinchedHomToIntervalMappingSpace_postOfEq]
    exact h
  have hm := (pinchedHomToIntervalMappingSpace_isQCatEquivalence x' y').cancel_right hh
  exact (qCatEquivalenceOfIso (eqToIso
    (congrArg₂ (fun a b => pinchedHom a b) hx hy))).isQCatEquivalence.cancel_right hm

end SerrePositivity.InfinityCategories
