module
public import Mathlib.CategoryTheory.Monoidal.Comon_

/-! # 余モノイドの構造同型の元の射
概要：余モノイドの結合・右単位同型を忘却すると、基底の同じ構造射を回収する。
方針：忘却関手の monoidal 性と恒等 tensor 比較を使う。
規約：基底は任意の braided monoidal 圏。使われ方：鎖立方体の元の座標射の照合。
-/
@[expose] public section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable {V : Type u} [Category.{v} V] [MonoidalCategory V] [BraidedCategory V]

/-- 余モノイドの左単位同型の順射は、基底の同じ左単位射。 -/
lemma comonoidLeftUnitorHom (M : Comon V) :
    ((λ_ M).hom).hom = (λ_ M.X).hom := by
  have h := Functor.Monoidal.map_leftUnitor (Comon.forget V) M
  simp only [Comon.forget_δ, Comon.forget_η] at h
  change ((λ_ M).hom).hom = 𝟙 (𝟙_ V ⊗ M.X) ≫
    (𝟙 (𝟙_ V) ▷ M.X) ≫ (λ_ M.X).hom at h
  simpa only [id_whiskerRight, Category.id_comp] using h

/-- 余モノイドの右単位同型の順射は、基底の同じ右単位射。 -/
lemma comonoidRightUnitorHom (M : Comon V) :
    ((ρ_ M).hom).hom = (ρ_ M.X).hom := by
  have h := Functor.Monoidal.map_rightUnitor (Comon.forget V) M
  simp only [Comon.forget_δ, Comon.forget_η] at h
  change ((ρ_ M).hom).hom = 𝟙 (M.X ⊗ 𝟙_ V) ≫
    (M.X ◁ 𝟙 (𝟙_ V)) ≫ (ρ_ M.X).hom at h
  simpa only [whiskerLeft_id, Category.id_comp] using h

/-- 余モノイドの右単位同型の逆射は、基底の同じ右単位射。 -/
lemma comonoidRightUnitorInvHom (M : Comon V) :
    ((ρ_ M).inv).hom = (ρ_ M.X).inv := by
  have h := Functor.Monoidal.map_rightUnitor_inv (Comon.forget V) M
  simp only [Comon.forget_ε, Comon.forget_μ] at h
  change ((ρ_ M).inv).hom = (ρ_ M.X).inv ≫
    (M.X ◁ 𝟙 (𝟙_ V)) ≫ 𝟙 (M.X ⊗ 𝟙_ V) at h
  simpa only [whiskerLeft_id, Category.comp_id] using h

/-- 余モノイドの結合同型の順射は、基底の同じ結合射。 -/
lemma comonoidAssociatorHom (M N P : Comon V) :
    ((α_ M N P).hom).hom = (α_ M.X N.X P.X).hom := by
  have h := Functor.Monoidal.map_associator (Comon.forget V) M N P
  simp only [Comon.forget_δ, Comon.forget_μ] at h
  change ((α_ M N P).hom).hom = 𝟙 ((M.X ⊗ N.X) ⊗ P.X) ≫
    (𝟙 (M.X ⊗ N.X) ▷ P.X) ≫ (α_ M.X N.X P.X).hom ≫
      (M.X ◁ 𝟙 (N.X ⊗ P.X)) ≫ 𝟙 (M.X ⊗ (N.X ⊗ P.X)) at h
  simpa only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id] using h

end SerrePositivity.KST.SConstruction
