module
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-! # 余積余錐の源を同型で移した普遍性
概要：二つの源の同型で前合成しても、同じ余錐頂点が余積の普遍性を持つ。
方針：元の余積降下へ逆同型を前合成し、両包含で一意性を検出する。
規約：任意の通常圏。使われ方：自由点つき境界を smash の単位からの両端和へ移す。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits
variable {C : Type u} [Category.{v} C]

/-- 元の同じ余積余錐の源だけを同型で移す。 -/
def binaryCofanSourceIsos {X Y X' Y' P : C} {l : X ⟶ P} {r : Y ⟶ P}
    (h : IsColimit (BinaryCofan.mk l r)) (e : X' ≅ X) (d : Y' ≅ Y) :
    IsColimit (BinaryCofan.mk (e.hom ≫ l) (d.hom ≫ r)) := by
  refine BinaryCofan.IsColimit.mk (BinaryCofan.mk (e.hom ≫ l) (d.hom ≫ r))
    (fun {T} (a : X' ⟶ T) (b : Y' ⟶ T) =>
      BinaryCofan.IsColimit.desc (s := BinaryCofan.mk l r) h (e.inv ≫ a) (d.inv ≫ b)) ?_ ?_ ?_
  · intro T a b
    have hf : l ≫ BinaryCofan.IsColimit.desc (s := BinaryCofan.mk l r) h
        (e.inv ≫ a) (d.inv ≫ b) = e.inv ≫ a :=
      BinaryCofan.IsColimit.inl_desc h _ _
    change (e.hom ≫ l) ≫ _ = a
    rw [Category.assoc, hf, ← Category.assoc, e.hom_inv_id, Category.id_comp]
  · intro T a b
    have hf : r ≫ BinaryCofan.IsColimit.desc (s := BinaryCofan.mk l r) h
        (e.inv ≫ a) (d.inv ≫ b) = d.inv ≫ b :=
      BinaryCofan.IsColimit.inr_desc h _ _
    change (d.hom ≫ r) ≫ _ = b
    rw [Category.assoc, hf, ← Category.assoc, d.hom_inv_id, Category.id_comp]
  · intro T a b m ha hb
    change (e.hom ≫ l) ≫ m = a at ha
    change (d.hom ≫ r) ≫ m = b at hb
    apply BinaryCofan.IsColimit.hom_ext (s := BinaryCofan.mk l r) h
    · have hf : l ≫ BinaryCofan.IsColimit.desc (s := BinaryCofan.mk l r) h
          (e.inv ≫ a) (d.inv ≫ b) = e.inv ≫ a :=
        BinaryCofan.IsColimit.inl_desc h _ _
      change l ≫ m = l ≫ _
      rw [hf, ← ha]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    · have hf : r ≫ BinaryCofan.IsColimit.desc (s := BinaryCofan.mk l r) h
          (e.inv ≫ a) (d.inv ≫ b) = d.inv ≫ b :=
        BinaryCofan.IsColimit.inr_desc h _ _
      change r ≫ m = r ≫ _
      rw [hf, ← hb]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]

end SerrePositivity.KST.SConstruction
