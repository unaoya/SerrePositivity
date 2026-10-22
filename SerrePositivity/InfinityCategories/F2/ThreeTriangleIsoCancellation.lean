module

public import SerrePositivity.InfinityCategories.F2.FunctorTetrahedronEdgeComparisonSquare

/-!
概要：同じ三つの指定合成関係から、二内部面を消去して外側の指定比較の式を得る。
方針：共有する内部同型を指定された逆で相殺する。
規約：同型の値を選び直さない。使われ方：単位三角柱全体の指定 path の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
namespace SerrePositivity.InfinityCategories.F2

/-- 三つの元の指定関係から二内部面を消去した、外側の指定同型の厳密な等式。 -/
lemma threeTriangleIso_cancel {C : Type u} [Category.{v} C]
    {s x y z₀ z₁ z₂ z₃ z₄ : C}
    (ld : s ≅ z₀) (ud : s ≅ z₃) (c : z₀ ≅ z₁) (t : z₃ ≅ z₄)
    (a : s ≅ x) (b : s ≅ y) (ll : y ≅ z₁) (ul : y ≅ z₂)
    (lr : x ≅ z₂) (ur : x ≅ z₄)
    (h₁ : ld ≪≫ c = b ≪≫ ll) (h₂ : a ≪≫ lr = b ≪≫ ul)
    (h₃ : a ≪≫ ur = ud ≪≫ t) :
    (ld.symm ≪≫ ud) ≪≫ t = c ≪≫ (ll.symm ≪≫ ul) ≪≫ (lr.symm ≪≫ ur) := by
  have hb : b = ld ≪≫ c ≪≫ ll.symm := by
    apply Iso.ext
    have h := congrArg (fun f => f ≫ ll.inv) (congrArg Iso.hom h₁)
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] using h.symm
  have ha : a = b ≪≫ ul ≪≫ lr.symm := by
    apply Iso.ext
    have h := congrArg (fun f => f ≫ lr.inv) (congrArg Iso.hom h₂)
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] using h
  calc
    (ld.symm ≪≫ ud) ≪≫ t = ld.symm ≪≫ (ud ≪≫ t) := Iso.trans_assoc _ _ _
    _ = ld.symm ≪≫ (a ≪≫ ur) := by rw [← h₃]
    _ = _ := by
      rw [ha, hb]
      apply Iso.ext
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.F2
