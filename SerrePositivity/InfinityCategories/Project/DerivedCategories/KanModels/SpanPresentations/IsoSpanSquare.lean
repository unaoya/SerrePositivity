module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.FunctorIsoWhiskerSpan
/-!
概要：二つの実 span 正方形を同じ比較の差へ移す。
方針：既存の同じ射の作用・比較の逆・合成則を使う。
規約：指定比較の値を保持する。使われ方：実 diagonal span の tensor 像。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory
lemma iso_span_square {C : Type u} [Category.{v} C]
    {A0 A1 A2 B0 B1 B2 : C}
    (a0 : A2 ≅ A0) (a1 : A2 ≅ A1) (b0 : B2 ≅ B0) (b1 : B2 ≅ B1)
    (k0 : A0 ≅ B0) (k1 : A1 ≅ B1) (k2 : A2 ≅ B2)
    (h0 : k2 ≪≫ b0 = a0 ≪≫ k0) (h1 : k2 ≪≫ b1 = a1 ≪≫ k1) :
    k0 ≪≫ b0.symm ≪≫ b1 = a0.symm ≪≫ a1 ≪≫ k1 := by
  calc
    _ = a0.symm ≪≫ (a0 ≪≫ k0) ≪≫ b0.symm ≪≫ b1 := by
      simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
    _ = a0.symm ≪≫ (k2 ≪≫ b0) ≪≫ b0.symm ≪≫ b1 := by rw [h0]
    _ = a0.symm ≪≫ (k2 ≪≫ b1) := by
      simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]
    _ = _ := by rw [h1]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
