module
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses

/-! # 点つき成分の自然性四角形と厳密比較の合成
概要：前向き比較の成分自然性を、同じ厳密自然比較の後合成へ移す。
方針：前後合成で成分の等号を移し、元の厳密四角形を代入する。
規約：Kan 性は不要。使われ方：全 SOA・新 BF 段比較の入力自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra.PointedMapping

/-- 成分で自然な比較と厳密自然な比較の合成も、同じ元の射で成分が自然。 -/
lemma pointedComponentNaturalSquare_post
    {A B A' B' X Y : PointedSimplicialSet.{u}}
    (g : A ⟶ B) (b : A' ⟶ B') (β : A ⟶ A') (β' : B ⟶ B')
    (c : A' ⟶ X) (c' : B' ⟶ Y) (f : X ⟶ Y)
    (hβ : componentOf (β ≫ b) = componentOf (g ≫ β'))
    (hc : b ≫ c' = c ≫ f) :
    componentOf (g ≫ (β' ≫ c')) = componentOf ((β ≫ c) ≫ f) := by
  calc
    componentOf (g ≫ (β' ≫ c')) = componentOf ((β ≫ b) ≫ c') := by
      simpa only [Category.assoc] using (componentOf_comp_right hβ c').symm
    _ = componentOf ((β ≫ c) ≫ f) := by
      rw [Category.assoc, hc, ← Category.assoc]

end SerrePositivity.KST.SConstruction
