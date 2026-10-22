module
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses

/-! # 二つの点つき成分自然性四角形の合成
概要：同じ元の射を保持する二つの成分自然性四角形を合成する。
方針：前後合成で成分の等号を移し、結合律で照合する。
規約：Kan 性は不要。使われ方：旧置換射影と新 BF 比較の入力自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra.PointedMapping

/-- 同じ元の射に関する成分自然性四角形の合成も成分で自然。 -/
lemma pointedComponentSquareComposition
    {A B A' B' X Y : PointedSimplicialSet.{u}}
    (g : A ⟶ B) (b : A' ⟶ B') (β : A ⟶ A') (β' : B ⟶ B')
    (c : A' ⟶ X) (c' : B' ⟶ Y) (f : X ⟶ Y)
    (hβ : componentOf (g ≫ β') = componentOf (β ≫ b))
    (hc : componentOf (b ≫ c') = componentOf (c ≫ f)) :
    componentOf (g ≫ (β' ≫ c')) = componentOf ((β ≫ c) ≫ f) := by
  calc
    componentOf (g ≫ (β' ≫ c')) = componentOf ((β ≫ b) ≫ c') := by
      simpa only [Category.assoc] using componentOf_comp_right hβ c'
    _ = componentOf ((β ≫ c) ≫ f) := by
      simpa only [Category.assoc] using componentOf_comp_left hc β

end SerrePositivity.KST.SConstruction
