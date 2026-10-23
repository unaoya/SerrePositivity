module

public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
概要：同じ dg 圏の閉零射による全 Hom 前後合成の加法性。
方針：閉射を単位からの chain map として読み、複体の tensor の加法性を使う。
規約：全次数の chain map の等式。使われ方：実直和の射影と分裂関係。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalPreadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] {C : Type v} [DGCategory R C]

/-- 閉零射の後合成は全 Hom 複体上の零 chain map。 -/
lemma dgClosedHomPost_zero (X Y Z : ClosedCategory R C) :
    eHomWhiskerLeft (Complex R) X (0 : Y ⟶ Z) = 0 := by
  unfold eHomWhiskerLeft
  change _ ≫ _ ◁ (0 : 𝟙_ (Complex R) ⟶ _) ≫ _ = 0
  simp only [whiskerLeft_zero, zero_comp, comp_zero]

/-- 閉零射の前合成も全 Hom 複体上の零 chain map。 -/
lemma dgClosedHomPre_zero (X Y Z : ClosedCategory R C) :
    eHomWhiskerRight (Complex R) (0 : X ⟶ Y) Z = 0 := by
  unfold eHomWhiskerRight
  change _ ≫ (0 : 𝟙_ (Complex R) ⟶ _) ▷ _ ≫ _ = 0
  simp only [zero_whiskerRight, zero_comp, comp_zero]

/-- 閉射の和の後合成は同じ二つの全 Hom chain map の和。 -/
lemma dgClosedHomPost_add (X Y Z : ClosedCategory R C) (f g : Y ⟶ Z) :
    eHomWhiskerLeft (Complex R) X (f + g) =
      eHomWhiskerLeft (Complex R) X f + eHomWhiskerLeft (Complex R) X g := by
  unfold eHomWhiskerLeft
  change _ ≫ _ ◁ (ForgetEnrichment.homTo (Complex R) f +
    ForgetEnrichment.homTo (Complex R) g) ≫ _ =
      (ρ_ (X ⟶[Complex R] Y)).inv ≫ _ ◁ ForgetEnrichment.homTo (Complex R) f ≫
        eComp (Complex R) X Y Z +
      (ρ_ (X ⟶[Complex R] Y)).inv ≫ _ ◁ ForgetEnrichment.homTo (Complex R) g ≫
        eComp (Complex R) X Y Z
  simp only [whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add]

/-- 閉射の和の前合成も同じ二つの全 Hom chain map の和。 -/
lemma dgClosedHomPre_add (X Y Z : ClosedCategory R C) (f g : X ⟶ Y) :
    eHomWhiskerRight (Complex R) (f + g) Z =
      eHomWhiskerRight (Complex R) f Z + eHomWhiskerRight (Complex R) g Z := by
  unfold eHomWhiskerRight
  change _ ≫ (ForgetEnrichment.homTo (Complex R) f +
    ForgetEnrichment.homTo (Complex R) g) ▷ _ ≫ _ =
      (λ_ (Y ⟶[Complex R] Z)).inv ≫ ForgetEnrichment.homTo (Complex R) f ▷ _ ≫
        eComp (Complex R) X Y Z +
      (λ_ (Y ⟶[Complex R] Z)).inv ≫ ForgetEnrichment.homTo (Complex R) g ▷ _ ≫
        eComp (Complex R) X Y Z
  simp only [add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]

end SerrePositivity.KST.NonConnective
