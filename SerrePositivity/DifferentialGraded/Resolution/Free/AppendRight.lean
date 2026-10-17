module
public import SerrePositivity.DifferentialGraded.Resolution.Free.Units

/-! # 左のpathを固定した全path直和への連結 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]

def appendPath (K : ComplexQuiver A D) {x y : D} (p : PathIndex D x y) (z : D) :
    pathTensor A D K p ⊗ homComplex A D K y z ⟶ homComplex A D K x z :=
  tensorCoproductRightDesc (pathTensor A D K p) (pathTensor A D K (x := y) (y := z))
    (homComplex A D K x z) (pathComposition A D K p)

lemma appendPath_inclusion (K : ComplexQuiver A D) {x y : D}
    (p : PathIndex D x y) (z : D) (q : PathIndex D y z) :
    (pathTensor A D K p ◁ pathInclusion A D K y z q) ≫ appendPath A D K p z =
      pathComposition A D K p q := tensorCoproductRightDesc_ι _ _ _ _ q

lemma composition_left_inclusion (K : ComplexQuiver A D) (x y z : D) (p : PathIndex D x y) :
    (pathInclusion A D K x y p ▷ homComplex A D K y z) ≫ composition A D K x y z =
      appendPath A D K p z := tensorCoproductDesc_left _ _ _ _ p

/-- 固定した非空左pathと全右pathの連結。 -/
abbrev appendWord (K : ComplexQuiver A D) (w : List D) (x y z : D) :
    wordTensor A D K w x y ⊗ homComplex A D K y z ⟶ homComplex A D K x z :=
  appendPath A D K (x := x) (y := y) (.inr w) z

/-- 一辺を全右pathの先頭へ加えるchain map。 -/
abbrev edgePrefix (K : ComplexQuiver A D) (x y z : D) :
    K x y ⊗ homComplex A D K y z ⟶ homComplex A D K x z := appendWord A D K [] x y z

lemma edgePrefix_unit (K : ComplexQuiver A D) (x y : D) :
    (K x y ◁ unitInclusion A D K y) ≫ edgePrefix A D K x y y =
      (ρ_ (K x y)).hom ≫ edgeInclusion A D K x y :=
  appendPath_inclusion A D K (.inr []) y (.inl ⟨rfl⟩)

lemma edgePrefix_nonempty (K : ComplexQuiver A D) (x y z : D) (w : List D) :
    (K x y ◁ pathInclusion A D K y z (.inr w)) ≫ edgePrefix A D K x y z =
      pathInclusion A D K x z (.inr (y :: w)) := by
  have h := appendPath_inclusion A D K (x := x) (y := y) (.inr []) z (.inr w)
  exact h.trans (Category.id_comp _)

lemma appendPath_unit (K : ComplexQuiver A D) (x y : D) :
    appendPath A D K (x := x) (.inl ⟨rfl⟩) y = (λ_ (homComplex A D K x y)).hom := by
  apply (tensorLeftCoproductIsColimit (𝟙_ (Complex A))
    (pathTensor A D K (x := x) (y := y))).hom_ext
  rintro ⟨p⟩
  change (𝟙_ (Complex A) ◁ pathInclusion A D K x y p) ≫ _ = _
  exact (appendPath_inclusion A D K (x := x) (y := x) (.inl ⟨rfl⟩) y p).trans
    (leftUnitor_naturality (pathInclusion A D K x y p)).symm

end SerrePositivity.DifferentialGraded.FreeDGCategory
