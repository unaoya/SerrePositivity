module
public import SerrePositivity.DifferentialGraded.Resolution.Free.AppendRight

/-! # 非空左pathの連結を先頭一辺と短いpathへ分解する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]

lemma appendWord_cons (K : ComplexQuiver A D) (b : D) (w : List D) (x y z : D) :
    appendWord A D K (b :: w) x y z =
      (α_ (K x b) (wordTensor A D K w b y) (homComplex A D K y z)).hom ≫
        K x b ◁ appendWord A D K w b y z ≫ edgePrefix A D K x b z := by
  apply (tensorLeftCoproductIsColimit (wordTensor A D K (b :: w) x y)
    (pathTensor A D K (x := y) (y := z))).hom_ext
  rintro ⟨q⟩
  have hl := appendPath_inclusion A D K (x := x) (y := y) (.inr (b :: w)) z q
  have hr := appendPath_inclusion A D K (x := b) (y := y) (.inr w) z q
  refine hl.trans ?_
  change pathComposition A D K (.inr (b :: w)) q =
    (((K x b ⊗ wordTensor A D K w b y) ◁ pathInclusion A D K y z q) ≫
      (α_ (K x b) (wordTensor A D K w b y) (homComplex A D K y z)).hom ≫
        K x b ◁ appendWord A D K w b y z ≫ edgePrefix A D K x b z)
  change (wordTensor A D K w b y ◁ pathInclusion A D K y z q) ≫
    appendWord A D K w b y z = pathComposition A D K (.inr w) q at hr
  rw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc, hr]
  cases q with
  | inl h =>
    rcases h with ⟨h⟩
    subst z
    change (ρ_ (K x b ⊗ wordTensor A D K w b y)).hom ≫
        pathInclusion A D K x y (.inr (b :: w)) =
      (α_ (K x b) (wordTensor A D K w b y) (𝟙_ (Complex A))).hom ≫
        K x b ◁ ((ρ_ (wordTensor A D K w b y)).hom ≫
          pathInclusion A D K b y (.inr w)) ≫ edgePrefix A D K x b y
    rw [whiskerLeft_comp, Category.assoc, edgePrefix_nonempty, rightUnitor_tensor_hom,
      Category.assoc]
  | inr v =>
    change (wordConcatenationIso A D K (b :: w) v x y z).hom ≫
        pathInclusion A D K x z (.inr (b :: concatenate D w v y)) =
      (α_ (K x b) (wordTensor A D K w b y) (wordTensor A D K v y z)).hom ≫
        K x b ◁ ((wordConcatenationIso A D K w v b y z).hom ≫
          pathInclusion A D K b z (.inr (concatenate D w v y))) ≫ edgePrefix A D K x b z
    rw [whiskerLeft_comp, Category.assoc, edgePrefix_nonempty]
    rfl

end SerrePositivity.DifferentialGraded.FreeDGCategory
