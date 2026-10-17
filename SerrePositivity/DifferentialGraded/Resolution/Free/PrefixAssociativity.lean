module
public import SerrePositivity.DifferentialGraded.Resolution.Free.AppendRecursion
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproductExt

/-! # 一辺の先頭作用と任意path連結の整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]

lemma appendPath_edgePrefix (K : ComplexQuiver A D) (x b y z : D)
    (p : PathIndex D b y) :
    (((K x b ◁ pathInclusion A D K b y p) ≫ edgePrefix A D K x b y) ▷
        homComplex A D K y z) ≫ composition A D K x y z =
      (α_ (K x b) (pathTensor A D K p) (homComplex A D K y z)).hom ≫
        K x b ◁ appendPath A D K p z ≫ edgePrefix A D K x b z := by
  cases p with
  | inl h =>
    rcases h with ⟨h⟩
    subst y
    change (((K x b ◁ unitInclusion A D K b) ≫ edgePrefix A D K x b b) ▷
        homComplex A D K b z) ≫ composition A D K x b z = _
    have hc := composition_left_inclusion A D K x b z (.inr [])
    change (edgeInclusion A D K x b ▷ homComplex A D K b z) ≫ composition A D K x b z =
      edgePrefix A D K x b z at hc
    rw [edgePrefix_unit, comp_whiskerRight, Category.assoc, hc, appendPath_unit]
    exact congrArg (fun k => k ≫ edgePrefix A D K x b z)
      (MonoidalCategory.triangle (K x b) (homComplex A D K b z)).symm
  | inr w =>
    rw [edgePrefix_nonempty, composition_left_inclusion]
    exact appendWord_cons A D K b w x y z

lemma composition_edgePrefix (K : ComplexQuiver A D) (x b y z : D) :
    (edgePrefix A D K x b y ▷ homComplex A D K y z) ≫ composition A D K x y z =
      (α_ (K x b) (homComplex A D K b y) (homComplex A D K y z)).hom ≫
        K x b ◁ composition A D K b y z ≫ edgePrefix A D K x b z := by
  apply tensorLeftRightCoproduct_hom_ext (K x b) (homComplex A D K y z)
    (pathTensor A D K (x := b) (y := y))
  intro p
  change (((K x b ◁ pathInclusion A D K b y p) ▷ homComplex A D K y z) ≫
      (edgePrefix A D K x b y ▷ homComplex A D K y z)) ≫ composition A D K x y z = _
  rw [← comp_whiskerRight, appendPath_edgePrefix]
  symm
  have hc := composition_left_inclusion A D K b y z p
  change (Sigma.ι (pathTensor A D K (x := b) (y := y)) p ▷ homComplex A D K y z) ≫
    composition A D K b y z = appendPath A D K p z at hc
  rw [associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc, hc]

end SerrePositivity.DifferentialGraded.FreeDGCategory
