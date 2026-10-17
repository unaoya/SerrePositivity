module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonGraded
public import SerrePositivity.DifferentialGraded.Quotient.PrependDifferential

/-! # 長さ filtration と先頭 Hom の全次数作用

word を変えない部分直和への作用と射影の可換式から、最終微分を持つ各段階の安定性を得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
attribute [local instance] Classical.propDecidable

/-- word 条件を保つ先頭 Hom の作用。 -/
def selectedPrepend (S : Set D) (P : Word S → Prop) (x y z : D) :
    homObject A D x y ⊗ selectedHom A D S P y z ⟶ selectedHom A D S P x z :=
  (tensorLeftCoproductIsColimit (homObject A D x y)
    (fun w : {w : Word S // P w} => term A D w.val y z)).desc
      (Cofan.mk _ (fun w => prependMap A D w.val x y z ≫
        Sigma.ι (fun w : {w : Word S // P w} => term A D w.val x z) w))

@[reassoc] lemma selectedPrepend_ι (S : Set D) (P : Word S → Prop) (x y z : D)
    (w : {w : Word S // P w}) :
    (homObject A D x y ◁ Sigma.ι (fun w : {w : Word S // P w} => term A D w.val y z) w) ≫
        selectedPrepend A D S P x y z =
      prependMap A D w.val x y z ≫
        Sigma.ι (fun w : {w : Word S // P w} => term A D w.val x z) w :=
  (tensorLeftCoproductIsColimit (homObject A D x y) _).fac _ ⟨w⟩

/-- 選んだ path の包含は、先頭 Hom の作用と可換。 -/
lemma selectedPrepend_inclusion (S : Set D) (P : Word S → Prop) (x y z : D) :
    selectedPrepend A D S P x y z ≫ selectedInclusion A D S P x z =
      (homObject A D x y ◁ selectedInclusion A D S P y z) ≫ internalPrepend A D S x y z := by
  apply (tensorLeftCoproductIsColimit (homObject A D x y)
    (fun w : {w : Word S // P w} => term A D w.val y z)).hom_ext
  rintro ⟨w⟩
  change (homObject A D x y ◁
      Sigma.ι (fun w : {w : Word S // P w} => term A D w.val y z) w) ≫
      (selectedPrepend A D S P x y z ≫ selectedInclusion A D S P x z) =
    (homObject A D x y ◁
      Sigma.ι (fun w : {w : Word S // P w} => term A D w.val y z) w) ≫
      ((homObject A D x y ◁ selectedInclusion A D S P y z) ≫ internalPrepend A D S x y z)
  rw [← Category.assoc, selectedPrepend_ι, Category.assoc, selected_ι_inclusion,
    ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, selected_ι_inclusion,
    internalPrepend_ι]

/-- 選んだ path への射影も、先頭 Hom の作用と可換。 -/
lemma selectedProjection_prepend (S : Set D) (P : Word S → Prop) (x y z : D) :
    internalPrepend A D S x y z ≫ selectedProjection A D S P x z =
      (homObject A D x y ◁ selectedProjection A D S P y z) ≫ selectedPrepend A D S P x y z := by
  apply (tensorLeftCoproductIsColimit (homObject A D x y)
    (fun w : Word S => term A D w y z)).hom_ext
  rintro ⟨w⟩
  change (homObject A D x y ◁ ι A D S y z w) ≫
      (internalPrepend A D S x y z ≫ selectedProjection A D S P x z) =
    (homObject A D x y ◁ ι A D S y z w) ≫
      ((homObject A D x y ◁ selectedProjection A D S P y z) ≫ selectedPrepend A D S P x y z)
  rw [← Category.assoc, internalPrepend_ι, Category.assoc, ι_selectedProjection,
    ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, ι_selectedProjection]
  by_cases h : P w
  · rw [dite_eq_left h, dite_eq_left h, selectedPrepend_ι]
  · rw [dite_eq_right h, dite_eq_right h, comp_zero,
      MonoidalPreadditive.whiskerLeft_zero, zero_comp]

/-- 長さ cutoff は先頭 Hom の作用と可換である。 -/
lemma lengthCutoff_prepend (S : Set D) (x y z : D) (n : ℕ) :
    internalPrepend A D S x y z ≫ lengthCutoff A D S x z n =
      (homObject A D x y ◁ lengthCutoff A D S y z n) ≫ internalPrepend A D S x y z := by
  simp only [lengthCutoff, ← Category.assoc, selectedProjection_prepend]
  rw [Category.assoc, selectedPrepend_inclusion, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp]

/-- 内部先頭作用は、相手の Hom の長さ上限を保つ。作用する Hom の次数は任意。 -/
lemma internalPrepend_mem_length (S : Set D) (x y z : D) (n : ℕ)
    (p q r : ℤ) (hr : p + q = r) (f : (homObject A D x y).X p)
    (t : (internalHom A D S y z).X q) (ht : t ∈ lengthSubmodule A D S y z n q) :
    (internalPrepend A D S x y z).f r
      (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q r hr (f ⊗ₜ[A] t)) ∈
        lengthSubmodule A D S x z n r := by
  have h := congrArg (fun g => g.f r
    (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q r hr (f ⊗ₜ[A] t)))
    (lengthCutoff_prepend A D S x y z n)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h
  rw [whiskerLeft_apply, lengthCutoff_fixed A D S y z n q t ht] at h
  rw [← h]
  exact lengthCutoff_mem A D S x z n r _

/-- 最終微分についての先頭作用も、全ての斉次次数で長さ上限を保つ。 -/
lemma quotientPrepend_mem_length (S : Set D) (x y z : D) (n : ℕ)
    (p q r : ℤ) (hr : p + q = r) (f : (homObject A D x y).X p)
    (t : (quotientHom A D S y z).X q) (ht : t ∈ lengthSubmodule A D S y z n q) :
    (quotientPrepend A D S x y z).f r
      (ιTensorObj (homObject A D x y) (quotientHom A D S y z) p q r hr (f ⊗ₜ[A] t)) ∈
        lengthSubmodule A D S x z n r := by
  have h := congrArg (fun g => g (f ⊗ₜ[A] t)) (quotientPrepend_ι A D S x y z p q r hr)
  simp only [ModuleCat.comp_apply] at h
  have hm := internalPrepend_mem_length A D S x y z n p q r hr f t ht
  exact (congrArg (fun v => v ∈ lengthSubmodule A D S x z n r) h).mpr hm

end SerrePositivity.DifferentialGraded.DGQuotient
