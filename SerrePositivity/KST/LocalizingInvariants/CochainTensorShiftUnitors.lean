module

public import SerrePositivity.KST.LocalizingInvariants.CochainTensorShiftElements

/-!
概要：tensor–shift 同型と左右の unitor の整合性。
方針：unitor の逆を次数零の単位元で評価し、元の逆三角形へ戻す。
規約：右因子 shift の符号は単位の次数零で恒等となる。使われ方：shift 作用の単位則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R]

lemma tensorLeftUnitor_inv_apply (P : CochainComplex (ModuleCat R) ℤ) (n : ℤ) (x : P.X n) :
    (cochainTensorLeftUnitor P).inv.f n x =
      ιTensorObj cochainTensorUnit P 0 n n (by omega)
        ((singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).inv (1 : R) ⊗ₜ[R] x) := by
  change (HomologicalComplex.leftUnitor' P).inv n x = _
  rw [HomologicalComplex.leftUnitor'_inv]
  rfl

lemma tensorRightUnitor_inv_apply (P : CochainComplex (ModuleCat R) ℤ) (n : ℤ) (x : P.X n) :
    (cochainTensorRightUnitor P).inv.f n x =
      ιTensorObj P cochainTensorUnit n 0 n (by omega)
        (x ⊗ₜ[R] (singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).inv (1 : R)) := by
  change (HomologicalComplex.rightUnitor' P).inv n x = _
  rw [HomologicalComplex.rightUnitor'_inv]
  rfl

lemma tensorShift_leftUnitor (P : CochainComplex (ModuleCat R) ℤ) (s : ℤ) :
    (cochainTensorShiftRight cochainTensorUnit P s).hom ≫
      (cochainTensorLeftUnitor P).hom⟦s⟧' = (cochainTensorLeftUnitor (P⟦s⟧)).hom := by
  apply (cancel_epi (cochainTensorLeftUnitor (P⟦s⟧)).inv).1
  rw [Iso.inv_hom_id]
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (cochainTensorLeftUnitor P).hom.f (n + s)
    ((cochainTensorShiftRight cochainTensorUnit P s).hom.f n
      ((cochainTensorLeftUnitor (P⟦s⟧)).inv.f n x)) = x
  rw [tensorLeftUnitor_inv_apply, tensorShiftRight_apply]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  rw [← tensorLeftUnitor_inv_apply]
  exact congrArg (fun f ↦ f.f (n + s) x) (cochainTensorLeftUnitor P).inv_hom_id

lemma tensorShift_rightUnitor (P : CochainComplex (ModuleCat R) ℤ) (s : ℤ) :
    (cochainTensorShiftLeft P cochainTensorUnit s).hom ≫
      (cochainTensorRightUnitor P).hom⟦s⟧' = (cochainTensorRightUnitor (P⟦s⟧)).hom := by
  apply (cancel_epi (cochainTensorRightUnitor (P⟦s⟧)).inv).1
  rw [Iso.inv_hom_id]
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (cochainTensorRightUnitor P).hom.f (n + s)
    ((cochainTensorShiftLeft P cochainTensorUnit s).hom.f n
      ((cochainTensorRightUnitor (P⟦s⟧)).inv.f n x)) = x
  rw [tensorRightUnitor_inv_apply, tensorShiftLeft_apply]
  rw [← tensorRightUnitor_inv_apply]
  exact congrArg (fun f ↦ f.f (n + s) x) (cochainTensorRightUnitor P).inv_hom_id

end SerrePositivity.KST.LocalizingInvariants
