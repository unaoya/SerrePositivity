module
public import SerrePositivity.DifferentialGraded.Quotient.EpsilonElement
public import SerrePositivity.DifferentialGraded.Quotient.Category

/-! # 指定ε生成元の収縮方程式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma eraseFirst_epsilonTerm {S : Set D} (b : S) :
    (eraseFirst A D b [] b.val b.val).v (-1) 0 (by omega)
      ((epsilonTerm A D b).f (-1)
        ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))) =
    (unitElement A b.val).val := by
  change ((eraseMiddle A (homObject A D b.val b.val) (homObject A D b.val b.val)).comp
    (Cochain.ofHom (eComp (Complex A) b.val b.val b.val)) (add_zero 1)).v (-1) 0 (by omega)
      ((epsilonTerm A D b).f (-1)
        ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))) = _
  rw [epsilonTerm_generator, cochain_comp_ofHom_apply, eraseMiddle_generator]
  simp only [Int.negOnePow_zero, one_smul]
  exact forward_unit A (unitElement A b.val).val

variable [Small.{u} D]

lemma erasure_epsilonElement (S : Set D) (b : S) :
    (erasure A D S b.val b.val).v (-1) 0 (by omega) (epsilonElement A D S b) =
      (originalHom A D S b.val b.val).f 0 (unitElement A b.val).val := by
  have h := congrArg (fun f : Cochain (term A D [b] b.val b.val)
      (internalHom A D S b.val b.val) 1 =>
      f.v (-1) 0 (by omega) ((epsilonTerm A D b).f (-1)
        ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))))
    (erasure_precomp A D S b.val b.val [b])
  rw [eraseRow_singleton, cochain_ofHom_comp_apply, cochain_comp_ofHom_apply,
    eraseFirst_epsilonTerm] at h
  exact h

lemma internal_d_epsilonElement (S : Set D) (b : S) :
    (internalHom A D S b.val b.val).d (-1) 0 (epsilonElement A D S b) = 0 :=
  (complexSphereCycle A (-1) (epsilon A D S b)).property

/-- 最終dg商における指定収縮の方程式dε_b=id_b。 -/
lemma differential_epsilonElement (S : Set D) (b : S) :
    (quotientHom A D S b.val b.val).d (-1) 0 (epsilonElement A D S b) =
      (unitElement A (⟨b.val⟩ : QuotientObject D S)).val := by
  rw [show (quotientHom A D S b.val b.val).d (-1) 0 =
      (internalHom A D S b.val b.val).d (-1) 0 +
        (erasure A D S b.val b.val).v (-1) 0 (by omega) from
      quotientHom_d A D S b.val b.val (-1)]
  change (internalHom A D S b.val b.val).d (-1) 0 (epsilonElement A D S b) +
    (erasure A D S b.val b.val).v (-1) 0 (by omega) (epsilonElement A D S b) = _
  rw [internal_d_epsilonElement, zero_add, erasure_epsilonElement]
  rfl

end SerrePositivity.DifferentialGraded.DGQuotient
