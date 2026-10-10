module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import SerrePositivity.CategoryTheory.CommShiftOfPrecomp

/-! # 対象を零に送る三角関手の Verdier 商への降下 -/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (P : ObjectProperty C) (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
  (hF : ∀ X, P X → IsZero (F.obj X))

include hF in
lemma triangulated_inverts_of_kills : P.trW.IsInvertedBy F := by
  intro X Y f hf
  obtain ⟨Z, g, h, hT, hZ⟩ := hf
  exact (Triangle.isZero₃_iff_isIso₁ _ (F.map_distinguished _ hT)).mp (hF Z hZ)

variable [IsTriangulated C] [P.IsTriangulated]

/-- 部分圏の対象は Verdier 商で零になる。 -/
lemma verdierQuotient_isZero (X : C) (hX : P X) : IsZero (P.trW.Q.obj X) := by
  have hf : P.trW (0 : (0 : C) ⟶ X) :=
    ⟨X, 𝟙 X, 0, contractible_distinguished₁ X, hX⟩
  have := Localization.inverts P.trW.Q P.trW _ hf
  exact IsZero.of_iso (P.trW.Q.map_isZero (isZero_zero C))
    (asIso (P.trW.Q.map (0 : (0 : C) ⟶ X))).symm

@[implicit_reducible]
noncomputable def verdierLift : P.trW.Localization ⥤ D :=
  Localization.lift F (triangulated_inverts_of_kills P F hF) P.trW.Q

noncomputable def verdierLiftFactors : P.trW.Q ⋙ verdierLift P F hF ≅ F :=
  Localization.fac F (triangulated_inverts_of_kills P F hF) P.trW.Q

noncomputable instance verdierLift_lifting :
    Localization.Lifting P.trW.Q P.trW F (verdierLift P F hF) := ⟨verdierLiftFactors P F hF⟩

noncomputable instance verdierLift_commShift : (verdierLift P F hF).CommShift ℤ :=
  Functor.commShiftOfLocalization P.trW.Q P.trW ℤ F (verdierLift P F hF)

instance verdierLiftFactors_commShift : NatTrans.CommShift (verdierLiftFactors P F hF).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization P.trW.Q P.trW ℤ F (verdierLift P F hF)

instance verdierLift_isTriangulated : (verdierLift P F hF).IsTriangulated := by
  let := Localization.essSurj_mapArrow P.trW.Q P.trW
  exact Functor.isTriangulated_of_precomp_iso (verdierLiftFactors P F hF)

end SerrePositivity
