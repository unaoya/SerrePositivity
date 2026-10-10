module

public import SerrePositivity.CategoryTheory.VerdierKaroubi
public import SerrePositivity.CategoryTheory.KaroubiLinear
public import Mathlib.CategoryTheory.Localization.Linear
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! # 商・完備化の比較と線形・三角構造の両立 -/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Idempotents
open CategoryTheory.Limits

variable {R : Type*} [Ring R] {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]

instance karoubiExtensionOne_linear (F : C ⥤ Karoubi D) [F.Linear R] :
    ((functorExtension₁ C D).obj F).Linear R where
  map_smul f r := by
    apply Karoubi.hom_ext
    change (F.map (r • f.f)).f = (r • F.map f.f).f
    rw [F.map_smul]

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

instance verdierLift_linear (P : ObjectProperty C) [P.IsTriangulated]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R]
    (hF : ∀ X, P X → IsZero (F.obj X)) : (verdierLift P F hF).Linear R :=
  (Localization.functor_linear_iff P.trW.Q P.trW R F (verdierLift P F hF)).mp inferInstance

variable (P : ObjectProperty C) [P.IsTriangulated]

omit [Linear R C] in
noncomputable instance karoubiVerdierOrderEquivalence_functor_commShift :
    (karoubiVerdierOrderEquivalence P).functor.CommShift ℤ := by
  change (completedKaroubiFirstToLast P).CommShift ℤ
  infer_instance

omit [Linear R C] in
noncomputable instance karoubiVerdierOrderEquivalence_inverse_commShift :
    (karoubiVerdierOrderEquivalence P).inverse.CommShift ℤ :=
  (karoubiVerdierOrderEquivalence P).commShiftInverse ℤ

omit [Linear R C] in
instance karoubiVerdierOrderEquivalence_commShift :
    (karoubiVerdierOrderEquivalence P).CommShift ℤ :=
  (karoubiVerdierOrderEquivalence P).commShift_of_functor ℤ

omit [Linear R C] in
instance karoubiVerdierOrderEquivalence_functor_isTriangulated :
    (karoubiVerdierOrderEquivalence P).functor.IsTriangulated := by
  change (completedKaroubiFirstToLast P).IsTriangulated
  infer_instance

omit [Linear R C] in
instance karoubiVerdierOrderEquivalence_isTriangulated :
    (karoubiVerdierOrderEquivalence P).IsTriangulated :=
  CategoryTheory.Equivalence.IsTriangulated.mk' _ inferInstance

instance karoubiVerdierOrderEquivalence_functor_linear :
    (karoubiVerdierOrderEquivalence P).functor.Linear R := by
  change (completedKaroubiFirstToLast P).Linear R
  infer_instance

instance karoubiVerdierOrderEquivalence_inverse_linear :
    (karoubiVerdierOrderEquivalence P).inverse.Linear R := by
  let E := karoubiVerdierOrderEquivalence P
  have : (E.functor ⋙ E.inverse).Linear R := Functor.linear_of_iso R E.unitIso
  exact Functor.linear_of_full_essSurj_comp E.functor E.inverse

end SerrePositivity
