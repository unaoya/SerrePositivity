module
public import SerrePositivity.DifferentialGraded.Module.HomElements
public import SerrePositivity.DifferentialGraded.Module.HomFunctor

/-! # 主Hom endの斉次合成と通常射による制限の成分 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHomForward_π {M N P : RightModule A D} {p q n : ℤ}
    (z : (moduleHom A D M N).X p) (w : (moduleHom A D N P).X q)
    (hn : p + q = n) (x : D) :
    (moduleHomπ A D M P x).f n (forward A (x := M) (y := N) (z := P) z w hn) =
      (p * q).negOnePow • (((moduleHomπ A D M N x).f p z).comp
        ((moduleHomπ A D N P x).f q w) hn) := by
  have h := congrArg (fun a => a.f n
    (ιTensorObj (moduleHom A D M N) (moduleHom A D N P) p q n hn (z ⊗ₜ[A] w)))
    (moduleComposition_π A D M N P x)
  change (moduleHomπ A D M P x).f n (forward A (x := M) (y := N) (z := P) z w hn) =
    (enrichedComposition _ _ _).f n
      ((moduleHomπ A D M N x ⊗ₘ moduleHomπ A D N P x).f n
        (ιTensorObj (moduleHom A D M N) (moduleHom A D N P) p q n hn (z ⊗ₜ[A] w))) at h
  rw [tensorMap_apply, enrichedComposition_apply] at h
  exact h

lemma moduleHomWhiskerRight_apply_π {M N P : ModuleCategory A D} (f : M ⟶ N)
    (q : ℤ) (z : (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) P)).X q) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) P) x).f q
        ((eHomWhiskerRight (Complex A) f P).f q z) =
      (Cochain.ofHom ((moduleEvaluation A D x).map f)).comp
        ((moduleHomπ A D (ForgetEnrichment.to (Complex A) N)
          (ForgetEnrichment.to (Complex A) P) x).f q z) (zero_add q) := by
  have h := congrArg (fun a => a.f q z) (moduleHomWhiskerRight_π A D (P := P) f x)
  exact h

end SerrePositivity.DifferentialGraded
