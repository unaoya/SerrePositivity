module
public import SerrePositivity.DifferentialGraded.Module.HomElementComposition

/-! # 全次数の後合成をHom複体間のcochainへ転置する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHomWhiskerLeft_apply_π {T M N : ModuleCategory A D} (f : M ⟶ N)
    (q : ℤ) (z : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M)).X q) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N) x).f q
        ((eHomWhiskerLeft (Complex A) T f).f q z) =
      ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) M) x).f q z).comp
          (Cochain.ofHom ((moduleEvaluation A D x).map f)) (add_zero q) :=
  congrArg (fun a => a.f q z) (moduleHomWhiskerLeft_π A D (M := T) f x)

lemma moduleHomCompose_π {T M N : RightModule A D} {p q n : ℤ}
    (g : (moduleHom A D M N).X p) (z : (moduleHom A D T M).X q)
    (hn : q + p = n) (x : D) :
    (moduleHomπ A D T N x).f n (compose A (x := T) (y := M) (z := N) g z hn) =
      ((moduleHomπ A D T M x).f q z).comp ((moduleHomπ A D M N x).f p g) hn := by
  unfold compose
  simp only [Units.smul_def, map_zsmul]
  change (q * p).negOnePow •
    (moduleHomπ A D T N x).f n (forward A (x := T) (y := M) (z := N) z g hn) = _
  rw [moduleHomForward_π, smul_smul, Int.units_mul_self, one_smul]

def modulePostcompositionMap (T M N : RightModule A D) :
    moduleHom A D M N ⟶ homComplex A (moduleHom A D T M) (moduleHom A D T N) :=
  curryRight ((β_ (moduleHom A D M N) (moduleHom A D T M)).hom ≫
    moduleComposition A D T M N)

lemma modulePostcompositionMap_apply (T M N : RightModule A D) {p q n : ℤ}
    (g : (moduleHom A D M N).X p) (z : (moduleHom A D T M).X q)
    (hn : q + p = n) :
    (((modulePostcompositionMap A D T M N).f p g).v q n hn) z =
      compose A (x := T) (y := M) (z := N) g z hn := by
  change (moduleComposition A D T M N).f n
    ((signedSwap (moduleHom A D M N) (moduleHom A D T M)).hom.f n
      (ιTensorObj (moduleHom A D M N) (moduleHom A D T M) p q n (by omega) (g ⊗ₜ[A] z))) = _
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]
  change (p * q).negOnePow • forward A (x := T) (y := M) (z := N) z g hn = _
  rw [compose, mul_comm p q]

lemma modulePostcompositionMap_d (T M N : RightModule A D) (p r : ℤ)
    (g : (moduleHom A D M N).X p) :
    δ p r ((modulePostcompositionMap A D T M N).f p g) =
      (modulePostcompositionMap A D T M N).f r ((moduleHom A D M N).d p r g) :=
  congrArg (fun a => a g) ((modulePostcompositionMap A D T M N).comm p r)

lemma modulePostcompositionMap_closed (T : ModuleCategory A D)
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    (modulePostcompositionMap A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N)).f 0
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val =
      Cochain.ofHom (eHomWhiskerLeft (Complex A) T f) := by
  apply Cochain.ext₀
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((modulePostcompositionMap A D (ForgetEnrichment.to (Complex A) T)
    (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N)).f 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val).v q q (add_zero q)) z =
        (eHomWhiskerLeft (Complex A) T f).f q z
  rw [modulePostcompositionMap_apply]
  apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) T)
    (N := ForgetEnrichment.to (Complex A) N)
  intro x
  rw [moduleHomCompose_π, ← moduleEvaluation_cochain]
  exact (congrArg (fun a => a.f q z) (moduleHomWhiskerLeft_π A D (M := T) f x)).symm

end SerrePositivity.DifferentialGraded
