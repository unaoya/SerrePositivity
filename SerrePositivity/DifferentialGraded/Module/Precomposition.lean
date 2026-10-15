module
public import SerrePositivity.DifferentialGraded.Module.HomElementComposition
public import SerrePositivity.DifferentialGraded.Module.Homotopy

/-! # 前合成の全次数転置と全dg自然なホモトピーの像

次数pの前合成は入力次数qについてKoszul符号を含む豊穣順合成である。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def modulePrecompositionMap (M N T : RightModule A D) :
    moduleHom A D M N ⟶ homComplex A (moduleHom A D N T) (moduleHom A D M T) :=
  curryRight (moduleComposition A D M N T)

lemma modulePrecompositionMap_apply (M N T : RightModule A D) {p q n : ℤ}
    (g : (moduleHom A D M N).X p) (z : (moduleHom A D N T).X q)
    (hn : q + p = n) :
    (((modulePrecompositionMap A D M N T).f p g).v q n hn) z =
      forward A (x := M) (y := N) (z := T) g z (by omega) := rfl

lemma modulePrecompositionMap_d (M N T : RightModule A D) (p r : ℤ)
    (g : (moduleHom A D M N).X p) :
    δ p r ((modulePrecompositionMap A D M N T).f p g) =
      (modulePrecompositionMap A D M N T).f r ((moduleHom A D M N).d p r g) :=
  congrArg (fun a => a g) ((modulePrecompositionMap A D M N T).comm p r)

lemma modulePrecompositionMap_closed {M N : ModuleCategory A D} (f : M ⟶ N)
    (T : ModuleCategory A D) :
    (modulePrecompositionMap A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) T)).f 0
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val =
      Cochain.ofHom (eHomWhiskerRight (Complex A) f T) := by
  apply Cochain.ext₀
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((modulePrecompositionMap A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) T)).f 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val).v q q (add_zero q)) z =
        (eHomWhiskerRight (Complex A) f T).f q z
  rw [modulePrecompositionMap_apply]
  apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) M)
    (N := ForgetEnrichment.to (Complex A) T)
  intro x
  rw [moduleHomForward_π, zero_mul, Int.negOnePow_zero, one_smul,
    ← moduleEvaluation_cochain]
  exact (moduleHomWhiskerRight_apply_π A D f q z x).symm

def moduleHomPrecomposeHomotopy {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ModuleHomotopy A D f g) (T : ModuleCategory A D) :
    Homotopy (eHomWhiskerRight (Complex A) f T) (eHomWhiskerRight (Complex A) g T) := by
  let H := modulePrecompositionMap A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) T)
  have hd := modulePrecompositionMap_d A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) T) (-1) 0 h.val
  change δ (-1) 0 (H.f (-1) h.val) =
    H.f 0 ((homObject A (RightModule A D) M N).d (-1) 0 h.val) at hd
  rw [h.property, map_sub, modulePrecompositionMap_closed,
    modulePrecompositionMap_closed] at hd
  refine (Cochain.equivHomotopy _ _).symm ⟨H.f (-1) h.val, ?_⟩
  exact (sub_eq_iff_eq_add).1 hd.symm

end SerrePositivity.DifferentialGraded
