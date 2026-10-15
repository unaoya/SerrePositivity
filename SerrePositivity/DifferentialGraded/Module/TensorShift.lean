module
public import SerrePositivity.DifferentialGraded.Complexes.TensorShift
public import SerrePositivity.DifferentialGraded.Module.Free
public import SerrePositivity.DifferentialGraded.Module.ShiftCoherence

/-! # tensor因子のshiftとdg加群shiftの比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左因子をshiftしたtensor加群と、tensor加群のshiftの全dg自然な同型。 -/
def tensorModuleShiftIso (K : Complex A) (M : RightModule A D) (s : ℤ) :
    ForgetEnrichment.of (Complex A) (tensorModule (K⟦s⟧) M) ≅
      (ForgetEnrichment.of (Complex A) (tensorModule K M))⟦s⟧ :=
  moduleIsoMk A D (M := tensorModule (K⟦s⟧) M) (N := shiftModule s (tensorModule K M))
    (fun x => SerrePositivity.cochainTensorShiftLeft K (M.obj x) s) (by
      intro x y
      change (M.map x y ≫ tensorLeftHom (K⟦s⟧) (M.obj x) (M.obj y)) ≫
        homPostcompose _ (SerrePositivity.cochainTensorShiftLeft K (M.obj y) s).hom = _
      simp only [Category.assoc]
      rw [tensorShiftLeft_hom_naturality]
      rfl)

@[simp] lemma tensorModuleShiftIso_hom_eval (K : Complex A) (M : RightModule A D)
    (s : ℤ) (x : D) :
    (moduleEvaluation A D x).map (tensorModuleShiftIso A D K M s).hom =
      (SerrePositivity.cochainTensorShiftLeft K (M.obj (op x)) s).hom :=
  moduleIsoMk_hom_eval A D _ _ x

@[simp] lemma tensorModuleShiftIso_inv_eval (K : Complex A) (M : RightModule A D)
    (s : ℤ) (x : D) :
    (moduleEvaluation A D x).map (tensorModuleShiftIso A D K M s).inv =
      (SerrePositivity.cochainTensorShiftLeft K (M.obj (op x)) s).inv :=
  moduleIsoMk_inv_eval A D _ _ x

/-- free_xは複体の整数shiftを加群shiftへ運ぶ。 -/
def freeAtShiftIso (x : D) (K : Complex A) (s : ℤ) :
    (freeAt x).obj (K⟦s⟧) ≅ ((freeAt x).obj K)⟦s⟧ :=
  tensorModuleShiftIso A D K (representable A x) s

end SerrePositivity.DifferentialGraded
