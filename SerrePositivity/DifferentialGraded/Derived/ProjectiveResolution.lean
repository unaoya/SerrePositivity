module
public import SerrePositivity.DifferentialGraded.Derived.ResolutionComparison

/-! # 証明付き射影解像度と標準比較

対象・増大射・全Homによる射影性・指定quasiIsoを保持する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

structure ModuleProjectiveResolution (M : ModuleCategory A D) where
  obj : ModuleCategory A D
  π : obj ⟶ M
  projective : moduleHomotopicallyProjective A D obj
  quasiIso : moduleQuasiIso A D π

def moduleCanonicalProjectiveResolution (M : ModuleCategory A D) :
    ModuleProjectiveResolution A D M where
  obj := moduleResolutionCandidate A D M
  π := moduleResolutionCandidateπ A D M
  projective := moduleSemifree_homotopicallyProjective A D
    (moduleResolutionCandidate_semifree A D M)
  quasiIso := moduleResolutionCandidateπ_quasiIso A D M

namespace ModuleProjectiveResolution
variable {A D} {M : ModuleCategory A D}

def comparison (P Q : ModuleProjectiveResolution A D M) : P.obj ⟶ Q.obj :=
  Classical.choose (moduleProjectiveResolution_comparison A D P.projective Q.projective
    P.π Q.π P.quasiIso Q.quasiIso)

lemma comparison_quasiIso (P Q : ModuleProjectiveResolution A D M) :
    moduleQuasiIso A D (P.comparison Q) :=
  (Classical.choose_spec (moduleProjectiveResolution_comparison A D P.projective Q.projective
    P.π Q.π P.quasiIso Q.quasiIso)).1

lemma comparison_fac (P Q : ModuleProjectiveResolution A D M) :
    (moduleToHomotopy A D).map (P.comparison Q) ≫ (moduleToHomotopy A D).map Q.π =
      (moduleToHomotopy A D).map P.π :=
  (Classical.choose_spec (moduleProjectiveResolution_comparison A D P.projective Q.projective
    P.π Q.π P.quasiIso Q.quasiIso)).2.1

lemma comparison_isIso_homotopy (P Q : ModuleProjectiveResolution A D M) :
    IsIso ((moduleToHomotopy A D).map (P.comparison Q)) :=
  moduleHomotopicallyProjective_quasiIso_isIso_homotopy A D P.projective Q.projective
    (P.comparison Q) (P.comparison_quasiIso Q)

lemma comparison_unique (P Q : ModuleProjectiveResolution A D M) (s : P.obj ⟶ Q.obj)
    (hs : (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map Q.π =
      (moduleToHomotopy A D).map P.π) :
    (moduleToHomotopy A D).map (P.comparison Q) = (moduleToHomotopy A D).map s :=
  moduleProjectiveResolution_comparison_unique A D P.projective P.π Q.π Q.quasiIso
    (P.comparison Q) s (P.comparison_fac Q) hs

lemma comparison_comp (P Q R : ModuleProjectiveResolution A D M) :
    (moduleToHomotopy A D).map (P.comparison Q) ≫
      (moduleToHomotopy A D).map (Q.comparison R) =
        (moduleToHomotopy A D).map (P.comparison R) :=
  moduleProjectiveResolution_comparison_cocycle A D P.projective P.π Q.π R.π R.quasiIso
    (P.comparison Q) (Q.comparison R) (P.comparison R)
    (P.comparison_fac Q) (Q.comparison_fac R) (P.comparison_fac R)

lemma comparison_self (P : ModuleProjectiveResolution A D M) :
    (moduleToHomotopy A D).map (P.comparison P) = 𝟙 _ := by
  have h := P.comparison_unique P (𝟙 P.obj) (by
    rw [CategoryTheory.Functor.map_id, Category.id_comp])
  exact h.trans ((moduleToHomotopy A D).map_id _)

end ModuleProjectiveResolution
end SerrePositivity.DifferentialGraded
