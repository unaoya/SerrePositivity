module
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveResolution
public import SerrePositivity.DifferentialGraded.Derived.HomOutPrecomposition

/-! # 射影解像度による導来Hom関手の選択独立性

比較の自然同型は、任意の比較射による前合成と一致し、恒等・cocycle条件を満たす。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

namespace ModuleProjectiveResolution
variable {A D} {M : ModuleCategory A D}

def derivedHom (P : ModuleProjectiveResolution A D M) :
    DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat A) :=
  moduleDerivedHomOut A D P.obj P.projective

def derivedHomComputation (P : ModuleProjectiveResolution A D M) (T : ModuleCategory A D) :
    P.derivedHom.obj ((moduleToDerived A D).obj T) ≅
      DerivedCategory.Q.obj (P.obj ⟶[Complex A] T) :=
  moduleDerivedHomOutEnrichedComputation A D P.obj P.projective T

def derivedHomIso (P Q : ModuleProjectiveResolution A D M) : Q.derivedHom ≅ P.derivedHom :=
  moduleDerivedHomOutPrecompIso A D P.projective Q.projective
    (P.comparison Q) (P.comparison_quasiIso Q)

lemma derivedHomIso_app (P Q : ModuleProjectiveResolution A D M) (T : ModuleCategory A D) :
    (P.derivedHomIso Q).hom.app ((moduleToDerived A D).obj T) =
      (Q.derivedHomComputation T).hom ≫
        DerivedCategory.Q.map (eHomWhiskerRight (Complex A) (P.comparison Q) T) ≫
          (P.derivedHomComputation T).inv :=
  moduleDerivedHomOutPrecomp_app A D P.projective Q.projective (P.comparison Q) T

lemma derivedHomIso_hom_eq (P Q : ModuleProjectiveResolution A D M) (s : P.obj ⟶ Q.obj)
    (hs : (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map Q.π =
      (moduleToHomotopy A D).map P.π) :
    (P.derivedHomIso Q).hom = moduleDerivedHomOutPrecomp A D P.projective Q.projective s := by
  change moduleDerivedHomOutPrecomp A D P.projective Q.projective (P.comparison Q) = _
  exact moduleDerivedHomOutPrecomp_eq_of_homotopy_map_eq A D P.projective Q.projective
    (P.comparison_unique Q s hs)

lemma derivedHomIso_self (P : ModuleProjectiveResolution A D M) :
    P.derivedHomIso P = Iso.refl P.derivedHom := by
  apply Iso.ext
  change (P.derivedHomIso P).hom = 𝟙 _
  rw [P.derivedHomIso_hom_eq P (𝟙 P.obj) (by
    rw [CategoryTheory.Functor.map_id, Category.id_comp])]
  exact moduleDerivedHomOutPrecomp_id A D P.obj P.projective

lemma derivedHomIso_trans (P Q R : ModuleProjectiveResolution A D M) :
    Q.derivedHomIso R ≪≫ P.derivedHomIso Q = P.derivedHomIso R := by
  apply Iso.ext
  change moduleDerivedHomOutPrecomp A D Q.projective R.projective (Q.comparison R) ≫
    moduleDerivedHomOutPrecomp A D P.projective Q.projective (P.comparison Q) =
      moduleDerivedHomOutPrecomp A D P.projective R.projective (P.comparison R)
  have hc : (moduleToHomotopy A D).map (P.comparison Q ≫ Q.comparison R) =
      (moduleToHomotopy A D).map (P.comparison R) :=
    ((moduleToHomotopy A D).map_comp _ _).trans (P.comparison_comp Q R)
  have h := moduleDerivedHomOutPrecomp_eq_of_homotopy_map_eq A D P.projective R.projective hc
  rw [moduleDerivedHomOutPrecomp_comp] at h
  exact h

end ModuleProjectiveResolution

lemma moduleCanonicalProjectiveResolution_derivedHom (M : ModuleCategory A D) :
    (moduleCanonicalProjectiveResolution A D M).derivedHom = moduleResolvedHomOut A D M := rfl

end SerrePositivity.DifferentialGraded
