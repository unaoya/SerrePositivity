module
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveResolution

/-! # 射影解像度への射の持ち上げとK(D)での関手法則 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
namespace ModuleProjectiveResolution
variable {M N L : ModuleCategory A D}

def lift (P : ModuleProjectiveResolution A D M) (Q : ModuleProjectiveResolution A D N)
    (f : M ⟶ N) : P.obj ⟶ Q.obj :=
  Classical.choose (moduleHomotopicallyProjective_homotopy_lift A D P.projective
    Q.π Q.quasiIso (P.π ≫ f))

lemma lift_fac (P : ModuleProjectiveResolution A D M) (Q : ModuleProjectiveResolution A D N)
    (f : M ⟶ N) :
    (moduleToHomotopy A D).map (P.lift Q f) ≫ (moduleToHomotopy A D).map Q.π =
      (moduleToHomotopy A D).map P.π ≫ (moduleToHomotopy A D).map f := by
  have h := (Classical.choose_spec (moduleHomotopicallyProjective_homotopy_lift A D P.projective
    Q.π Q.quasiIso (P.π ≫ f)))
  have hK := (moduleToHomotopy_map_eq_iff A D _ _).2 h
  exact ((moduleToHomotopy A D).map_comp _ _).symm.trans
    (hK.trans ((moduleToHomotopy A D).map_comp _ _))

lemma lift_unique (P : ModuleProjectiveResolution A D M)
    (Q : ModuleProjectiveResolution A D N) (f : M ⟶ N) (s : P.obj ⟶ Q.obj)
    (hs : (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map Q.π =
      (moduleToHomotopy A D).map P.π ≫ (moduleToHomotopy A D).map f) :
    (moduleToHomotopy A D).map (P.lift Q f) = (moduleToHomotopy A D).map s :=
  (moduleHomotopicallyProjective_homotopy_postcompose_bijective A D
    P.projective Q.π Q.quasiIso).1 ((P.lift_fac Q f).trans hs.symm)

lemma lift_id (P : ModuleProjectiveResolution A D M) :
    (moduleToHomotopy A D).map (P.lift P (𝟙 M)) = 𝟙 _ := by
  have h := P.lift_unique P (𝟙 M) (𝟙 P.obj) (by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id])
  exact h.trans ((moduleToHomotopy A D).map_id _)

lemma lift_comp (P : ModuleProjectiveResolution A D M) (Q : ModuleProjectiveResolution A D N)
    (R : ModuleProjectiveResolution A D L) (f : M ⟶ N) (g : N ⟶ L) :
    (moduleToHomotopy A D).map (P.lift Q f) ≫ (moduleToHomotopy A D).map (Q.lift R g) =
      (moduleToHomotopy A D).map (P.lift R (f ≫ g)) := by
  have hs : (moduleToHomotopy A D).map (P.lift Q f ≫ Q.lift R g) ≫
      (moduleToHomotopy A D).map R.π =
        (moduleToHomotopy A D).map P.π ≫ (moduleToHomotopy A D).map (f ≫ g) := by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      Category.assoc, Q.lift_fac R g, ← Category.assoc, P.lift_fac Q f, Category.assoc]
  exact ((moduleToHomotopy A D).map_comp _ _).symm.trans
    (P.lift_unique R (f ≫ g) _ hs).symm

lemma lift_quasiIso (P : ModuleProjectiveResolution A D M)
    (Q : ModuleProjectiveResolution A D N) (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    moduleQuasiIso A D (P.lift Q f) := by
  have hK : (moduleToHomotopy A D).map (P.lift Q f ≫ Q.π) =
      (moduleToHomotopy A D).map (P.π ≫ f) :=
    ((moduleToHomotopy A D).map_comp _ _).trans
      ((P.lift_fac Q f).trans ((moduleToHomotopy A D).map_comp _ _).symm)
  have hc : moduleQuasiIso A D (P.lift Q f ≫ Q.π) := by
    apply (moduleHomotopyQuasiIso_map_iff A D _).1
    rw [hK]
    apply (moduleHomotopyQuasiIso_map_iff A D _).2
    exact (moduleQuasiIso A D).comp_mem _ _ P.quasiIso hf
  exact (moduleQuasiIso A D).of_postcomp (W' := moduleQuasiIso A D) _ _ Q.quasiIso hc

lemma lift_id_comparison (P Q : ModuleProjectiveResolution A D M) :
    (moduleToHomotopy A D).map (P.lift Q (𝟙 M)) =
      (moduleToHomotopy A D).map (P.comparison Q) :=
  P.lift_unique Q (𝟙 M) (P.comparison Q) (by
    simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using P.comparison_fac Q)

lemma lift_comparison_naturality (P P' : ModuleProjectiveResolution A D M)
    (Q Q' : ModuleProjectiveResolution A D N) (f : M ⟶ N) :
    (moduleToHomotopy A D).map (P.lift Q f) ≫ (moduleToHomotopy A D).map (Q.comparison Q') =
      (moduleToHomotopy A D).map (P.comparison P') ≫ (moduleToHomotopy A D).map (P'.lift Q' f) := by
  apply (moduleHomotopicallyProjective_homotopy_postcompose_bijective A D
    P.projective Q'.π Q'.quasiIso).1
  dsimp only
  rw [Category.assoc, Q.comparison_fac Q', P.lift_fac Q f,
    Category.assoc, P'.lift_fac Q' f, ← Category.assoc, P.comparison_fac P']

end ModuleProjectiveResolution
end SerrePositivity.DifferentialGraded
