module
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveHomotopyHom

/-! # 射影解像度の比較とK(D)における選択独立性

比較射は全dg自然なホモトピーまで一意であり、三つの解像度の比較と整合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

theorem moduleProjectiveResolution_comparison {P Q M : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (hQ : moduleHomotopicallyProjective A D Q)
    (p : P ⟶ M) (q : Q ⟶ M) (hp : moduleQuasiIso A D p) (hq : moduleQuasiIso A D q) :
    ∃ s : P ⟶ Q, moduleQuasiIso A D s ∧
      (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map q =
        (moduleToHomotopy A D).map p ∧ IsIso ((moduleToHomotopy A D).map s) := by
  obtain ⟨s, hs⟩ := moduleHomotopicallyProjective_homotopy_lift A D hP q hq p
  have hsK := (moduleToHomotopy_map_eq_iff A D (s ≫ q) p).2 hs
  have hscomp : moduleQuasiIso A D (s ≫ q) := by
    apply (moduleHomotopyQuasiIso_map_iff A D (s ≫ q)).1
    rw [hsK]
    exact (moduleHomotopyQuasiIso_map_iff A D p).2 hp
  have hsW : moduleQuasiIso A D s :=
    (moduleQuasiIso A D).of_postcomp (W' := moduleQuasiIso A D) s q hq hscomp
  refine ⟨s, hsW, ?_, moduleHomotopicallyProjective_quasiIso_isIso_homotopy A D hP hQ s hsW⟩
  exact ((moduleToHomotopy A D).map_comp s q).symm.trans hsK

theorem moduleSemifreeResolution_comparison {P Q M : ModuleCategory A D}
    (hP : moduleSemifree A D P) (hQ : moduleSemifree A D Q)
    (p : P ⟶ M) (q : Q ⟶ M) (hp : moduleQuasiIso A D p) (hq : moduleQuasiIso A D q) :
    ∃ s : P ⟶ Q, moduleQuasiIso A D s ∧
      (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map q =
        (moduleToHomotopy A D).map p ∧ IsIso ((moduleToHomotopy A D).map s) :=
  moduleProjectiveResolution_comparison A D (moduleSemifree_homotopicallyProjective A D hP)
    (moduleSemifree_homotopicallyProjective A D hQ) p q hp hq

lemma moduleProjectiveResolution_comparison_unique {P Q M : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (p : P ⟶ M) (q : Q ⟶ M)
    (hq : moduleQuasiIso A D q) (s t : P ⟶ Q)
    (hs : (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map q =
      (moduleToHomotopy A D).map p)
    (ht : (moduleToHomotopy A D).map t ≫ (moduleToHomotopy A D).map q =
      (moduleToHomotopy A D).map p) :
    (moduleToHomotopy A D).map s = (moduleToHomotopy A D).map t :=
  (moduleHomotopicallyProjective_homotopy_postcompose_bijective A D hP q hq).1
    (hs.trans ht.symm)

lemma moduleProjectiveResolution_comparison_cocycle {P Q R M : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (p : P ⟶ M) (q : Q ⟶ M) (r : R ⟶ M)
    (hr : moduleQuasiIso A D r) (s : P ⟶ Q) (t : Q ⟶ R) (u : P ⟶ R)
    (hs : (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map q =
      (moduleToHomotopy A D).map p)
    (ht : (moduleToHomotopy A D).map t ≫ (moduleToHomotopy A D).map r =
      (moduleToHomotopy A D).map q)
    (hu : (moduleToHomotopy A D).map u ≫ (moduleToHomotopy A D).map r =
      (moduleToHomotopy A D).map p) :
    (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map t =
      (moduleToHomotopy A D).map u := by
  apply (moduleHomotopicallyProjective_homotopy_postcompose_bijective A D hP r hr).1
  dsimp only
  rw [Category.assoc, ht, hs, hu]

end SerrePositivity.DifferentialGraded
