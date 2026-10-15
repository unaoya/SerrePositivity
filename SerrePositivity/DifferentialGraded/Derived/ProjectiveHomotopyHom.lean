module
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveHomotopyLifting

/-! # 射影的始域からのK(D)のHomとquasiIso

準同型の後合成は全単射であり、射影的対象間の準同型はK(D)で同型となる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHomotopicallyProjective_postcompose_map_eq_iff {T M N : ModuleCategory A D}
    (hT : moduleHomotopicallyProjective A D T) (f : M ⟶ N)
    (hf : moduleQuasiIso A D f) (s t : T ⟶ M) :
    (moduleToHomotopy A D).map (s ≫ f) = (moduleToHomotopy A D).map (t ≫ f) ↔
      (moduleToHomotopy A D).map s = (moduleToHomotopy A D).map t := by
  constructor
  · intro h
    obtain ⟨h⟩ := (moduleToHomotopy_map_eq_iff A D _ _).1 h
    exact (moduleToHomotopy_map_eq_iff A D s t).2
      (moduleHomotopicallyProjective_homotopy_reflect A D hT f hf s t h)
  · intro h
    simpa only [CategoryTheory.Functor.map_comp] using
      congrArg (fun a => a ≫ (moduleToHomotopy A D).map f) h

lemma moduleHomotopicallyProjective_homotopy_postcompose_bijective
    {T M N : ModuleCategory A D} (hT : moduleHomotopicallyProjective A D T)
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    Function.Bijective (fun s : (moduleToHomotopy A D).obj T ⟶ (moduleToHomotopy A D).obj M =>
      s ≫ (moduleToHomotopy A D).map f) := by
  constructor
  · intro s t h
    obtain ⟨s, rfl⟩ := (moduleToHomotopy A D).map_surjective s
    obtain ⟨t, rfl⟩ := (moduleToHomotopy A D).map_surjective t
    apply (moduleHomotopicallyProjective_postcompose_map_eq_iff A D hT f hf s t).1
    simpa only [CategoryTheory.Functor.map_comp] using h
  · intro g
    obtain ⟨g, rfl⟩ := (moduleToHomotopy A D).map_surjective g
    obtain ⟨s, hs⟩ := moduleHomotopicallyProjective_homotopy_lift A D hT f hf g
    refine ⟨(moduleToHomotopy A D).map s, ?_⟩
    dsimp only
    rw [← CategoryTheory.Functor.map_comp]
    exact (moduleToHomotopy_map_eq_iff A D _ _).2 hs

lemma moduleHomotopicallyProjective_quasiIso_isIso_homotopy
    {M N : ModuleCategory A D} (hM : moduleHomotopicallyProjective A D M)
    (hN : moduleHomotopicallyProjective A D N) (f : M ⟶ N)
    (hf : moduleQuasiIso A D f) : IsIso ((moduleToHomotopy A D).map f) := by
  obtain ⟨s, hs⟩ := moduleHomotopicallyProjective_homotopy_lift A D hN f hf (𝟙 N)
  have hs' : (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map f = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp]
    exact ((moduleToHomotopy_map_eq_iff A D _ _).2 hs).trans
      ((moduleToHomotopy A D).map_id N)
  have ht : (moduleToHomotopy A D).map f ≫ (moduleToHomotopy A D).map s = 𝟙 _ := by
    apply (moduleHomotopicallyProjective_homotopy_postcompose_bijective A D hM f hf).1
    dsimp only
    rw [Category.assoc, hs', Category.comp_id, Category.id_comp]
  exact ⟨⟨(moduleToHomotopy A D).map s, ht, hs'⟩⟩

end SerrePositivity.DifferentialGraded
