module
public import SerrePositivity.DifferentialGraded.Tensor.Homotopy
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveHomotopyHom
public import SerrePositivity.DifferentialGraded.Derived.SemifreeProjective

/-! # 射影的/semifree対象間の準同型のtensorによる保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 射影的対象間の準同型は、任意の左加群とのtensorでホモトピー同値になる。 -/
def rightTensorProjectiveHomotopyEquiv (L : LeftModule A D) {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    HomotopyEquiv ((rightTensorFunctor A D L).obj M) ((rightTensorFunctor A D L).obj N) := by
  let Q := moduleToHomotopy A D
  have : IsIso (Q.map f) := moduleHomotopicallyProjective_quasiIso_isIso_homotopy A D hM hN f hf
  let g : N ⟶ M := Q.preimage (inv (Q.map f))
  have hg : Q.map g = inv (Q.map f) := Q.map_preimage _
  have hfg : Nonempty (ModuleHomotopy A D (f ≫ g) (𝟙 M)) := by
    apply (moduleToHomotopy_map_eq_iff A D _ _).1
    change Q.map (f ≫ g) = Q.map (𝟙 M)
    rw [CategoryTheory.Functor.map_comp, hg, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  have hgf : Nonempty (ModuleHomotopy A D (g ≫ f) (𝟙 N)) := by
    apply (moduleToHomotopy_map_eq_iff A D _ _).1
    change Q.map (g ≫ f) = Q.map (𝟙 N)
    rw [CategoryTheory.Functor.map_comp, hg, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
  refine
    { hom := (rightTensorFunctor A D L).map f
      inv := (rightTensorFunctor A D L).map g
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_ }
  · have ht := (rightTensorMap_homotopy A D L hfg.some).some
    change Homotopy ((rightTensorFunctor A D L).map (f ≫ g))
      ((rightTensorFunctor A D L).map (𝟙 M)) at ht
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using ht
  · have ht := (rightTensorMap_homotopy A D L hgf.some).some
    change Homotopy ((rightTensorFunctor A D L).map (g ≫ f))
      ((rightTensorFunctor A D L).map (𝟙 N)) at ht
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using ht

lemma rightTensor_projective_quasiIso (L : LeftModule A D) {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    QuasiIso ((rightTensorFunctor A D L).map f) :=
  (rightTensorProjectiveHomotopyEquiv A D L hM hN f hf).quasiIso_hom

/-- semifree解像度同士の準同型は、左加群にflat条件を課さずtensorで準同型になる。 -/
lemma rightTensor_semifree_quasiIso (L : LeftModule A D) {M N : ModuleCategory A D}
    (hM : moduleSemifree A D M) (hN : moduleSemifree A D N) (f : M ⟶ N)
    (hf : moduleQuasiIso A D f) : QuasiIso ((rightTensorFunctor A D L).map f) :=
  rightTensor_projective_quasiIso A D L
    (moduleSemifree_homotopicallyProjective A D hM)
    (moduleSemifree_homotopicallyProjective A D hN) f hf

end SerrePositivity.DifferentialGraded.BalancedTensor
