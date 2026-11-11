module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Module
/-!
概要：MC 変形後の bar からの全次数 Hom を元の graded Hom に同定する。
方針：評価 cochain の成分を保持し、全次数の豊穣自然性で Hom end に戻す。
規約：この同値は次数ごとの線形同値であり、元の微分を保つ鎖同型とはしない。
使われ方：native 余錐の高次成分と bar Hom の twisted 微分の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits Preadditive DifferentialGraded SSet
open HomologicalComplex CochainComplex HomComplex
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

def dgCoherentBarRebaseHom (q : ℤ)
    (z : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) N).X q) :
    (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC) N).X q :=
  _root_.SerrePositivity.DifferentialGraded.moduleHomElementMk R D q
    (fun x => Cochain.mk (fun i j hij =>
      ((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D _ N x.unop).f q z).v i j hij)) (by
    intro x y p a
    apply Cochain.ext
    intro i j hij
    have h := congrArg (fun f => f.v i j hij)
      (_root_.SerrePositivity.DifferentialGraded.moduleHomElement_naturality R D q z x y p a)
    rw [Cochain.units_smul_v] at h ⊢
    rw [Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
      Cochain.comp_v _ _ _ i (i + q) j rfl (by omega)] at h ⊢
    simpa only [Cochain.mk_v, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule_map_v] using h)

def dgCoherentBarForgetHom (q : ℤ)
    (z : (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC) N).X q) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) N).X q :=
  _root_.SerrePositivity.DifferentialGraded.moduleHomElementMk R D q
    (fun x => Cochain.mk (fun i j hij =>
      ((moduleHomπ R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC) N x.unop).f q z).v i j hij)) (by
    intro x y p a
    apply Cochain.ext
    intro i j hij
    have h := congrArg (fun f => f.v i j hij)
      (_root_.SerrePositivity.DifferentialGraded.moduleHomElement_naturality R D q z x y p a)
    rw [Cochain.units_smul_v] at h ⊢
    rw [Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
      Cochain.comp_v _ _ _ i (i + q) j rfl (by omega)] at h ⊢
    simpa only [Cochain.mk_v, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule_map_v] using h)

def dgCoherentBarHomDegreeEquiv (q : ℤ) :
    (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC) N).X q ≃ₗ[R]
      (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) N).X q where
  toFun := dgCoherentBarForgetHom R D F hMC N q
  invFun := dgCoherentBarRebaseHom R D F hMC N q
  left_inv z := by
    apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext R D
    intro x
    apply Cochain.ext
    intro i j hij
    simp only [dgCoherentBarForgetHom, dgCoherentBarRebaseHom,
      _root_.SerrePositivity.DifferentialGraded.moduleHomElementMk_π, Cochain.mk_v]
  right_inv z := by
    apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext R D
    intro x
    apply Cochain.ext
    intro i j hij
    simp only [dgCoherentBarForgetHom, dgCoherentBarRebaseHom,
      _root_.SerrePositivity.DifferentialGraded.moduleHomElementMk_π, Cochain.mk_v]
  map_add' z w := by
    apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext R D
    intro x
    simp only [map_add, dgCoherentBarForgetHom, _root_.SerrePositivity.DifferentialGraded.moduleHomElementMk_π]
    apply Cochain.ext
    intro i j hij
    rfl
  map_smul' a z := by
    apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext R D
    intro x
    simp only [map_smul, dgCoherentBarForgetHom, _root_.SerrePositivity.DifferentialGraded.moduleHomElementMk_π]
    apply Cochain.ext
    intro i j hij
    rfl

lemma dgCoherentBarHomDegreeEquiv_π (q : ℤ)
    (z : (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC) N).X q) (x : D)
    (i j : ℤ) (hij : i + q = j) :
    ((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) N x).f q
      (dgCoherentBarHomDegreeEquiv R D F hMC N q z)).v i j hij =
      ((moduleHomπ R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC) N x).f q z).v i j hij := by
  change ((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D _ N x).f q
    (dgCoherentBarForgetHom R D F hMC N q z)).v i j hij = _
  rw [dgCoherentBarForgetHom, _root_.SerrePositivity.DifferentialGraded.moduleHomElementMk_π]
  rfl

lemma dgCoherentBarHomDegreeEquiv_d (q : ℤ)
    (z : (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC) N).X q) :
    dgCoherentBarHomDegreeEquiv R D F hMC N (q + 1)
      ((moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC) N).d q (q + 1) z) =
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) N).d q (q + 1)
      (dgCoherentBarHomDegreeEquiv R D F hMC N q z) +
    (q + 1).negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R
      (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) (z := N)
      (dgCoherentBarHomDegreeEquiv R D F hMC N q z) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F)
      (by omega : 1 + q = q + 1) := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext R D
  intro x
  simp only [map_add, Units.smul_def, map_zsmul, _root_.SerrePositivity.DifferentialGraded.moduleHomElement_d_π,
    _root_.SerrePositivity.DifferentialGraded.moduleHomCompose_π]
  apply Cochain.ext
  intro i j hij
  rw [dgCoherentBarHomDegreeEquiv_π, _root_.SerrePositivity.DifferentialGraded.moduleHomElement_d_π]
  rw [δ_v (F := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC).obj (Opposite.op x))
    (G := N.obj (Opposite.op x)) q (q + 1) rfl _ i j hij
      (i + q) (i + 1) (by omega) rfl]
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule_d]
  rw [Cochain.add_v, Cochain.smul_v,
    δ_v q (q + 1) rfl _ i j hij (i + q) (i + 1) (by omega) rfl,
    Cochain.comp_v _ _ _ i (i + 1) j rfl (by omega)]
  simp only [dgCoherentBarHomDegreeEquiv_π, add_comp, smul_add, Units.smul_def]
  abel

def dgCoherentBarHomColumnsEquiv (q : ℤ) :
    (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F hMC) N).X q ≃ₗ[R]
      (∀ s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I,
        (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
          (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s)) N).X q) :=
  (dgCoherentBarHomDegreeEquiv R D F hMC N q).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv R D F (ForgetEnrichment.of (Complex R) N) q)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
