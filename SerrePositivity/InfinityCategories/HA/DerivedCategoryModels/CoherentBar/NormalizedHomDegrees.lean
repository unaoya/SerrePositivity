module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedDifferential
/-!
概要：正規化実 bar からの全次数 Hom を、非退化単体の全列へ線形に同定する。
方針：同じ MC 微分変更で評価成分を保ち、非退化直和の Hom 同値へ渡す。
規約：正規化加群の公開型を保持する。native 余錐の全 HA 方程式は別に検証する。
使われ方：工程Bの余錐の成分と全 Hom 普遍性の正規化側の入口。
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

lemma dgCoherentBarNormalizedModule_d (x : Dᵒᵖ) (n : ℤ) :
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC).obj x).d n (n + 1) =
      ((ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F)).obj x).d
        n (n + 1) +
      ((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F))
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F)) x.unop).f 1
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTheta R D F)).v n (n + 1) rfl :=
  _root_.SerrePositivity.DifferentialGraded.maurerCartanPerturbComplex_d _ _
    (_root_.SerrePositivity.DifferentialGraded.moduleMaurerCartan_evaluation R D _ _
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTheta_maurerCartan R D F hMC) x.unop) n

lemma dgCoherentBarNormalizedModule_map_v (x y : Dᵒᵖ) (p : ℤ)
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y p) (i j : ℤ) (hij : i + p = j) :
    (((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC).map x y).f p a).v i j hij =
      (((ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F)).map x y).f
        p a).v i j hij := rfl

def dgCoherentBarNormalizedHomEquiv (q : ℤ) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F)) N).X q ≃ₗ[R]
      (∀ s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedIndex I,
        (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
          (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D F s)) N).X q) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCoproductHomDegreeIso R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D F)
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N) q).toLinearEquiv

def dgCoherentBarNormalizedRebaseHom (q : ℤ)
    (z : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F)) N).X q) :
    (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N).X q :=
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
    simpa only [Cochain.mk_v, dgCoherentBarNormalizedModule_map_v] using h)

def dgCoherentBarNormalizedForgetHom (q : ℤ)
    (z : (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N).X q) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F)) N).X q :=
  _root_.SerrePositivity.DifferentialGraded.moduleHomElementMk R D q
    (fun x => Cochain.mk (fun i j hij =>
      ((moduleHomπ R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N x.unop).f q z).v i j hij)) (by
    intro x y p a
    apply Cochain.ext
    intro i j hij
    have h := congrArg (fun f => f.v i j hij)
      (_root_.SerrePositivity.DifferentialGraded.moduleHomElement_naturality R D q z x y p a)
    rw [Cochain.units_smul_v] at h ⊢
    rw [Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
      Cochain.comp_v _ _ _ i (i + q) j rfl (by omega)] at h ⊢
    simpa only [Cochain.mk_v, dgCoherentBarNormalizedModule_map_v] using h)

def dgCoherentBarNormalizedHomDegreeEquiv (q : ℤ) :
    (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N).X q ≃ₗ[R]
      (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F)) N).X q where
  toFun := dgCoherentBarNormalizedForgetHom R D F hMC N q
  invFun := dgCoherentBarNormalizedRebaseHom R D F hMC N q
  left_inv z := by
    apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext R D
    intro x
    apply Cochain.ext
    intro i j hij
    simp only [dgCoherentBarNormalizedForgetHom, dgCoherentBarNormalizedRebaseHom,
      _root_.SerrePositivity.DifferentialGraded.moduleHomElementMk_π, Cochain.mk_v]
  right_inv z := by
    apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext R D
    intro x
    apply Cochain.ext
    intro i j hij
    simp only [dgCoherentBarNormalizedForgetHom, dgCoherentBarNormalizedRebaseHom,
      _root_.SerrePositivity.DifferentialGraded.moduleHomElementMk_π, Cochain.mk_v]
  map_add' z w := by
    apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext R D
    intro x
    simp only [map_add, dgCoherentBarNormalizedForgetHom, _root_.SerrePositivity.DifferentialGraded.moduleHomElementMk_π]
    apply Cochain.ext
    intro i j hij
    rfl
  map_smul' a z := by
    apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext R D
    intro x
    simp only [map_smul, dgCoherentBarNormalizedForgetHom, _root_.SerrePositivity.DifferentialGraded.moduleHomElementMk_π]
    apply Cochain.ext
    intro i j hij
    rfl

lemma dgCoherentBarNormalizedHomDegreeEquiv_π (q : ℤ)
    (z : (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N).X q) (x : D)
    (i j : ℤ) (hij : i + q = j) :
    ((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F)) N x).f q
      (dgCoherentBarNormalizedHomDegreeEquiv R D F hMC N q z)).v i j hij =
      ((moduleHomπ R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N x).f q z).v i j hij := by
  change ((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D _ N x).f q
    (dgCoherentBarNormalizedForgetHom R D F hMC N q z)).v i j hij = _
  rw [dgCoherentBarNormalizedForgetHom, _root_.SerrePositivity.DifferentialGraded.moduleHomElementMk_π]
  rfl

lemma dgCoherentBarNormalizedHomDegreeEquiv_d (q : ℤ)
    (z : (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N).X q) :
    dgCoherentBarNormalizedHomDegreeEquiv R D F hMC N (q + 1)
      ((moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N).d q (q + 1) z) =
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F)) N).d q (q + 1)
      (dgCoherentBarNormalizedHomDegreeEquiv R D F hMC N q z) +
    (q + 1).negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R
      (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F))
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F)) (z := N)
      (dgCoherentBarNormalizedHomDegreeEquiv R D F hMC N q z) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTheta R D F)
      (by omega : 1 + q = q + 1) := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext R D
  intro x
  simp only [map_add, Units.smul_def, map_zsmul, _root_.SerrePositivity.DifferentialGraded.moduleHomElement_d_π,
    _root_.SerrePositivity.DifferentialGraded.moduleHomCompose_π]
  apply Cochain.ext
  intro i j hij
  rw [dgCoherentBarNormalizedHomDegreeEquiv_π, _root_.SerrePositivity.DifferentialGraded.moduleHomElement_d_π]
  rw [δ_v (F := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC).obj (Opposite.op x))
    (G := N.obj (Opposite.op x)) q (q + 1) rfl _ i j hij
      (i + q) (i + 1) (by omega) rfl]
  rw [dgCoherentBarNormalizedModule_d]
  rw [Cochain.add_v, Cochain.smul_v,
    δ_v q (q + 1) rfl _ i j hij (i + q) (i + 1) (by omega) rfl,
    Cochain.comp_v _ _ _ i (i + 1) j rfl (by omega)]
  simp only [dgCoherentBarNormalizedHomDegreeEquiv_π, add_comp, smul_add, Units.smul_def]
  abel

def dgCoherentBarNormalizedHomColumnsEquiv (q : ℤ) :
    (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N).X q ≃ₗ[R]
      (∀ s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedIndex I,
        (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
          (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D F s)) N).X q) :=
  (dgCoherentBarNormalizedHomDegreeEquiv R D F hMC N q).trans
    (dgCoherentBarNormalizedHomEquiv R D F N q)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
