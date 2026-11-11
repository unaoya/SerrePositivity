module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedNativeHomCoordinates
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeColumns
/-!
概要：native 余錐の成分への後合成を、正規化全 Hom の線形座標と厳密に比較する。
方針：MC 前後で保たれる評価成分と、非退化直和への制限を使う。
規約：全次数の元と同じ元の native 成分を保持する。
使われ方：native Hom 普遍性で使う実際の前向き写像の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open HomologicalComplex CochainComplex HomComplex
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

lemma dgCoherentBarNormalizedHomEquiv_apply (q : ℤ)
    (z : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F)) N).X q)
    (s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedIndex I) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedHomEquiv R D F N q z s =
      (eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D F) s)
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N)).f q z :=
  ConcreteCategory.congr_hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCoproductHomDegreeIso_π R D
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D F) (ForgetEnrichment.of (Complex R) N) q s) z

lemma dgCoherentBarNormalizedRebase_compose (M : _root_.SerrePositivity.DifferentialGraded.RightModule R D) {p q k : ℤ}
    (z : (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N).X q)
    (w : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D M
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F))).X p)
    (hk : p + q = k) :
    compose R (x := M) (y := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) (z := N) z
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTargetRebase R D F hMC M p w) hk =
    _root_.SerrePositivity.DifferentialGraded.compose R (x := M)
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F)) (z := N)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedHomDegreeEquiv R D F hMC N q z) w hk := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext R D (M := M) (N := N)
  intro x
  rw [_root_.SerrePositivity.DifferentialGraded.moduleHomCompose_π, _root_.SerrePositivity.DifferentialGraded.moduleHomCompose_π]
  apply Cochain.ext
  intro i j hij
  rw [Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
    Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTargetRebase_π, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedHomDegreeEquiv_π]

lemma dgCoherentBarNormalizedShiftedInclusion_nondegenerate
    (s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedIndex I) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedShiftedInclusion R D F s.val =
    (s.val.1 : ℤ).negOnePow •
      (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s.val))
        (Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D F) s)).f (-(s.val.1 : ℤ))
        (moduleShiftInElement R D (s.val.1 : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s.val)) := by
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedShiftedInclusion _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion
  simp only [Units.smul_def, map_zsmul]
  have h := congrArg (fun f => f.f (-(s.val.1 : ℤ))
    (moduleShiftInElement R D (s.val.1 : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s.val)))
    (eHomWhiskerLeft_comp (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s.val))
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s.val)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F))
  change (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
    (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s.val))
    (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s.val ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)).f (-(s.val.1 : ℤ)) _ =
    (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s.val))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)).f (-(s.val.1 : ℤ))
      ((eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s.val))
        (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s.val)).f (-(s.val.1 : ℤ))
        (moduleShiftInElement R D (s.val.1 : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s.val))) at h
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection_ι] at h
  rw [← h]

lemma dgCoherentBarNativeColumn_compose_eq_coordinates (q : ℤ)
    (z : (moduleHom R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N).X q)
    (s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedIndex I) :
    compose R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s.val)
      (y := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) (z := N) z
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC s.val)
      (show -(s.val.1 : ℤ) + q = q - (s.val.1 : ℤ) by omega) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeHomEquiv R D F hMC N q z s := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn, dgCoherentBarNormalizedRebase_compose,
    dgCoherentBarNormalizedShiftedInclusion_nondegenerate, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_right,
    _root_.SerrePositivity.DifferentialGraded.moduleHomClosedInsertion R D
      (S := ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s.val))
      (M := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D F s)
      (N := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F) (P := ForgetEnrichment.of (Complex R) N)]
  change _ = (s.val.1 : ℤ).negOnePow •
    compose R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s.val)
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D F s)) (z := N)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedHomEquiv R D F N q
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedHomDegreeEquiv R D F hMC N q z) s)
      (moduleShiftInElement R D (s.val.1 : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s.val)) (by omega)
  rw [dgCoherentBarNormalizedHomEquiv_apply]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
