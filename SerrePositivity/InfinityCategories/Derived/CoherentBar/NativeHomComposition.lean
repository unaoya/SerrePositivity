module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedNativeHomCoordinates
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeColumns
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open HomologicalComplex CochainComplex HomComplex
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

lemma dgCoherentBarNormalizedHomEquiv_apply (q : ℤ)
    (z : (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F)) N).X q)
    (s : dgCoherentBarNormalizedIndex I) :
    dgCoherentBarNormalizedHomEquiv R D F N q z s =
      (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarNormalizedFamily R D F) s)
        (ForgetEnrichment.of (Complex R) N)).f q z :=
  ConcreteCategory.congr_hom (dgModuleCoproductHomDegreeIso_π R D
    (dgCoherentBarNormalizedFamily R D F) (ForgetEnrichment.of (Complex R) N) q s) z

lemma dgCoherentBarNormalizedRebase_compose (M : RightModule R D) {p q k : ℤ}
    (z : (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC) N).X q)
    (w : (moduleHom R D M
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))).X p)
    (hk : p + q = k) :
    compose R (x := M) (y := dgCoherentBarNormalizedModule R D F hMC) (z := N) z
      (dgCoherentBarNormalizedTargetRebase R D F hMC M p w) hk =
    compose R (x := M)
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F)) (z := N)
      (dgCoherentBarNormalizedHomDegreeEquiv R D F hMC N q z) w hk := by
  apply moduleHomElement_ext R D (M := M) (N := N)
  intro x
  rw [moduleHomCompose_π, moduleHomCompose_π]
  apply Cochain.ext
  intro i j hij
  rw [Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
    Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
    dgCoherentBarNormalizedTargetRebase_π, dgCoherentBarNormalizedHomDegreeEquiv_π]

lemma dgCoherentBarNormalizedShiftedInclusion_nondegenerate
    (s : dgCoherentBarNormalizedIndex I) :
    dgCoherentBarNormalizedShiftedInclusion R D F s.val =
    (s.val.1 : ℤ).negOnePow •
      (eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s.val))
        (Sigma.ι (dgCoherentBarNormalizedFamily R D F) s)).f (-(s.val.1 : ℤ))
        (moduleShiftInElement R D (s.val.1 : ℤ) (dgCoherentBarSource R D F s.val)) := by
  unfold dgCoherentBarNormalizedShiftedInclusion dgCoherentBarShiftedInclusion
  simp only [Units.smul_def, map_zsmul]
  have h := congrArg (fun f => f.f (-(s.val.1 : ℤ))
    (moduleShiftInElement R D (s.val.1 : ℤ) (dgCoherentBarSource R D F s.val)))
    (eHomWhiskerLeft_comp (Complex R)
      (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s.val))
      (Sigma.ι (dgCoherentBarFamily R D F) s.val)
      (dgCoherentBarNormalizedProjection R D F))
  change (eHomWhiskerLeft (Complex R)
    (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s.val))
    (Sigma.ι (dgCoherentBarFamily R D F) s.val ≫
      dgCoherentBarNormalizedProjection R D F)).f (-(s.val.1 : ℤ)) _ =
    (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s.val))
      (dgCoherentBarNormalizedProjection R D F)).f (-(s.val.1 : ℤ))
      ((eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s.val))
        (Sigma.ι (dgCoherentBarFamily R D F) s.val)).f (-(s.val.1 : ℤ))
        (moduleShiftInElement R D (s.val.1 : ℤ) (dgCoherentBarSource R D F s.val))) at h
  rw [dgCoherentBarNormalizedProjection_ι] at h
  rw [← h]

lemma dgCoherentBarNativeColumn_compose_eq_coordinates (q : ℤ)
    (z : (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC) N).X q)
    (s : dgCoherentBarNormalizedIndex I) :
    compose R (x := dgCoherentBarSource R D F s.val)
      (y := dgCoherentBarNormalizedModule R D F hMC) (z := N) z
      (dgCoherentBarNativeColumn R D F hMC s.val)
      (show -(s.val.1 : ℤ) + q = q - (s.val.1 : ℤ) by omega) =
      dgCoherentBarNormalizedNativeHomEquiv R D F hMC N q z s := by
  rw [dgCoherentBarNativeColumn, dgCoherentBarNormalizedRebase_compose,
    dgCoherentBarNormalizedShiftedInclusion_nondegenerate, DGNerve.compose_units_smul_right,
    moduleHomClosedInsertion R D
      (S := ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s.val))
      (M := dgCoherentBarNormalizedFamily R D F s)
      (N := dgCoherentBarNormalizedGraded R D F) (P := ForgetEnrichment.of (Complex R) N)]
  change _ = (s.val.1 : ℤ).negOnePow •
    compose R (x := dgCoherentBarSource R D F s.val)
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedFamily R D F s)) (z := N)
      (dgCoherentBarNormalizedHomEquiv R D F N q
        (dgCoherentBarNormalizedHomDegreeEquiv R D F hMC N q z) s)
      (moduleShiftInElement R D (s.val.1 : ℤ) (dgCoherentBarSource R D F s.val)) (by omega)
  rw [dgCoherentBarNormalizedHomEquiv_apply]

end SerrePositivity.InfinityCategories
