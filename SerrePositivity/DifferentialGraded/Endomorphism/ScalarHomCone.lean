module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomShift
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomShortExact
public import SerrePositivity.DifferentialGraded.Module.ConeGradedSplit

/-! # 実際のHom係数変更比較のcone・三角形閉性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex Pretriangulated Limits
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarModuleHom_cone {M N : ModuleCategory A D} (f : M ⟶ N)
    (T : ModuleCategory A D)
    (hM : QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) T)))
    (hN : QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) T))) :
    QuasiIso (scalarModuleHom φ D
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) T)) :=
  scalarModuleHom_gradedSplit_middle φ D (moduleConeGradedSplit A D f) T
    (scalarModuleHom_shift φ D 1 (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) T) hM) hN

lemma scalarModuleHomComparisonLocus_triangle_obj₃
    (T : Triangle (ModuleHomotopyCategory A D)) (hT : T ∈ distTriang _)
    (h₁ : scalarModuleHomComparisonLocus φ D T.obj₁)
    (h₂ : scalarModuleHomComparisonLocus φ D T.obj₂) :
    scalarModuleHomComparisonLocus φ D T.obj₃ := by
  obtain ⟨M, N, f, ⟨e⟩⟩ := hT
  have hM := (scalarModuleHomComparisonLocus φ D).prop_of_iso (Triangle.π₁.mapIso e) h₁
  have hN := (scalarModuleHomComparisonLocus φ D).prop_of_iso (Triangle.π₂.mapIso e) h₂
  apply (scalarModuleHomComparisonLocus φ D).prop_of_iso (Triangle.π₃.mapIso e.symm)
  intro Q
  exact scalarModuleHom_cone φ D f Q (hM Q) (hN Q)

instance scalarModuleHomComparisonLocusTriangulatedClosed₃ :
    (scalarModuleHomComparisonLocus φ D).IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk' (scalarModuleHomComparisonLocus_triangle_obj₃ φ D)

instance scalarModuleHomComparisonLocusTriangulatedClosed₂ :
    (scalarModuleHomComparisonLocus φ D).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

lemma scalarModuleHomComparisonLocus_zero :
    scalarModuleHomComparisonLocus φ D ((moduleToHomotopy A D).obj (moduleZero A D)) := by
  intro T
  change QuasiIso (scalarModuleHom φ D (zeroModule A D) (ForgetEnrichment.to (Complex A) T))
  have hs := moduleHom_isZero_src A D (zeroModule A D) (ForgetEnrichment.to (Complex A) T)
    (fun _ => isZero_zero (Complex A))
  have ht := moduleHom_isZero_src A' (ScalarExtension.DGBaseChange φ D)
    (ScalarExtension.rightModule φ D (zeroModule A D))
    (ScalarExtension.rightModule φ D (ForgetEnrichment.to (Complex A) T))
    (fun _ => (ScalarExtension.extension φ).map_isZero (isZero_zero (Complex A)))
  have := ((ScalarExtension.extension φ).map_isZero hs).isIso ht
    (scalarModuleHom φ D (zeroModule A D) (ForgetEnrichment.to (Complex A) T))
  infer_instance

instance scalarModuleHomComparisonLocusNonempty :
    (scalarModuleHomComparisonLocus φ D).Nonempty :=
  ObjectProperty.nonempty_of_prop (scalarModuleHomComparisonLocus_zero φ D)

instance scalarModuleHomComparisonLocusContainsZero :
    (scalarModuleHomComparisonLocus φ D).ContainsZero := inferInstance

instance scalarModuleHomComparisonLocusIsTriangulated :
    (scalarModuleHomComparisonLocus φ D).IsTriangulated where

end SerrePositivity.DifferentialGraded
