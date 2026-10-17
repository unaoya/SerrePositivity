module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleHom
public import SerrePositivity.DifferentialGraded.Module.HomFunctor

/-! # 実際のHom係数変更比較の閉零射に関する両変数自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarModuleHom_precompose {M N : ModuleCategory A D} (f : M ⟶ N)
    (P : ModuleCategory A D) :
    (ScalarExtension.extension φ).map (eHomWhiskerRight (Complex A) f P) ≫
        scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
          (ForgetEnrichment.to (Complex A) P) =
      scalarModuleHom φ D (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) P) ≫
        eHomWhiskerRight (Complex A') ((ScalarExtension.moduleExtension φ D).map f)
          ((ScalarExtension.moduleExtension φ D).obj P) := by
  apply moduleHom_ext
  intro x
  let L := ScalarExtension.extension φ
  let F := ScalarExtension.moduleExtension φ D
  let π := moduleHomπ A D
  let c := ScalarExtension.homComparison φ
  let s (X Y : ModuleCategory A D) := scalarModuleHom φ D
    (ForgetEnrichment.to (Complex A) X) (ForgetEnrichment.to (Complex A) Y)
  have hr := moduleHomWhiskerRight_π A' (ScalarExtension.DGBaseChange φ D)
    (P := F.obj P) (F.map f) x
  rw [ScalarExtension.moduleExtension_eval] at hr
  have hπM := scalarModuleHom_π φ D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) P) x
  have hπN := scalarModuleHom_π φ D (ForgetEnrichment.to (Complex A) N)
    (ForgetEnrichment.to (Complex A) P) x
  calc
    _ = L.map (eHomWhiskerRight (Complex A) f P) ≫
        (L.map (π (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) P) x) ≫
          c ((moduleEvaluation A D x).obj M) ((moduleEvaluation A D x).obj P)) := by
      rw [Category.assoc]
      exact congrArg (fun k => L.map (eHomWhiskerRight (Complex A) f P) ≫ k) hπM
    _ = L.map (π (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) P) x) ≫
        c ((moduleEvaluation A D x).obj N) ((moduleEvaluation A D x).obj P) ≫
          homPrecompose (L.map ((moduleEvaluation A D x).map f))
            (L.obj ((moduleEvaluation A D x).obj P)) := by
      rw [← CategoryTheory.Functor.map_comp_assoc, moduleHomWhiskerRight_π,
        CategoryTheory.Functor.map_comp, Category.assoc]
      exact congrArg (fun k => L.map (π (ForgetEnrichment.to (Complex A) N)
        (ForgetEnrichment.to (Complex A) P) x) ≫ k)
        (ScalarExtension.homComparison_precompose φ ((moduleEvaluation A D x).map f) _)
    _ = _ := by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ homPrecompose (L.map ((moduleEvaluation A D x).map f))
          (L.obj ((moduleEvaluation A D x).obj P))) hπN.symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun k => s N P ≫ k) hr.symm).trans (Category.assoc _ _ _).symm)))

lemma scalarModuleHom_postcompose (M : ModuleCategory A D) {N P : ModuleCategory A D}
    (f : N ⟶ P) :
    (ScalarExtension.extension φ).map (eHomWhiskerLeft (Complex A) M f) ≫
        scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
          (ForgetEnrichment.to (Complex A) P) =
      scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) ≫
        eHomWhiskerLeft (Complex A') ((ScalarExtension.moduleExtension φ D).obj M)
          ((ScalarExtension.moduleExtension φ D).map f) := by
  apply moduleHom_ext
  intro x
  let L := ScalarExtension.extension φ
  let F := ScalarExtension.moduleExtension φ D
  let π := moduleHomπ A D
  let c := ScalarExtension.homComparison φ
  let s (X Y : ModuleCategory A D) := scalarModuleHom φ D
    (ForgetEnrichment.to (Complex A) X) (ForgetEnrichment.to (Complex A) Y)
  have hr := moduleHomWhiskerLeft_π A' (ScalarExtension.DGBaseChange φ D)
    (M := F.obj M) (F.map f) x
  rw [ScalarExtension.moduleExtension_eval] at hr
  have hπP := scalarModuleHom_π φ D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) P) x
  have hπN := scalarModuleHom_π φ D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N) x
  calc
    _ = L.map (eHomWhiskerLeft (Complex A) M f) ≫
        (L.map (π (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) P) x) ≫
          c ((moduleEvaluation A D x).obj M) ((moduleEvaluation A D x).obj P)) := by
      rw [Category.assoc]
      exact congrArg (fun k => L.map (eHomWhiskerLeft (Complex A) M f) ≫ k) hπP
    _ = L.map (π (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) x) ≫
        c ((moduleEvaluation A D x).obj M) ((moduleEvaluation A D x).obj N) ≫
          homPostcompose (L.obj ((moduleEvaluation A D x).obj M))
            (L.map ((moduleEvaluation A D x).map f)) := by
      rw [← CategoryTheory.Functor.map_comp_assoc, moduleHomWhiskerLeft_π,
        CategoryTheory.Functor.map_comp, Category.assoc]
      exact congrArg (fun k => L.map (π (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N) x) ≫ k)
        (ScalarExtension.homComparison_postcompose φ _ ((moduleEvaluation A D x).map f))
    _ = _ := by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ homPostcompose (L.obj ((moduleEvaluation A D x).obj M))
          (L.map ((moduleEvaluation A D x).map f))) hπN.symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun k => s M N ≫ k) hr.symm).trans (Category.assoc _ _ _).symm)))

end SerrePositivity.DifferentialGraded
