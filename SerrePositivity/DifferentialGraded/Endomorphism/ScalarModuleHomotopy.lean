module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarClosedMap
public import SerrePositivity.DifferentialGraded.Module.Homotopy

/-! # 実際の係数拡大による全dg自然な加群ホモトピーの保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarModuleHom_cycle {M N : ModuleCategory A D} (f : M ⟶ N) :
    let := φ.toAlgebra
    (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)).f 0
        ((1 : A') ⊗ₜ[A] (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A')
        ((ScalarExtension.moduleExtension φ D).map f))).val := by
  let := φ.toAlgebra
  have h := congrArg (fun k => (cycleFromUnit _ k).val) (scalarModuleHom_closedMap φ D f)
  change (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)).f 0
    (((ScalarExtension.extension φ).map (ForgetEnrichment.homTo (Complex A) f)).f 0
      ((ScalarExtension.unitIso φ).inv.f 0
        ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A'))).inv (1 : A')))) = _ at h
  erw [ScalarExtension.sphereIso_inv_one φ 0, ModuleCat.ExtendScalars.map_tmul φ] at h
  exact h

/-- 次数−1のHom end要素を係数変更する。各値だけのホモトピーには弱めない。 -/
def scalarModuleHomotopy {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ModuleHomotopy A D f g) :
    ModuleHomotopy A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).map f)
      ((ScalarExtension.moduleExtension φ D).map g) := by
  let := φ.toAlgebra
  let s := scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N)
  refine ⟨s.f (-1) ((1 : A') ⊗ₜ[A] h.val), ?_⟩
  have hc := congrArg (fun k => k ((1 : A') ⊗ₜ[A] h.val)) (s.comm (-1) 0)
  change _ = s.f 0 ((ModuleCat.extendScalars φ).map
    ((homObject A (RightModule A D) M N).d (-1) 0) ((1 : A') ⊗ₜ[A] h.val)) at hc
  erw [ModuleCat.ExtendScalars.map_tmul φ] at hc
  change (moduleHom A' (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.rightModule φ D (ForgetEnrichment.to (Complex A) M))
      (ScalarExtension.rightModule φ D (ForgetEnrichment.to (Complex A) N))).d (-1) 0
      (s.f (-1) ((1 : A') ⊗ₜ[A] h.val)) = _ at hc
  calc
    _ = s.f 0 ((1 : A') ⊗ₜ[A]
        ((homObject A (RightModule A D) M N).d (-1) 0 h.val)) := hc
    _ = _ := by
      rw [h.property, TensorProduct.tmul_sub, map_sub]
      exact congrArg₂ (fun a b => a - b) (scalarModuleHom_cycle φ D f)
        (scalarModuleHom_cycle φ D g)

/-- 実際の加群係数拡大を全dg自然なホモトピーの商へ降ろす。 -/
def scalarModuleExtensionHomotopy : ModuleHomotopyCategory A D ⥤
    ModuleHomotopyCategory A' (ScalarExtension.DGBaseChange φ D) :=
  CategoryTheory.Quotient.lift _ (ScalarExtension.moduleExtension φ D ⋙
    moduleToHomotopy A' (ScalarExtension.DGBaseChange φ D)) (by
      intro M N f g hb
      obtain ⟨h⟩ := (moduleHomotopy_nonempty_iff A D f g).2 hb
      exact (moduleToHomotopy_map_eq_iff A' (ScalarExtension.DGBaseChange φ D) _ _).2
        ⟨scalarModuleHomotopy φ D h⟩)

lemma scalarModuleExtensionHomotopy_fac :
    moduleToHomotopy A D ⋙ scalarModuleExtensionHomotopy φ D =
      ScalarExtension.moduleExtension φ D ⋙
        moduleToHomotopy A' (ScalarExtension.DGBaseChange φ D) :=
  CategoryTheory.Quotient.lift_spec _ _ _

end SerrePositivity.DifferentialGraded
