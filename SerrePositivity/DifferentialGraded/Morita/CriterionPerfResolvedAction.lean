module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfResolvedHom

/-! # 射影的入力間の主 kernel 作用と、射影増強後の全 Hom 比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

def criterionPerfKernelMainAugmentation :
    moduleToDerived A D ⋙ kernelDerivedTensor A D E
        ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P)) ⟶
      (kernelTensor A D E P).onClosed ⋙ moduleToDerived A E :=
  whiskerLeft (moduleToDerived A D)
      (kernelDerivedTensorOnBimoduleIso A D E (BimoduleCategory.of A E D P)).hom ≫
    kernelDerivedTensorAugmentation A D E P

/-- 射影的入力に対する主作用の計算同型は、自然な増強から取る。 -/
def criterionPerfKernelProjectiveComputation (M : ModuleCategory A D)
    (hM : moduleHomotopicallyProjective A D M) :
    (kernelDerivedTensor A D E
        ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).obj
        ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj M) := by
  have := kernelDerivedTensorAugmentation_isIso_of_relativeKFlat A D E P M
    (moduleHomotopicallyProjective_relativeKFlat A D hM)
  have : IsIso ((criterionPerfKernelMainAugmentation A D E P).app M) := by
    dsimp only [criterionPerfKernelMainAugmentation, NatTrans.comp_app, whiskerLeft_app]
    infer_instance
  exact asIso ((criterionPerfKernelMainAugmentation A D E P).app M)

def criterionPerfKernelProjectiveActionMap {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : (moduleToDerived A D).obj M ⟶ (moduleToDerived A D).obj N) :
    (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj M) ⟶
      (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj N) :=
  (criterionPerfKernelProjectiveComputation A D E P M hM).inv ≫
    (kernelDerivedTensor A D E
      ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).map f ≫
    (criterionPerfKernelProjectiveComputation A D E P N hN).hom

lemma criterionPerfKernelProjectiveActionMap_closed {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) :
    criterionPerfKernelProjectiveActionMap A D E P hM hN ((moduleToDerived A D).map f) =
      (moduleToDerived A E).map ((kernelTensor A D E P).onClosed.map f) := by
  have h := (criterionPerfKernelMainAugmentation A D E P).naturality f
  exact (congrArg
    (fun k => (criterionPerfKernelProjectiveComputation A D E P M hM).inv ≫ k) h).trans
    (Iso.inv_hom_id_assoc (criterionPerfKernelProjectiveComputation A D E P M hM) _)

lemma criterionPerfResolvedAction_homology_zero {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (R : ModuleProjectiveResolution A E ((kernelTensor A D E P).onClosed.obj M))
    (f : (moduleToDerived A D).obj M ⟶ (moduleToDerived A D).obj N) :
    criterionPerfColumnDerivedHomEquiv A (RightModule A D) E (kernelTensor A D E P) M N R
        (criterionPerfKernelProjectiveActionMap A D E P hM hN f) =
      homologyMap (criterionPerfResolvedHomComparison A D E (kernelTensor A D E P) M N R) 0
        (moduleProjectiveDerivedHomologyEquiv A D hM N f) := by
  obtain ⟨g, hg⟩ := (moduleProjectiveDerivedHomEquiv A D hM N).surjective f
  obtain ⟨g, rfl⟩ := (moduleToHomotopy A D).map_surjective g
  rw [moduleProjectiveDerivedHomEquiv_map] at hg
  subst f
  rw [criterionPerfKernelProjectiveActionMap_closed, moduleProjectiveDerivedHomologyEquiv_map]
  exact criterionPerfHomComparison_homology_zero A (RightModule A D) E
    (kernelTensor A D E P) g R

lemma criterionPerfResolvedAction_quasiIsoAt_zero_iff {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (R : ModuleProjectiveResolution A E ((kernelTensor A D E P).onClosed.obj M)) :
    QuasiIsoAt (criterionPerfResolvedHomComparison A D E (kernelTensor A D E P) M N R) 0 ↔
      Function.Bijective
        ((kernelDerivedTensor A D E
          ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).map
          (X := (moduleToDerived A D).obj M) (Y := (moduleToDerived A D).obj N)) := by
  let eS := moduleProjectiveDerivedHomologyEquiv A D hM N
  let eT := criterionPerfColumnDerivedHomEquiv A (RightModule A D) E
    (kernelTensor A D E P) M N R
  let t := criterionPerfKernelProjectiveActionMap A D E P hM hN
  let a := homologyMap (criterionPerfResolvedHomComparison A D E (kernelTensor A D E P) M N R) 0
  have heq : eT ∘ t = a ∘ eS := funext (criterionPerfResolvedAction_homology_zero A D E P hM hN R)
  have ht : Function.Bijective t ↔ Function.Bijective a :=
    (Function.Bijective.of_comp_iff' eT.bijective t).symm.trans (by
      rw [heq]
      exact Function.Bijective.of_comp_iff a eS.bijective)
  have hm : Function.Bijective t ↔ Function.Bijective
      ((kernelDerivedTensor A D E
        ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).map
        (X := (moduleToDerived A D).obj M) (Y := (moduleToDerived A D).obj N)) :=
    Function.Bijective.of_comp_iff'
      (Iso.homCongr (criterionPerfKernelProjectiveComputation A D E P M hM)
        (criterionPerfKernelProjectiveComputation A D E P N hN)).bijective _
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  exact ht.symm.trans hm

/-- 全 Hom 比較の擬同型性は、全ての源 shift 上での主作用の射の全単射性に一致する。 -/
lemma criterionPerfResolvedAction_quasiIso_iff_sourceShifts {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (R : ModuleProjectiveResolution A E ((kernelTensor A D E P).onClosed.obj M)) :
    QuasiIso (criterionPerfResolvedHomComparison A D E (kernelTensor A D E P) M N R) ↔
      ∀ s : ℤ, Function.Bijective
        ((kernelDerivedTensor A D E
          ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).map
          (X := (moduleToDerived A D).obj (M⟦s⟧)) (Y := (moduleToDerived A D).obj N)) := by
  rw [criterionPerfResolvedHomComparison_quasiIso_iff_shifts]
  apply forall_congr'
  intro s
  exact criterionPerfResolvedAction_quasiIsoAt_zero_iff A D E P
    (moduleHomotopicallyProjective_shift A D hM s) hN _

end SerrePositivity.DifferentialGraded.Morita
