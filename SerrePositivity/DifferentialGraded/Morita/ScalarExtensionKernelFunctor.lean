module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernel
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomNaturality
public import SerrePositivity.DifferentialGraded.Bimodule.LeftEvaluation
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionLeftMaps

/-! # 通常kernelの全Hom自然な閉零射の係数変更 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 係数変更した右加群射の族は左Dの全Hom作用と可換する。 -/
def scalarKernelMap {P Q : BimoduleCategory A E D} (f : P ⟶ Q) :
    BimoduleCategory.of A' (DGBaseChange φ E) (DGBaseChange φ D)
        (scalarKernel φ D E (BimoduleCategory.underlying A E D P)) ⟶
      BimoduleCategory.of A' (DGBaseChange φ E) (DGBaseChange φ D)
        (scalarKernel φ D E (BimoduleCategory.underlying A E D Q)) :=
  ⟨fun d => (moduleExtension φ E).map (f.val d), by
    intro d d'
    change D at d
    change D at d'
    change (extension φ).map ((BimoduleCategory.underlying A E D P).toFunctor.map d d') ≫
        scalarModuleHom φ E _ _ ≫ eHomWhiskerLeft (Complex A') _
          ((moduleExtension φ E).map (f.val d')) =
      (extension φ).map ((BimoduleCategory.underlying A E D Q).toFunctor.map d d') ≫
        scalarModuleHom φ E _ _ ≫ eHomWhiskerRight (Complex A')
          ((moduleExtension φ E).map (f.val d)) _
    erw [← scalarModuleHom_postcompose φ E
      (ForgetEnrichment.of (Complex A) ((BimoduleCategory.underlying A E D P).rightAt d))
      (f.val d')]
    rw [← CategoryTheory.Functor.map_comp_assoc]
    change (extension φ).map
        ((BimoduleCategory.underlying A E D P).toFunctor.map d d' ≫
          moduleHomPostcompose A E _ _ _ (f.val d')) ≫ _ = _
    rw [f.property, CategoryTheory.Functor.map_comp, Category.assoc]
    exact congrArg (fun k => (extension φ).map
      ((BimoduleCategory.underlying A E D Q).toFunctor.map d d') ≫ k)
        (scalarModuleHom_precompose φ E (f.val d) _)
  ⟩

def scalarKernelFunctor : BimoduleCategory A E D ⥤
    BimoduleCategory A' (DGBaseChange φ E) (DGBaseChange φ D) where
  obj P := BimoduleCategory.of A' (DGBaseChange φ E) (DGBaseChange φ D)
    (scalarKernel φ D E (BimoduleCategory.underlying A E D P))
  map f := scalarKernelMap φ D E f
  map_id P := by
    apply Subtype.ext
    funext d
    exact (moduleExtension φ E).map_id _
  map_comp f g := by
    apply Subtype.ext
    funext d
    exact (moduleExtension φ E).map_comp (f.val d) (g.val d)

lemma scalarKernelMap_value {P Q : BimoduleCategory A E D} (f : P ⟶ Q)
    (e : E) (d : D) :
    (BimoduleCategory.valueEvaluation A' (DGBaseChange φ E) (DGBaseChange φ D) e d).map
        (scalarKernelMap φ D E f) =
      (extension φ).map ((BimoduleCategory.valueEvaluation A E D e d).map f) :=
  moduleExtension_eval φ E (f.val d) e

variable [Small.{u} D]

/-- 左評価と通常kernelの係数変更は、kernel射にも自然に交換する。 -/
def scalarKernelLeftEvaluationIso (e : E) :
    scalarKernelFunctor φ D E ⋙
        BimoduleCategory.leftEvaluation A' (DGBaseChange φ E) (DGBaseChange φ D) e ≅
      BimoduleCategory.leftEvaluation A E D e ⋙ leftModuleExtension φ D :=
  NatIso.ofComponents
    (fun P => eqToIso (congrArg (ForgetEnrichment.of (Complex A'))
      (scalarKernel_leftAt φ D E (BimoduleCategory.underlying A E D P) e)))
    (by
      intro P Q f
      apply leftModuleMorphism_ext A' (DGBaseChange φ D)
      intro d
      simp only [CategoryTheory.Functor.map_comp, eqToIso.hom, eqToHom_map,
        eqToHom_refl]
      erw [Category.id_comp, Category.comp_id]
      change (leftModuleEvaluation A' (DGBaseChange φ D) d).map
          ((BimoduleCategory.leftEvaluation A' (DGBaseChange φ E)
            (DGBaseChange φ D) e).map (scalarKernelMap φ D E f)) =
        (leftModuleEvaluation A' (DGBaseChange φ D) d).map
          ((leftModuleExtension φ D).map ((BimoduleCategory.leftEvaluation A E D e).map f))
      rw [BimoduleCategory.leftEvaluation_map_eval, scalarKernelMap_value,
        leftModuleExtension_eval, BimoduleCategory.leftEvaluation_map_eval])

end SerrePositivity.DifferentialGraded.Morita
