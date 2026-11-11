module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceAction
public import SerrePositivity.DifferentialGraded.Functor.Closed
public import SerrePositivity.KST.SConstruction.DGModuleExtensionRightUnitEvaluation
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGConjugationNaturality
/-!
概要：出発提示を保持する小模型の恒等入力作用を、全 Hom 上の厳密恒等と同定する。
方針：ラベル等号の評価を元の入力移送へ照合し、実延長の右単位則と全 Hom 自然性を使う。
規約：対象等号だけから関手等号を結論しない。一般の加群比較を同じ元の seed で使う。
使われ方：16時間試作の厳密関手性の恒等側の判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded _root_.SerrePositivity.KST.SConstruction
variable (R : Type u) [CommRing R] (D : Type u) [DGCategory R D] (κ : Cardinal.{u})

lemma dgKappaPresentedSourceObjectMap_id_valueIso (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) :
    eqToIso (congrArg (fun Y => ForgetEnrichment.of (Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ Y)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap_id R D κ X)) =
      dgModuleExtensionInputIso R (X.code.Objects R κ) D
        (strictDGFunctor_comp_id X.arrow)
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceSeed R D κ X)) := rfl

lemma dgKappaPresentedSourceAction_unitIso (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceActionIso R D D κ (DGFunctor.id D) X ≪≫
      eqToIso (congrArg (fun Y => ForgetEnrichment.of (Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ Y)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap_id R D κ X)) =
      dgModuleExtensionIdentityAt R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ X) := by
  apply Iso.ext
  rw [Iso.trans_hom, dgKappaPresentedSourceObjectMap_id_valueIso]
  exact dgModuleExtensionCompositionAt_comp_id R (X.code.Objects R κ) D X.arrow
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceSeed R D κ X))

lemma dgKappaPresentedSourceAction_id :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D D κ (DGFunctor.id D) =
      DGFunctor.id (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) := by
  refine inducedDGFunctor_ext_of_closed_conjugation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap_id R D κ) ?_
  intro X Y
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction_map, Category.assoc, enrichedClosedIsoConjugation_trans,
    dgKappaPresentedSourceAction_unitIso, dgKappaPresentedSourceAction_unitIso]
  apply enrichedConjugation_of_naturality (Complex R)
    (dgModuleExtensionIdentityAt R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ X))
    (dgModuleExtensionIdentityAt R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ Y)) _ (𝟙 _)
  simpa only [Category.id_comp, moduleHomPostcompose, moduleHomPrecompose] using
    dgModuleExtensionIdentityAt_naturality R D
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ Y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
