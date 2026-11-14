module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaPresentedSourceAction
public import SerrePositivity.KST.SConstruction.DGModuleExtensionTripleEvaluation
/-!
概要：出発提示模型の二回の作用比較を、同じ実延長の三重比較と照合する。
方針：同じ提示・seed で元の結合式を評価し、ラベル等号の移送を残す。
規約：入力関手の結合等号を捨てない。関手等号への昇格は全 Hom 比較で行う。
使われ方：16時間試作の厳密合成則に必要な評価比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded _root_.SerrePositivity.KST.SConstruction
variable (R : Type u) [CommRing R] (D E B : Type u)
  [DGCategory R D] [DGCategory R E] [DGCategory R B] (κ : Cardinal.{u})
  (F : DGFunctor R D E) (G : DGFunctor R E B)

lemma dgKappaPresentedSourceObjectMap_comp_valueIso (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) :
    eqToIso (congrArg (fun Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R B κ =>
      ForgetEnrichment.of (Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R B κ Y))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap_comp R D κ E F B G X).symm) =
      dgModuleExtensionInputIso R (X.code.Objects R κ) B
        (strictDGFunctor_comp_assoc X.arrow F G)
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceSeed R D κ X)) := rfl

lemma dgKappaPresentedSourceAction_compositionIso (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) :
    (dgModuleExtension R E B G).onClosed.mapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceActionIso R D E κ F X) ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceActionIso R E B κ G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap R D κ E F X) ≪≫
      eqToIso (congrArg (fun Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R B κ =>
      ForgetEnrichment.of (Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R B κ Y))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap_comp R D κ E F B G X).symm) =
      dgModuleExtensionCompositionAt R D E B F G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ X) ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceActionIso R D B κ (F.comp G) X := by
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [dgKappaPresentedSourceObjectMap_comp_valueIso]
  exact dgModuleExtensionCompositionAt_assoc R (X.code.Objects R κ) D E B X.arrow F G
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceSeed R D κ X))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
