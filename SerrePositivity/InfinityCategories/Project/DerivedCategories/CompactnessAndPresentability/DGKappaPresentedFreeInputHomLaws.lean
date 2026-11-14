module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaPresentedFreeParameter
public import SerrePositivity.KST.SConstruction.DGModuleExtensionInputHomComposition
/-!
概要：自由表示の入力 Hom 作用が全次数の単位・合成を保つことを示す。
方針：元の加群延長の全 Hom 法則と、指定した閉同型の共役の法則を合成する。
規約：入力 Hom を閉零射へ制限しない。関手の後合成変数の厳密則とは区別する。
使われ方：16時間試作の dg 関手 nerve における豊穣作用の検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded _root_.SerrePositivity.KST.SConstruction
variable (R : Type u) [CommRing R] (D : Type v) (E : Type w)
  [DGCategory R D] [DGCategory R E] [Small.{u} D] [Small.{u} E] (κ : Cardinal.{u})

lemma dgKappaPresentedFreeInputHom_eq (F G : DGFunctor R D E)
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeInputHom R D E κ F G X =
      dgModuleExtensionInputHom R D E F G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R D κ X) ≫
        enrichedClosedIsoConjugation (Complex R)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeExtensionIso R D E F κ X)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeExtensionIso R D E G κ X) := rfl

lemma dgKappaPresentedFreeInputHom_identity (F : DGFunctor R D E)
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) :
    dgFunctorIdentity R D E F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeInputHom R D E κ F F X =
      eId (Complex R) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeAction R D E F κ).obj X) := by
  rw [dgKappaPresentedFreeInputHom_eq, ← Category.assoc, dgModuleExtensionInputHom_identity]
  exact enrichedClosedIsoConjugation_id (Complex R)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeExtensionIso R D E F κ X)

lemma dgKappaPresentedFreeInputHom_composition (F G H : DGFunctor R D E)
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) :
    dgFunctorComposition R D E F G H ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeInputHom R D E κ F H X =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeInputHom R D E κ F G X ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeInputHom R D E κ G H X) ≫
          eComp (Complex R) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeAction R D E F κ).obj X)
            ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeAction R D E G κ).obj X)
            ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeAction R D E H κ).obj X) := by
  change _ = _ ≫ eComp (Complex R)
    (ForgetEnrichment.of (Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R E κ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeObjectMap R F X)))
    (ForgetEnrichment.of (Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R E κ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeObjectMap R G X)))
    (ForgetEnrichment.of (Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R E κ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeObjectMap R H X)))
  rw [dgKappaPresentedFreeInputHom_eq, ← Category.assoc,
    dgModuleExtensionInputHom_composition]
  change ((_ ⊗ₘ _) ≫ eComp (Complex R)
    (ForgetEnrichment.of (Complex R)
      ((dgModuleExtension R D E F).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R D κ X)))
    (ForgetEnrichment.of (Complex R)
      ((dgModuleExtension R D E G).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R D κ X)))
    (ForgetEnrichment.of (Complex R)
      ((dgModuleExtension R D E H).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R D κ X)))) ≫ _ = _
  rw [dgKappaPresentedFreeInputHom_eq, dgKappaPresentedFreeInputHom_eq,
    ← tensorHom_comp_tensorHom_assoc, enrichedClosedIsoConjugation_comp]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
