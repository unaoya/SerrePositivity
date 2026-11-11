module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceParameter
public import SerrePositivity.KST.SConstruction.DGModuleExtensionInputHomComposition
public import SerrePositivity.DifferentialGraded.Functor.Closed
/-!
概要：出発提示表示の入力 Hom 作用が全次数の単位・合成を保つことを示す。
方針：元の加群延長の全 Hom 法則と、指定した閉同型の共役の法則を合成する。
規約：入力 Hom を閉零射へ制限しない。関手の後合成変数の厳密則とは区別する。
使われ方：16時間試作の dg 関手 nerve における豊穣作用の検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded _root_.SerrePositivity.KST.SConstruction
variable (R : Type u) [CommRing R] (D E : Type u)
  [DGCategory R D] [DGCategory R E] (κ : Cardinal.{u})

lemma dgKappaPresentedSourceInputHom_eq (F G : DGFunctor R D E)
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceInputHom R D E κ F G X =
      dgModuleExtensionInputHom R D E F G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ X) ≫
        enrichedClosedIsoConjugation (Complex R)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceActionIso R D E κ F X)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceActionIso R D E κ G X) := rfl

lemma dgKappaPresentedSourceInputHom_identity (F : DGFunctor R D E)
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) :
    dgFunctorIdentity R D E F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceInputHom R D E κ F F X =
      eId (Complex R) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D E κ F).obj X) := by
  rw [dgKappaPresentedSourceInputHom_eq, ← Category.assoc, dgModuleExtensionInputHom_identity]
  exact enrichedClosedIsoConjugation_id (Complex R)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceActionIso R D E κ F X)

lemma dgKappaPresentedSourceInputHom_composition (F G H : DGFunctor R D E)
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) :
    dgFunctorComposition R D E F G H ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceInputHom R D E κ F H X =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceInputHom R D E κ F G X ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceInputHom R D E κ G H X) ≫
          eComp (Complex R) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D E κ F).obj X)
            ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D E κ G).obj X)
            ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D E κ H).obj X) := by
  change _ = _ ≫ eComp (Complex R)
    (ForgetEnrichment.of (Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R E κ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap R D κ E F X)))
    (ForgetEnrichment.of (Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R E κ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap R D κ E G X)))
    (ForgetEnrichment.of (Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R E κ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap R D κ E H X)))
  have h := enrichedClosedIsoConjugation_preserves_tensor_composition R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceActionIso R D E κ F X)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceActionIso R D E κ G X)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceActionIso R D E κ H X)
    (dgFunctorComposition R D E F G H)
    (dgModuleExtensionInputHom R D E F G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ X))
    (dgModuleExtensionInputHom R D E G H (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ X))
    (dgModuleExtensionInputHom R D E F H (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ X))
    (dgModuleExtensionInputHom_composition R D E F G H
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ X))
  simpa only [dgKappaPresentedSourceInputHom_eq] using h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
