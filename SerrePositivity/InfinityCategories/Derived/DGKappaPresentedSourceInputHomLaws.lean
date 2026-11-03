module
public import SerrePositivity.InfinityCategories.Derived.DGKappaPresentedSourceParameter
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded SerrePositivity.KST.SConstruction
variable (R : Type u) [CommRing R] (D E : Type u)
  [DGCategory R D] [DGCategory R E] (κ : Cardinal.{u})

lemma dgKappaPresentedSourceInputHom_eq (F G : DGFunctor R D E)
    (X : DGKappaPresentedSourceObject R D κ) :
    dgKappaPresentedSourceInputHom R D E κ F G X =
      dgModuleExtensionInputHom R D E F G (dgKappaPresentedSourceValue R D κ X) ≫
        enrichedClosedIsoConjugation (Complex R)
          (dgKappaPresentedSourceActionIso R D E κ F X)
          (dgKappaPresentedSourceActionIso R D E κ G X) := rfl

lemma dgKappaPresentedSourceInputHom_identity (F : DGFunctor R D E)
    (X : DGKappaPresentedSourceObject R D κ) :
    dgFunctorIdentity R D E F ≫ dgKappaPresentedSourceInputHom R D E κ F F X =
      eId (Complex R) ((dgKappaPresentedSourceAction R D E κ F).obj X) := by
  rw [dgKappaPresentedSourceInputHom_eq, ← Category.assoc, dgModuleExtensionInputHom_identity]
  exact enrichedClosedIsoConjugation_id (Complex R)
    (dgKappaPresentedSourceActionIso R D E κ F X)

lemma dgKappaPresentedSourceInputHom_composition (F G H : DGFunctor R D E)
    (X : DGKappaPresentedSourceObject R D κ) :
    dgFunctorComposition R D E F G H ≫ dgKappaPresentedSourceInputHom R D E κ F H X =
      (dgKappaPresentedSourceInputHom R D E κ F G X ⊗ₘ
        dgKappaPresentedSourceInputHom R D E κ G H X) ≫
          eComp (Complex R) ((dgKappaPresentedSourceAction R D E κ F).obj X)
            ((dgKappaPresentedSourceAction R D E κ G).obj X)
            ((dgKappaPresentedSourceAction R D E κ H).obj X) := by
  change _ = _ ≫ eComp (Complex R)
    (ForgetEnrichment.of (Complex R)
      (dgKappaPresentedSourceValue R E κ (dgKappaPresentedSourceObjectMap R D κ E F X)))
    (ForgetEnrichment.of (Complex R)
      (dgKappaPresentedSourceValue R E κ (dgKappaPresentedSourceObjectMap R D κ E G X)))
    (ForgetEnrichment.of (Complex R)
      (dgKappaPresentedSourceValue R E κ (dgKappaPresentedSourceObjectMap R D κ E H X)))
  have h := enrichedClosedIsoConjugation_preserves_tensor_composition R
    (dgKappaPresentedSourceActionIso R D E κ F X)
    (dgKappaPresentedSourceActionIso R D E κ G X)
    (dgKappaPresentedSourceActionIso R D E κ H X)
    (dgFunctorComposition R D E F G H)
    (dgModuleExtensionInputHom R D E F G (dgKappaPresentedSourceValue R D κ X))
    (dgModuleExtensionInputHom R D E G H (dgKappaPresentedSourceValue R D κ X))
    (dgModuleExtensionInputHom R D E F H (dgKappaPresentedSourceValue R D κ X))
    (dgModuleExtensionInputHom_composition R D E F G H
      (dgKappaPresentedSourceValue R D κ X))
  simpa only [dgKappaPresentedSourceInputHom_eq] using h

end SerrePositivity.InfinityCategories
