module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaPresentedSourceCompositionIso
public import SerrePositivity.DifferentialGraded.Functor.Closed

public import SerrePositivity.DifferentialGraded.SharedFunctoriality.ModuleExtensionConjugation
/-!
概要：小さい出発提示模型の作用が、全 Hom を含めて入力の合成を厳密に保つことを示す。
方針：元の三重比較と全 Hom 自然性を、任意ラベル族の一般の共役貼り合わせへ渡す。
規約：表示の再選択・導来同型・対象等号だけで関手等号を代用しない。
使われ方：16時間試作の厳密関手性の合成側の判定。
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

lemma dgKappaPresentedSourceAction_comp :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D E κ F).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R E B κ G) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D B κ (F.comp G) := by
  refine inducedDGFunctor_ext_of_closed_conjugation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R B κ)
    (fun X => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap_comp R D κ E F B G X).symm) ?_
  intro X Y
  let tX := eqToIso (congrArg (fun Z => ForgetEnrichment.of (Complex R)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R B κ Z))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap_comp R D κ E F B G X).symm)
  let tY := eqToIso (congrArg (fun Z => ForgetEnrichment.of (Complex R)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R B κ Z))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap_comp R D κ E F B G Y).symm)
  have hn := dgModuleExtensionComposition_conjugation R D E B F G
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ Y)
  have hp := dgFunctor_conjugation_pasting R (dgModuleExtension R E B G)
    ((dgModuleExtension R D E F).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ Y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceActionIso R D E κ F X)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceActionIso R D E κ F Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceActionIso R E B κ G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap R D κ E F X))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceActionIso R E B κ G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap R D κ E F Y))
    tX tY
    (dgModuleExtensionCompositionAt R D E B F G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ X))
    (dgModuleExtensionCompositionAt R D E B F G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ Y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceActionIso R D B κ (F.comp G) X)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceActionIso R D B κ (F.comp G) Y)
    ((dgModuleExtension R D B (F.comp G)).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ Y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction_compositionIso R D E B κ F G X)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction_compositionIso R D E B κ F G Y) hn
  change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D E κ F).map X Y ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R E B κ G).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap R D κ E F X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap R D κ E F Y)) ≫
      enrichedClosedIsoConjugation (Complex R) tX tY = _
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction_map, Category.assoc,
    ForgetEnrichment.to_of] using hp

end SerrePositivity.InfinityCategories.Project.DerivedCategories
