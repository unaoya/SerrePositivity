module
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGModuleExtensionComposition
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGConjugationNaturality
/-!
概要：元の実 dg 加群延長の合成比較を、全 Hom の共役等式として公開する。
方針：合成比較の元の全 Hom 自然性へ、一般の閉共役判定を適用する。
規約：任意の実右加群で使え、全加群型の Small 性を必要としない。
使われ方：表示模型で巨大な評価式を展開せず、実延長の合成則を適用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.KST.SConstruction
variable (R : Type u) [CommRing R] (D : Type v) (E : Type w) (B : Type z)
  [DGCategory R D] [DGCategory R E] [DGCategory R B]
  [Small.{u} D] [Small.{u} E] [Small.{u} B]
  (F : DGFunctor R D E) (G : DGFunctor R E B) (M N : RightModule R D)

lemma dgModuleExtensionComposition_conjugation :
    (dgModuleExtension R D E F).map M N ≫
      (dgModuleExtension R E B G).map ((dgModuleExtension R D E F).obj M)
        ((dgModuleExtension R D E F).obj N) ≫
      enrichedClosedIsoConjugation (Complex R)
        (dgModuleExtensionCompositionAt R D E B F G M)
        (dgModuleExtensionCompositionAt R D E B F G N) =
    (dgModuleExtension R D B (F.comp G)).map M N := by
  rw [← Category.assoc]
  apply enrichedConjugation_of_naturality (Complex R)
    (dgModuleExtensionCompositionAt R D E B F G M)
    (dgModuleExtensionCompositionAt R D E B F G N)
  simpa only [moduleHomPostcompose, moduleHomPrecompose, DGFunctor.comp,
    EnrichedFunctor.comp] using
    dgModuleExtensionCompositionAt_naturality R D E B F G M N

end SerrePositivity.DifferentialGraded
