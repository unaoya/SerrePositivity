module
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGModuleExtensionComposition
public import SerrePositivity.KST.SConstruction.BimoduleFirstParameterConjugation

/-! # 元の実加群延長の合成比較の同じ二段分解
概要：元の合成比較は、逆結合比較と graph 比較の実 tensor 像の合成である。
方針：元の双加群同型の定義を評価し、同じ閉零同型を回収する。
規約：新しい比較を選ばない。使われ方：全パラメータ入力作用の比較共役。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T]

/-- 元の実合成比較を、同じ逆結合比較と同じ tensor graph 比較に分解する。 -/
lemma dgModuleExtensionCompositionAt_factor (F : DGFunctor A D E) (G : DGFunctor A E T)
    (M : RightModule A D) :
    dgModuleExtensionCompositionAt A D E T F G M =
      (BimoduleTensor.associatorRightModuleIso A T E D (RightModule A D)
          (functorGraph A E T G) (functorGraph A D E F) (DGFunctor.id _) M).symm ≪≫
        bimoduleFirstTensorIsoAt A T D (RightModule A D) (DGFunctor.id _)
          (dgFunctorGraphCompositionIso A D E T F G) M := by
  apply Iso.ext
  simp only [dgModuleExtensionCompositionAt, dgModuleExtensionCompositionTensorIso,
    Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, BimoduleTensor.associatorIso_inv_eval]
  rfl

end SerrePositivity.KST.SConstruction
