module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionTripleTensorSteps
public import SerrePositivity.KST.SConstruction.DGTripleComparisonPasting

/-! # 元の実延長の三重 tensor 比較
概要：元の実延長の三重比較の二経路を、入力結合等号を保って照合する。
方針：元の graph 結合則を tensor 作用へ送り、二つの逆自然性と逆五角を合成する。
規約：大きい全加群型の smallness を要求しない。使われ方：実延長の三重比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z q
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z) (U : Type q)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T] [DGCategory A U] [Small.{u} U]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (H : DGFunctor A T U)
local notation "P" => functorGraph A T U H
local notation "Q" => functorGraph A E T G
local notation "R" => functorGraph A D E F
local notation "S" => DGFunctor.id (RightModule A D)

/-- 元の実延長の三重比較は、全加群上の同じ tensor 射として両立する。 -/
lemma dgModuleExtensionCompositionTensorIso_assoc :
    BimoduleTensor.composeMap A U T (RightModule A D) (𝟙 (BimoduleCategory.of A U T P))
        (dgModuleExtensionCompositionTensorIso A D E T F G).hom ≫
      (dgModuleExtensionCompositionTensorIso A D T U (F.comp G) H).hom ≫
      (dgModuleGraphTensorFunctor A D U).map
        (dgFunctorGraphInputIso A D U (strictDGFunctor_comp_assoc F G H)).hom =
    (BimoduleTensor.associatorIso A U T E (RightModule A D) P Q
        (dgModuleExtension A D E F)).inv ≫
      BimoduleTensor.composeMap A U E (RightModule A D)
        (dgFunctorGraphCompositionIso A E T U G H).hom
        (𝟙 (BimoduleCategory.of A E (RightModule A D) (dgModuleExtension A D E F))) ≫
      (dgModuleExtensionCompositionTensorIso A D E U F (G.comp H)).hom := by
  exact dgTripleComparison_pasting (dgModuleGraphTensorFunctor A D U)
    (BimoduleTensor.composeMap A U T D (𝟙 (BimoduleCategory.of A U T P))
      (dgFunctorGraphCompositionIso A D E T F G).hom)
    (dgFunctorGraphCompositionIso A D T U (F.comp G) H).hom
    (dgFunctorGraphInputIso A D U (strictDGFunctor_comp_assoc F G H)).hom
    (BimoduleTensor.associatorIso A U T E D P Q R).inv
    (BimoduleTensor.composeMap A U E D (dgFunctorGraphCompositionIso A E T U G H).hom
      (𝟙 (BimoduleCategory.of A E D R)))
    (dgFunctorGraphCompositionIso A D E U F (G.comp H)).hom
    (BimoduleTensor.composeMap A U T (RightModule A D) (𝟙 (BimoduleCategory.of A U T P))
      (BimoduleTensor.associatorIso A T E D (RightModule A D) Q R S).inv)
    (BimoduleTensor.composeMap A U T (RightModule A D) (𝟙 (BimoduleCategory.of A U T P))
      ((dgModuleGraphTensorFunctor A D T).map
        (dgFunctorGraphCompositionIso A D E T F G).hom))
    (BimoduleTensor.associatorIso A U T D (RightModule A D) P
      (functorGraph A D T (F.comp G)) S).inv
    (BimoduleTensor.associatorIso A U T D (RightModule A D) P
      (BimoduleTensor.compose A T E D Q R) S).inv
    (BimoduleTensor.associatorIso A U T E (RightModule A D) P Q
      (dgModuleExtension A D E F)).inv
    (BimoduleTensor.associatorIso A U E D (RightModule A D)
      (BimoduleTensor.compose A U T E P Q) R S).inv
    (BimoduleTensor.composeMap A U E (RightModule A D)
      (dgFunctorGraphCompositionIso A E T U G H).hom
      (𝟙 (BimoduleCategory.of A E (RightModule A D) (dgModuleExtension A D E F))))
    (BimoduleTensor.associatorIso A U E D (RightModule A D)
      (functorGraph A E U (G.comp H)) R S).inv
    (BimoduleTensor.composeMap A U T (RightModule A D) (𝟙 (BimoduleCategory.of A U T P))
      (dgModuleExtensionCompositionTensorIso A D E T F G).hom)
    (dgModuleExtensionCompositionTensorIso A D T U (F.comp G) H).hom
    (dgModuleExtensionCompositionTensorIso A D E U F (G.comp H)).hom
    (dgModuleExtensionTriple_inner_expansion A D E T U F G H) rfl rfl
    (dgModuleExtensionTriple_graph_inverse A D E T U F G H)
    (dgModuleExtensionTriple_inner_naturality A D E T U F G H)
    (dgModuleExtensionTriple_inverse_pentagon A D E T U F G H)
    (dgModuleExtensionTriple_outer_naturality A D E T U F G H)


end SerrePositivity.KST.SConstruction
