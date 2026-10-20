module
public import SerrePositivity.KST.SConstruction.DGTensorInverseCoherence
public import SerrePositivity.KST.SConstruction.DGFunctorGraphAssociativity
public import SerrePositivity.KST.SConstruction.DGModuleExtensionComposition

/-! # 実延長の三重比較を tensor の自然性と五角へ分解する
概要：元の graph と恒等加群に対する逆向きの tensor coherence を固定する。
方針：graph の結合則、元の逆結合の自然性、元の五角を特殊化する。
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

omit [Small.{u} D] in
/-- 元の graph 結合則を、実延長で使う逆結合から始まる式へ移す。 -/
lemma dgModuleExtensionTriple_graph_inverse :
    BimoduleTensor.composeMap A U T D (𝟙 (BimoduleCategory.of A U T P))
        (dgFunctorGraphCompositionIso A D E T F G).hom ≫
      (dgFunctorGraphCompositionIso A D T U (F.comp G) H).hom ≫
      (dgFunctorGraphInputIso A D U (strictDGFunctor_comp_assoc F G H)).hom =
    (BimoduleTensor.associatorIso A U T E D P Q R).inv ≫
      BimoduleTensor.composeMap A U E D (dgFunctorGraphCompositionIso A E T U G H).hom
        (𝟙 (BimoduleCategory.of A E D R)) ≫
      (dgFunctorGraphCompositionIso A D E U F (G.comp H)).hom :=
  dgIso_move_hom_left (BimoduleTensor.associatorIso A U T E D P Q R) _ _
    (dgFunctorGraphCompositionIso_assoc A D E T U F G H)

/-- 内側の graph 比較は、元の逆結合の三変数自然性に従う。 -/
@[reassoc]
lemma dgModuleExtensionTriple_inner_naturality :
    BimoduleTensor.composeMap A U T (RightModule A D) (𝟙 (BimoduleCategory.of A U T P))
        ((dgModuleGraphTensorFunctor A D T).map
          (dgFunctorGraphCompositionIso A D E T F G).hom) ≫
      (BimoduleTensor.associatorIso A U T D (RightModule A D) P
        (functorGraph A D T (F.comp G)) S).inv =
    (BimoduleTensor.associatorIso A U T D (RightModule A D) P
        (BimoduleTensor.compose A T E D Q R) S).inv ≫
      (dgModuleGraphTensorFunctor A D U).map
        (BimoduleTensor.composeMap A U T D (𝟙 (BimoduleCategory.of A U T P))
          (dgFunctorGraphCompositionIso A D E T F G).hom) := by
  change BimoduleTensor.composeMap A U T (RightModule A D)
    (𝟙 (BimoduleCategory.of A U T P))
    (BimoduleTensor.composeMap A T D (RightModule A D)
      (dgFunctorGraphCompositionIso A D E T F G).hom
      (𝟙 (BimoduleCategory.of A D (RightModule A D) S))) ≫ _ = _
  exact dgTensor_associator_inv_naturality A U T D (RightModule A D)
    (𝟙 (BimoduleCategory.of A U T P)) (dgFunctorGraphCompositionIso A D E T F G).hom
    (𝟙 (BimoduleCategory.of A D (RightModule A D) S))

/-- 外側の graph 比較は、同じ元の逆結合の自然性に従う。 -/
@[reassoc]
lemma dgModuleExtensionTriple_outer_naturality :
    (BimoduleTensor.associatorIso A U E D (RightModule A D)
        (BimoduleTensor.compose A U T E P Q) R S).inv ≫
      (dgModuleGraphTensorFunctor A D U).map
        (BimoduleTensor.composeMap A U E D (dgFunctorGraphCompositionIso A E T U G H).hom
          (𝟙 (BimoduleCategory.of A E D R))) =
    BimoduleTensor.composeMap A U E (RightModule A D)
        (dgFunctorGraphCompositionIso A E T U G H).hom
        (𝟙 (BimoduleCategory.of A E (RightModule A D)
          (BimoduleTensor.compose A E D (RightModule A D) R S))) ≫
      (BimoduleTensor.associatorIso A U E D (RightModule A D)
        (functorGraph A E U (G.comp H)) R S).inv := by
  have h := dgTensor_associator_inv_naturality A U E D (RightModule A D)
    (dgFunctorGraphCompositionIso A E T U G H).hom
    (𝟙 (BimoduleCategory.of A E D R))
    (𝟙 (BimoduleCategory.of A D (RightModule A D) S))
  simp only [BimoduleTensor.composeMap_id] at h
  exact h.symm

/-- 元の三 graph と恒等加群に対する、実際の逆結合の五角。 -/
@[reassoc]
lemma dgModuleExtensionTriple_inverse_pentagon :
    BimoduleTensor.composeMap A U T (RightModule A D) (𝟙 (BimoduleCategory.of A U T P))
        (BimoduleTensor.associatorIso A T E D (RightModule A D) Q R S).inv ≫
      (BimoduleTensor.associatorIso A U T D (RightModule A D) P
        (BimoduleTensor.compose A T E D Q R) S).inv ≫
      (dgModuleGraphTensorFunctor A D U).map
        (BimoduleTensor.associatorIso A U T E D P Q R).inv =
    (BimoduleTensor.associatorIso A U T E (RightModule A D) P Q
        (BimoduleTensor.compose A E D (RightModule A D) R S)).inv ≫
      (BimoduleTensor.associatorIso A U E D (RightModule A D)
        (BimoduleTensor.compose A U T E P Q) R S).inv :=
  dgTensor_associator_inv_pentagon A U T E D (RightModule A D) P Q R S

/-- 元の内側の実延長比較を、逆結合と graph 比較の作用へ展開する。 -/
lemma dgModuleExtensionTriple_inner_expansion :
    BimoduleTensor.composeMap A U T (RightModule A D) (𝟙 (BimoduleCategory.of A U T P))
        (dgModuleExtensionCompositionTensorIso A D E T F G).hom =
      BimoduleTensor.composeMap A U T (RightModule A D) (𝟙 (BimoduleCategory.of A U T P))
        (BimoduleTensor.associatorIso A T E D (RightModule A D) Q R S).inv ≫
      BimoduleTensor.composeMap A U T (RightModule A D) (𝟙 (BimoduleCategory.of A U T P))
        ((dgModuleGraphTensorFunctor A D T).map
          (dgFunctorGraphCompositionIso A D E T F G).hom) := by
  change BimoduleTensor.composeMap A U T (RightModule A D)
    (𝟙 (BimoduleCategory.of A U T P))
    ((BimoduleTensor.associatorIso A T E D (RightModule A D) Q R S).inv ≫
      (dgModuleGraphTensorFunctor A D T).map
        (dgFunctorGraphCompositionIso A D E T F G).hom) = _
  exact dgBimoduleTensor_second_comp A U T (RightModule A D)
    (BimoduleCategory.of A U T P) _ _

end SerrePositivity.KST.SConstruction
