module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceUnitClosed
public import SerrePositivity.DifferentialGraded.Tensor.Pentagon

/-! # 通常kernel作用の結合coherence

## 概要
三因子kernelの通常作用の二つの合成経路を、元のbimodule結合子により比較する。

## 方針
既存五角を逆向きの作用比較へ変形し、全右加群で評価する。

## 規約と注意
局所Hom K-flat性は不要。最後の入力族の対象型のSmallを仮定しない。

## 使われ方
U16aの導来作用の結合coherenceの計算モデル。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t x
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor

private lemma inverse_pentagon {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ : C}
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₀ ≅ X₃) (d : X₃ ≅ X₄) (e : X₄ ≅ X₂)
    (h : a.hom ≫ b.hom = c.hom ≫ d.hom ≫ e.hom) :
    e.inv ≫ d.inv = b.inv ≫ a.inv ≫ c.hom := by
  apply (cancel_epi (a.hom ≫ b.hom)).1
  conv_lhs => rw [h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  (G : Type t) [DGCategory A G] [Small.{u} G]

/-- 入力族で評価した結合子は、同じ加群を入力とする通常作用の合成比較。 -/
lemma kernelTensorAssociatorFamily (Q : Bimodule A F E) (R : Bimodule A G F)
    (C : Type x) [DGCategory A C] (S : Bimodule A E C) (c : C) :
    (BimoduleCategory.evaluation A G C c).map (associatorIso A G F E C R Q S).inv =
      (kernelTensorCompositionClosedIso A E F G Q R).hom.app
        ((BimoduleCategory.evaluation A E C c).obj (BimoduleCategory.of A E C S)) := by
  rw [kernelTensorCompositionClosedIso_hom_app]
  apply moduleMorphism_ext
  intro g
  change (BimoduleCategory.valueEvaluation A G C g c).map
    (associatorIso A G F E C R Q S).inv =
    (BimoduleCategory.valueEvaluation A G (RightModule A E) g (S.rightAt c)).map
      (associatorIso A G F E (RightModule A E) R Q (DGFunctor.id (RightModule A E))).inv
  rw [associatorIso_inv_value_eval, associatorIso_inv_value_eval]
  unfold associatorValueIso
  rfl

/-- 五角を作用の合成比較の向きへ変形した、入力族上のbimodule等式。 -/
lemma kernelTensorAssociator_inversePentagon
    (P : Bimodule A E D) (Q : Bimodule A F E) (R : Bimodule A G F)
    (C : Type x) [DGCategory A C] (S : Bimodule A D C) :
    composeMap A G F C (𝟙 (BimoduleCategory.of A G F R))
        (associatorIso A F E D C Q P S).inv ≫
      (associatorIso A G F D C R (BimoduleTensor.compose A F E D Q P) S).inv =
    (associatorIso A G F E C R Q (BimoduleTensor.compose A E D C P S)).inv ≫
      (associatorIso A G E D C (BimoduleTensor.compose A G F E R Q) P S).inv ≫
        composeMap A G D C (associatorIso A G F E D R Q P).hom
          (𝟙 (BimoduleCategory.of A D C S)) := by
  let a := associatorIso A G E D C (BimoduleTensor.compose A G F E R Q) P S
  let b := associatorIso A G F E C R Q (BimoduleTensor.compose A E D C P S)
  let c := (composeFunctor A G D C).mapIso
    (Iso.prod (associatorIso A G F E D R Q P) (Iso.refl (BimoduleCategory.of A D C S)))
  let d := associatorIso A G F D C R (BimoduleTensor.compose A F E D Q P) S
  let e := (composeFunctor A G F C).mapIso
    (Iso.prod (Iso.refl (BimoduleCategory.of A G F R)) (associatorIso A F E D C Q P S))
  exact inverse_pentagon a b c d e (pentagon A G F E D C R Q P S)

/-- 三つの通常kernel作用の合成比較は、元のbimodule結合子と整合する。 -/
lemma kernelTensorCompositionClosedIso_associator
    (P : Bimodule A E D) (Q : Bimodule A F E) (R : Bimodule A G F)
    (M : ModuleCategory A D) :
    (kernelTensor A F G R).onClosed.map
        ((kernelTensorCompositionClosedIso A D E F P Q).hom.app M) ≫
      (kernelTensorCompositionClosedIso A D F G (BimoduleTensor.compose A F E D Q P) R).hom.app M =
    (kernelTensorCompositionClosedIso A E F G Q R).hom.app ((kernelTensor A D E P).onClosed.obj M) ≫
      (kernelTensorCompositionClosedIso A D E G P (BimoduleTensor.compose A G F E R Q)).hom.app M ≫
        (kernelTensorMap A D G (associatorIso A G F E D R Q P).hom).app M := by
  let V := BimoduleCategory.evaluation A G (RightModule A D)
    (ForgetEnrichment.to (Complex A) M)
  have hv := congrArg V.map (kernelTensorAssociator_inversePentagon A D E F G P Q R
    (RightModule A D) (DGFunctor.id (RightModule A D)))
  simp only [Functor.map_comp] at hv
  rw [kernelTensorFamilyMap, kernelTensorAssociatorFamily, kernelTensorAssociatorFamily,
    kernelTensorAssociatorFamily, kernelTensorAssociatorFamily] at hv
  convert hv using 1 <;> rfl

end SerrePositivity.DifferentialGraded.Morita
