module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionClosed
public import SerrePositivity.DifferentialGraded.Morita.KernelAugmentationNaturality
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorNaturality

/-! # 通常kernelの射に対する作用合成の自然性

## 概要
通常作用の合成比較が、両方のkernelの任意の閉零射に自然であることを証明する。

## 方針
作用射の水平合成を実際の入れ子bimodule射と同定し、既存結合子の三変数自然性を評価する。

## 規約と注意
局所Hom K-flat条件は不要。主導来kernel全体への降下と作用coherenceは別途行う。

## 使われ方
U16aの全導来kernelの合成比較を、kernel射に自然な族へ束ねる基盤。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]

private lemma inverse_naturality {C : Type*} [Category C] {X Y X' Y' : C}
    (a : X ≅ Y) (b : X' ≅ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : f ≫ b.hom = a.hom ≫ g) : g ≫ b.inv = a.inv ≫ f := by
  apply (cancel_epi a.hom).1
  rw [← Category.assoc, ← h, Category.assoc, b.hom_inv_id, Category.comp_id,
    a.hom_inv_id_assoc]

/-- 通常作用の合成比較の成分は、既存結合子の逆射を加群で評価した射。 -/
lemma kernelTensorCompositionClosedIso_hom_app
    (P : Bimodule A E D) (Q : Bimodule A F E) (M : ModuleCategory A D) :
    (kernelTensorCompositionClosedIso A D E F P Q).hom.app M =
      (BimoduleCategory.evaluation A F (RightModule A D)
        (ForgetEnrichment.to (Complex A) M)).map
        (associatorIso A F E D (RightModule A D) Q P
          (DGFunctor.id (RightModule A D))).inv := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

variable {P P' : BimoduleCategory A E D} {Q Q' : BimoduleCategory A F E}
  (f : P ⟶ P') (g : Q ⟶ Q')

/-- 二つの作用射の水平合成は、入れ子bimodule射の評価に一致する。 -/
lemma kernelTensorCompositionMap_app (M : ModuleCategory A D) :
    (NatTrans.hcomp (kernelTensorMap A D E f) (kernelTensorMap A E F g)).app M =
      (BimoduleCategory.evaluation A F (RightModule A D)
        (ForgetEnrichment.to (Complex A) M)).map
        (composeMap A F E (RightModule A D) g
          (composeMap A E D (RightModule A D) f
            (𝟙 (BimoduleCategory.of A D (RightModule A D)
              (DGFunctor.id (RightModule A D)))))) := by
  apply moduleMorphism_ext
  intro e
  simp only [NatTrans.hcomp_app, CategoryTheory.Functor.map_comp,
    kernelTensorMap_value, kernelTensor_map_eval]
  have he := composeMap_value_eval A F E (RightModule A D) g
    (composeMap A E D (RightModule A D) f
      (𝟙 (BimoduleCategory.of A D (RightModule A D)
        (DGFunctor.id (RightModule A D))))) e (ForgetEnrichment.to (Complex A) M)
  dsimp only [BimoduleCategory.valueEvaluation, Functor.comp_map] at he
  erw [he]
  unfold composeValueMap BalancedTensor.rightTensorMap BalancedTensor.rightTensorFunctor
  rw [← BalancedTensor.map_comp]
  simp only [Category.id_comp]
  erw [Category.comp_id]
  exact congrArg (fun k => BalancedTensor.map A E k
    ((BimoduleCategory.leftEvaluation A F E e).map g))
    (kernelTensorMap_app A D E f M)

/-- 通常作用の合成比較は、両kernelの任意の閉零射に自然。 -/
lemma kernelTensorCompositionClosedIso_kernel_naturality :
    NatTrans.hcomp (kernelTensorMap A D E f) (kernelTensorMap A E F g) ≫
        (kernelTensorCompositionClosedIso A D E F
          (BimoduleCategory.underlying A E D P') (BimoduleCategory.underlying A F E Q')).hom =
      (kernelTensorCompositionClosedIso A D E F
          (BimoduleCategory.underlying A E D P) (BimoduleCategory.underlying A F E Q)).hom ≫
        kernelTensorMap A D F (composeMap A F E D g f) := by
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app, kernelTensorCompositionMap_app,
    kernelTensorCompositionClosedIso_hom_app, kernelTensorMap_app]
  let V := BimoduleCategory.evaluation A F (RightModule A D)
    (ForgetEnrichment.to (Complex A) M)
  have h := associatorIso_naturality A F E D (RightModule A D) g f
    (𝟙 (BimoduleCategory.of A D (RightModule A D)
      (DGFunctor.id (RightModule A D))))
  have hi := inverse_naturality
    (associatorIso A F E D (RightModule A D)
      (BimoduleCategory.underlying A F E Q) (BimoduleCategory.underlying A E D P)
      (DGFunctor.id (RightModule A D)))
    (associatorIso A F E D (RightModule A D)
      (BimoduleCategory.underlying A F E Q') (BimoduleCategory.underlying A E D P')
      (DGFunctor.id (RightModule A D))) _ _ h
  have hh := congrArg V.map hi
  simp only [CategoryTheory.Functor.map_comp] at hh
  convert hh using 1 <;> rfl

end SerrePositivity.DifferentialGraded.Morita
