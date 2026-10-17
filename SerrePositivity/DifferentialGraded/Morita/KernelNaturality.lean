module
public import SerrePositivity.DifferentialGraded.Morita.KernelResolution

/-! # kernelの閉零射によるtensor作用の自然変換

## 概要
全Hom自然なkernel射を、入力加群にも自然なtensor作用の射へ送る。

## 方針
既存のbimodule合成射を右D加群圏の恒等dg関手で評価し、全Hom自然性を閉零射で評価する。

## 規約と注意
全右加群型にsmallnessを課さず、D・EのSmall.{u}だけを用いる。局所Hom条件は不要。

## 使われ方
U16aの主導来kernel上の関手族を構成するための通常・H⁰の自然性。
公開型と進捗はformalization-plans/dg-theory-morita.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A]

private lemma homEquiv_post {V : Type*} [Category* V] [MonoidalCategory V]
    {C : Type*} [Category* C] [EnrichedOrdinaryCategory V C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V (f ≫ g) = eHomEquiv V f ≫ eHomWhiskerLeft V X g := by
  rw [eHomEquiv_comp]
  dsimp only [eHomWhiskerLeft]
  rw [rightUnitor_inv_naturality_assoc]
  simp only [unitors_inv_equal, tensorHom_def, Category.assoc]

private lemma homEquiv_pre {V : Type*} [Category* V] [MonoidalCategory V]
    {C : Type*} [Category* C] [EnrichedOrdinaryCategory V C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V (f ≫ g) = eHomEquiv V g ≫ eHomWhiskerRight V f Z := by
  rw [eHomEquiv_comp]
  dsimp only [eHomWhiskerRight]
  rw [leftUnitor_inv_naturality_assoc]
  simp only [tensorHom_def', Category.assoc]

/-- 全Hom自然な加群値bimodule射を閉零関手の自然変換へ評価する。源Cのsmallnessは不要。 -/
def kernelClosedFamilyNatTrans (E : Type w) [DGCategory A E] [Small.{u} E]
    (C : Type z) [DGCategory A C] {P Q : BimoduleCategory A E C} (a : P ⟶ Q) :
    (BimoduleCategory.underlying A E C P).toFunctor.onClosed ⟶
      (BimoduleCategory.underlying A E C Q).toFunctor.onClosed where
  app X := a.val (ForgetEnrichment.to (Complex A) X)
  naturality {X Y} f := by
    have h := congrArg (fun k => ForgetEnrichment.homTo (Complex A) f ≫ k)
      (a.property (ForgetEnrichment.to (Complex A) X) (ForgetEnrichment.to (Complex A) Y))
    apply (eHomEquiv (Complex A)).injective
    rw [homEquiv_post, homEquiv_pre]
    change (ForgetEnrichment.homTo (Complex A) f ≫ _) ≫ _ =
      (ForgetEnrichment.homTo (Complex A) f ≫ _) ≫ _
    simp only [moduleHomPostcompose, moduleHomPrecompose] at h
    convert h using 1 <;> rfl

variable (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- kernel射を通常tensor作用の自然変換へ送る。大きい全加群圏のsmallnessは不要。 -/
def kernelTensorMap {P P' : BimoduleCategory A E D} (f : P ⟶ P') :
    (kernelTensor A D E (BimoduleCategory.underlying A E D P)).onClosed ⟶
      (kernelTensor A D E (BimoduleCategory.underlying A E D P')).onClosed :=
  kernelClosedFamilyNatTrans A E (RightModule A D)
    (BimoduleTensor.composeMap A E D (RightModule A D) f
      (𝟙 (BimoduleCategory.of A D (RightModule A D) (DGFunctor.id (RightModule A D)))))

/-- 閉零作用のkernel射を各入力で評価すると、既存bimodule合成射の成分になる。 -/
lemma kernelTensorMap_app {P P' : BimoduleCategory A E D} (f : P ⟶ P')
    (M : ModuleCategory A D) :
    (kernelTensorMap A D E f).app M =
      (BimoduleTensor.composeMap A E D (RightModule A D) f
        (𝟙 (BimoduleCategory.of A D (RightModule A D)
          (DGFunctor.id (RightModule A D))))).val (ForgetEnrichment.to (Complex A) M) := rfl

/-- 恒等kernel射の通常作用は恒等自然変換。 -/
lemma kernelTensorMap_id (P : BimoduleCategory A E D) :
    kernelTensorMap A D E (𝟙 P) = 𝟙 _ := by
  apply NatTrans.ext
  funext M
  exact congrArg (fun k => k.val (ForgetEnrichment.to (Complex A) M))
    (BimoduleTensor.composeMap_id A E D (RightModule A D) P
      (BimoduleCategory.of A D (RightModule A D) (DGFunctor.id (RightModule A D))))

/-- kernel射の合成は通常作用の自然変換の合成へ送られる。 -/
lemma kernelTensorMap_comp {P P' P'' : BimoduleCategory A E D}
    (f : P ⟶ P') (g : P' ⟶ P'') :
    kernelTensorMap A D E (f ≫ g) = kernelTensorMap A D E f ≫ kernelTensorMap A D E g := by
  apply NatTrans.ext
  funext M
  let I := BimoduleCategory.of A D (RightModule A D) (DGFunctor.id (RightModule A D))
  have h := BimoduleTensor.composeMap_comp A E D (RightModule A D) f g (𝟙 I) (𝟙 I)
  rw [Category.id_comp] at h
  exact congrArg (fun k => k.val (ForgetEnrichment.to (Complex A) M)) h

/-- H⁰商の普遍性で、kernel射の通常作用を入力のホモトピー圏へ降ろす。 -/
def kernelTensorHomotopyMap {P P' : BimoduleCategory A E D} (f : P ⟶ P') :
    (kernelTensor A D E (BimoduleCategory.underlying A E D P)).onHomotopy ⟶
      (kernelTensor A D E (BimoduleCategory.underlying A E D P')).onHomotopy :=
  CategoryTheory.Quotient.natTransLift (boundaryRelation A (RightModule A D))
    { app M := (moduleToHomotopy A E).map ((kernelTensorMap A D E f).app M)
      naturality := fun {M N} g => by
        change (moduleToHomotopy A E).map _ ≫ (moduleToHomotopy A E).map _ =
          (moduleToHomotopy A E).map _ ≫ (moduleToHomotopy A E).map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (moduleToHomotopy A E).map ((kernelTensorMap A D E f).naturality g) }

/-- 元の入力でのH⁰成分は、既存の通常kernel作用の射を商へ送ったもの。 -/
lemma kernelTensorHomotopyMap_app {P P' : BimoduleCategory A E D} (f : P ⟶ P')
    (M : ModuleCategory A D) :
    (kernelTensorHomotopyMap A D E f).app ((moduleToHomotopy A D).obj M) =
      (moduleToHomotopy A E).map ((kernelTensorMap A D E f).app M) := rfl

/-- H⁰上でも恒等kernel射は恒等に写る。 -/
lemma kernelTensorHomotopyMap_id (P : BimoduleCategory A E D) :
    kernelTensorHomotopyMap A D E (𝟙 P) = 𝟙 _ := by
  apply NatTrans.ext
  funext X
  rcases X with ⟨M⟩
  change (moduleToHomotopy A E).map ((kernelTensorMap A D E (𝟙 P)).app M) = 𝟙 _
  rw [kernelTensorMap_id]
  exact (moduleToHomotopy A E).map_id _

/-- H⁰への降下はkernel射の合成を保つ。 -/
lemma kernelTensorHomotopyMap_comp {P P' P'' : BimoduleCategory A E D}
    (f : P ⟶ P') (g : P' ⟶ P'') :
    kernelTensorHomotopyMap A D E (f ≫ g) =
      kernelTensorHomotopyMap A D E f ≫ kernelTensorHomotopyMap A D E g := by
  apply NatTrans.ext
  funext X
  rcases X with ⟨M⟩
  change (moduleToHomotopy A E).map ((kernelTensorMap A D E (f ≫ g)).app M) =
    (moduleToHomotopy A E).map ((kernelTensorMap A D E f).app M) ≫
      (moduleToHomotopy A E).map ((kernelTensorMap A D E g).app M)
  rw [kernelTensorMap_comp]
  exact (moduleToHomotopy A E).map_comp _ _

/-- tensor作用のkernel射は、各値でid入力と左評価射のbalanced tensor mapに一致する。 -/
lemma kernelTensorMap_value {P P' : BimoduleCategory A E D} (f : P ⟶ P')
    (M : ModuleCategory A D) (e : E) :
    (moduleEvaluation A E e).map ((kernelTensorMap A D E f).app M) =
      BalancedTensor.map A D (𝟙 M) ((BimoduleCategory.leftEvaluation A E D e).map f) := by
  change (BimoduleCategory.valueEvaluation A E (RightModule A D) e
    (ForgetEnrichment.to (Complex A) M)).map
      (BimoduleTensor.composeMap A E D (RightModule A D) f
        (𝟙 (BimoduleCategory.of A D (RightModule A D)
          (DGFunctor.id (RightModule A D))))) = _
  rw [BimoduleTensor.composeMap_value_eval]
  unfold BimoduleTensor.composeValueMap
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- 射影的右D入力は相対K-flatなので、任意kernel準同型をtensor作用が保つ。 -/
lemma kernelTensorMap_projective_quasiIso {P P' : BimoduleCategory A E D}
    (f : P ⟶ P') (hf : BimoduleCategory.quasiIso A E D f)
    (M : ModuleCategory A D) (hM : moduleHomotopicallyProjective A D M) :
    moduleQuasiIso A E ((kernelTensorMap A D E f).app M) := by
  intro e
  rw [kernelTensorMap_value]
  exact moduleRelativeKFlat_preserves_leftQuasiIso A D
    (ForgetEnrichment.to (Complex A) M) (moduleHomotopicallyProjective_relativeKFlat A D hM)
    ((BimoduleCategory.leftEvaluation A E D e).map f)
    (BimoduleCategory.quasiIso_leftEvaluation A E D hf e)

end SerrePositivity.DifferentialGraded.Morita
