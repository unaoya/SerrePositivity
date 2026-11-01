module

public import SerrePositivity.DifferentialGraded.Morita.Kernel
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Localization.Prod
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.KFlatness
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Pentagon
public import Mathlib.Tactic.CategoryTheory.Slice

/-!
# Morita.CoherenceCompositionKernel

## 概要
15 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## CoherenceIdentity（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceIdentity.lean） -/

/-! # 対角kernelの主導来作用と恒等関手

## 概要
対角bimoduleのtensor単位子と入力解像度の増大射から、主導来作用の恒等比較を構成する。

## 方針
通常単位子をH⁰へ降ろし、入力解像度関手の増大を局所化の普遍性で恒等関手へ比較する。

## 規約と注意
DのSmall.{u}だけを要求し、localHomKFlatは不要。一般の分解変更coherenceは扱わない。

## 使われ方
U16aのkernelIdentityIsoと、以後の合成比較の単位整合性で使う。
-/

@[expose] public section CoherenceIdentity
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 対角kernelの通常作用は、既存の全Hom自然な左単位子によって恒等と比較される。 -/
def kernelIdentityClosedIso :
    (kernelTensor A D D (Bimodule.diagonal A D)).onClosed ≅ 𝟭 (ModuleCategory A D) :=
  NatIso.ofComponents (fun M =>
    (BimoduleCategory.evaluation A D (RightModule A D) (ForgetEnrichment.to (Complex A) M)).mapIso
      (leftBimoduleUnitIso A D (RightModule A D) (DGFunctor.id (RightModule A D))))
    (fun f => (kernelClosedFamilyNatTrans A D (RightModule A D)
      (leftBimoduleUnitIso A D (RightModule A D)
        (DGFunctor.id (RightModule A D))).hom).naturality f)

/-- 対角kernelの通常単位子をH⁰商へ降ろした自然同型。 -/
def kernelIdentityHomotopyIso :
    (kernelTensor A D D (Bimodule.diagonal A D)).onHomotopy ≅
      𝟭 (ModuleHomotopyCategory A D) :=
  CategoryTheory.Quotient.natIsoLift (boundaryRelation A (RightModule A D))
    (eqToIso (kernelTensor A D D (Bimodule.diagonal A D)).onHomotopy_fac ≪≫
      Functor.isoWhiskerRight (kernelIdentityClosedIso A D) (moduleToHomotopy A D) ≪≫
      Functor.leftUnitor (moduleToHomotopy A D) ≪≫
      (Functor.rightUnitor (moduleToHomotopy A D)).symm)

/-- 指定入力解像度族の増大射は、持ち上げのH⁰可換squareにより自然変換になる。 -/
def kernelInputResolutionHomotopyAugmentation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionHomotopyFunctor A D R ⟶ moduleToHomotopy A D where
  app M := (moduleToHomotopy A D).map (R M).π
  naturality {M N} f := (R M).lift_fac (R N) f

/-- 入力増大は準同型なので、主導来圏では解像度族と元の入力を自然同型で結ぶ。 -/
def kernelInputResolutionDerivedAugmentationIso
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionHomotopyFunctor A D R ⋙ moduleHomotopyToDerivedClosed A D ≅
      moduleToDerived A D := by
  let τ := whiskerRight (kernelInputResolutionHomotopyAugmentation A D R)
    (moduleHomotopyToDerivedClosed A D)
  have ht : IsIso τ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    exact Localization.inverts (moduleHomotopyToDerivedClosed A D)
      (moduleHomotopyQuasiIso A D) _
      ((moduleHomotopyQuasiIso_map_iff A D (R M).π).2 (R M).quasiIso)
  let := ht
  exact asIso τ ≪≫ moduleToHomotopyDerivedIso A D

/-- 同じ入力解像度の増大を全主導来入力へ延長した、実際の解像度関手の余単位同型。 -/
def kernelInputResolutionDerivedCounitIso
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleDerivedResolutionFunctor A D R ⋙ moduleHomotopyToDerivedClosed A D ≅
      𝟭 (DerivedModuleCategory A D) := by
  let G := moduleDerivedResolutionFunctor A D R ⋙ moduleHomotopyToDerivedClosed A D
  let e : moduleToDerived A D ⋙ G ≅ moduleToDerived A D :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (moduleDerivedResolutionFunctor_fac A D R)
        (moduleHomotopyToDerivedClosed A D) ≪≫
      kernelInputResolutionDerivedAugmentationIso A D R
  exact Localization.liftNatIso (moduleToDerived A D) (moduleQuasiIso A D)
    (moduleToDerived A D ⋙ G) (moduleToDerived A D) G (𝟭 _) e

/-- 通常の対角kernelの導来作用を、H⁰単位子と入力解像度増大から恒等へ比較する。 -/
def kernelDerivedTensorOnBimoduleIdentityIso :
    kernelDerivedTensorOnBimodule A D D (Bimodule.diagonal A D) ≅
      𝟭 (DerivedModuleCategory A D) :=
  Functor.isoWhiskerLeft
      (moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D))
      (Functor.isoWhiskerRight (kernelIdentityHomotopyIso A D)
          (moduleHomotopyToDerivedClosed A D) ≪≫
        Functor.leftUnitor (moduleHomotopyToDerivedClosed A D)) ≪≫
    kernelInputResolutionDerivedCounitIso A D (moduleCanonicalProjectiveResolution A D)

/-- 主導来対角kernelの作用は恒等関手と自然同型。必要仮定はSmall.{u} Dのみ。 -/
def kernelIdentityIso :
    kernelDerivedTensor A D D (kernelIdentity A D) ≅ 𝟭 (DerivedModuleCategory A D) :=
  kernelDerivedTensorOnBimoduleIso A D D
      (BimoduleCategory.of A D D (Bimodule.diagonal A D)) ≪≫
    kernelDerivedTensorOnBimoduleIdentityIso A D

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceIdentity

/-! ## CoherenceCompositionFamilies（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceCompositionFamilies.lean） -/

/-! # 主導来kernelの作用合成を表す二つの関手族

## 概要
作用を順に合成する族と、導来合成kernelを作用させる族を同じ関手圏に置く。

## 方針
MathlibのwhiskeringLeft・whiskeringRightと既存の主導来作用・bimodule合成を合成する。

## 規約と注意
kernelはD→Eで右E・左D。合成kernel側だけに始域DのlocalHomKFlatを要求する。

## 使われ方
U16aの合成比較を全ての導来kernel射に自然な関手族の同型として構成するための入口。
-/

@[expose] public section CoherenceCompositionFamilies
universe u v w z

noncomputable section
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]

/-- 二つの主導来kernelの作用をD→E→Fの順に合成する関手族。 -/
def kernelActionCompositionFamily :
    Kernel A D E ⥤ (Kernel A E F ⥤
      (DerivedModuleCategory A D ⥤ DerivedModuleCategory A F)) :=
  kernelDerivedTensorFunctor A D E ⋙
    whiskeringLeft (DerivedModuleCategory A D) (DerivedModuleCategory A E)
      (DerivedModuleCategory A F) ⋙
    (whiskeringLeft (Kernel A E F)
      (DerivedModuleCategory A E ⥤ DerivedModuleCategory A F)
      (DerivedModuleCategory A D ⥤ DerivedModuleCategory A F)).obj
      (kernelDerivedTensorFunctor A E F)

/-- 導来合成kernelの主導来作用を同じ二変数の関手族に置く。 -/
def kernelCompositeActionFamily (hD : localHomKFlat A D) :
    Kernel A D E ⥤ (Kernel A E F ⥤
      (DerivedModuleCategory A D ⥤ DerivedModuleCategory A F)) :=
  BimoduleTensor.derivedBimoduleComposeFunctor A F E D hD ⋙
    (whiskeringRight (Kernel A E F) (Kernel A D F)
      (DerivedModuleCategory A D ⥤ DerivedModuleCategory A F)).obj
      (kernelDerivedTensorFunctor A D F)

/-- 作用合成族の両kernel射に関する成分は、実際の二つの作用射の水平合成。 -/
lemma kernelActionCompositionFamily_map_app
    {P P' : Kernel A D E} {Q Q' : Kernel A E F} (f : P ⟶ P') (g : Q ⟶ Q') :
    ((kernelActionCompositionFamily A D E F).map f).app Q ≫
        ((kernelActionCompositionFamily A D E F).obj P').map g =
      NatTrans.hcomp ((kernelDerivedTensorFunctor A D E).map f)
        ((kernelDerivedTensorFunctor A E F).map g) := by
  apply NatTrans.ext
  funext X
  simp only [NatTrans.hcomp_app]
  change (kernelDerivedTensor A E F Q).map
      (((kernelDerivedTensorFunctor A D E).map f).app X) ≫
    ((kernelDerivedTensorFunctor A E F).map g).app ((kernelDerivedTensor A D E P').obj X) = _
  exact ((kernelDerivedTensorFunctor A E F).map g).naturality
    (((kernelDerivedTensorFunctor A D E).map f).app X)

/-- 合成kernel作用族の両kernel射に関する成分はkernelComposeMapの作用。 -/
lemma kernelCompositeActionFamily_map_app (hD : localHomKFlat A D)
    {P P' : Kernel A D E} {Q Q' : Kernel A E F} (f : P ⟶ P') (g : Q ⟶ Q') :
    ((kernelCompositeActionFamily A D E F hD).map f).app Q ≫
        ((kernelCompositeActionFamily A D E F hD).obj P').map g =
      (kernelDerivedTensorFunctor A D F).map (kernelComposeMap A D E F hD f g) :=
  ((kernelDerivedTensorFunctor A D F).map_comp _ _).symm

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceCompositionFamilies

/-! ## CoherenceCompositionLocalization（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceCompositionLocalization.lean） -/

/-! # kernel作用合成の積圏表示とK-flatモデルの局所化

## 概要
二つの主導来kernelの作用合成を積圏上に置き、K-flat代表と通常代表からの積局所化を固定する。

## 方針
U12e-localのK-flat部分圏との比較同値とMathlibの積局所化を使う。

## 規約と注意
必要な局所Hom条件は始域Dだけ。モデルの射のクラスは各指定準同型の積。

## 使われ方
U16aの合成比較を全導来kernelの任意射に自然な同型へ延長する。
-/

@[expose] public section CoherenceCompositionLocalization
universe u v w z

noncomputable section
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]

/-- 二つの作用を合成する関手を、kernelの積圏上で読む。 -/
def kernelActionCompositionBifunctor : Kernel A D E × Kernel A E F ⥤
    (DerivedModuleCategory A D ⥤ DerivedModuleCategory A F) :=
  uncurry.obj (kernelActionCompositionFamily A D E F)

/-- 導来合成kernelの作用を、同じ積圏上で読む。 -/
def kernelCompositeActionBifunctor (hD : localHomKFlat A D) :
    Kernel A D E × Kernel A E F ⥤
      (DerivedModuleCategory A D ⥤ DerivedModuleCategory A F) :=
  uncurry.obj (kernelCompositeActionFamily A D E F hD)

/-- 作用合成の積圏上のmapは、二つの作用射の水平合成。 -/
lemma kernelActionCompositionBifunctor_map
    {X Y : Kernel A D E × Kernel A E F} (f : X ⟶ Y) :
    (kernelActionCompositionBifunctor A D E F).map f =
      NatTrans.hcomp ((kernelDerivedTensorFunctor A D E).map f.1)
        ((kernelDerivedTensorFunctor A E F).map f.2) :=
  kernelActionCompositionFamily_map_app A D E F f.1 f.2

/-- 導来合成kernel作用の積圏上のmapは、kernelComposeMapの作用。 -/
lemma kernelCompositeActionBifunctor_map (hD : localHomKFlat A D)
    {X Y : Kernel A D E × Kernel A E F} (f : X ⟶ Y) :
    (kernelCompositeActionBifunctor A D E F hD).map f =
      (kernelDerivedTensorFunctor A D F).map (kernelComposeMap A D E F hD f.1 f.2) :=
  kernelCompositeActionFamily_map_app A D E F hD f.1 f.2

/-- 最初のkernelを右K-flat代表で、後のkernelを通常代表で与える積関手。 -/
def kernelCompositionModels : RightKFlatBimoduleCategory A E D × BimoduleCategory A F E ⥤
    Kernel A D E × Kernel A E F :=
  (rightKFlatInclusion A E D ⋙ bimoduleToDerived A E D).prod (bimoduleToDerived A F E)

/-- 上の積モデルで反転する射は、各既存準同型クラスの積。 -/
def kernelCompositionModelQuasiIso : MorphismProperty
    (RightKFlatBimoduleCategory A E D × BimoduleCategory A F E) :=
  (rightKFlatQuasiIso A E D).prod (BimoduleCategory.quasiIso A F E)

/-- Dの局所Hom K-flat性により、モデルの積関手は指定した準同型の積に関する局所化。 -/
lemma kernelCompositionModels_isLocalization (hD : localHomKFlat A D) :
    (kernelCompositionModels A D E F).IsLocalization (kernelCompositionModelQuasiIso A D E F) := by
  let := rightKFlatDerivedInclusion_isEquivalence A E D hD
  let : (rightKFlatQuasiIso A E D).ContainsIdentities := by
    dsimp only [rightKFlatQuasiIso]
    infer_instance
  let : (rightKFlatInclusion A E D ⋙ bimoduleToDerived A E D).IsLocalization
      (rightKFlatQuasiIso A E D) :=
    Functor.IsLocalization.of_iso (W := rightKFlatQuasiIso A E D)
      (eqToIso (rightKFlatDerivedInclusion_fac A E D))
  dsimp only [kernelCompositionModels, kernelCompositionModelQuasiIso]
  infer_instance

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceCompositionLocalization

/-! ## CoherenceCompositionValueNaturality（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceCompositionValueNaturality.lean） -/

/-! # K-flat代表による導来kernel合成の両射計算

## 概要
U12e-localの指定K-flat代表での合成計算を、両kernelの射について同じsquareにまとめる。

## 方針
最初のkernelの射の計算と、後のkernelの射への自然性を貼り、通常合成の関手性を使う。

## 規約と注意
必要な局所Hom条件は始域Dだけ。後のkernelは任意の通常代表。

## 使われ方
U16aの自然なkernel合成比較の主局所化への降下で使う。
-/

@[expose] public section CoherenceCompositionValueNaturality
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]

/-- 右相対K-flat代表による導来合成の計算は、両kernelの任意射に自然。 -/
lemma kernelComposeKFlatValueIso_naturality (hD : localHomKFlat A D)
    {P P' : RightKFlatBimoduleCategory A E D} {Q Q' : BimoduleCategory A F E}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    kernelComposeMap A D E F hD ((bimoduleToDerived A E D).map f.hom)
        ((bimoduleToDerived A F E).map g) ≫
        (derivedBimoduleComposeKFlatValueIso A F E D hD P' Q').hom =
      (derivedBimoduleComposeKFlatValueIso A F E D hD P Q).hom ≫
        (bimoduleToDerived A F D).map (composeMap A F E D g f.hom) := by
  have hf := derivedBimoduleComposeKFlatValueIso_naturality A F E D hD f Q
  have hg := (derivedBimoduleComposeKFlatIso A F E D hD P').hom.naturality
    ((bimoduleToDerived A F E).map g)
  rw [derivedComposeWith_map_base] at hg
  change _ ≫ (derivedBimoduleComposeKFlatValueIso A F E D hD P' Q').hom =
    (derivedBimoduleComposeKFlatValueIso A F E D hD P' Q).hom ≫ _ at hg
  dsimp only [kernelComposeMap]
  rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]
  rw [← Functor.map_comp, ← composeMap_comp, Category.id_comp, Category.comp_id]

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceCompositionValueNaturality

/-! ## KernelAugmentation（旧 SerrePositivity/DifferentialGraded/Morita/KernelAugmentation.lean） -/

/-! # kernel作用の通常tensorへの増大比較と相対K-flat入力での計算

## 概要
入力解像度の増大射から、主導来作用と通常tensorの自然な比較を構成する。

## 方針
既存のHom mapの評価・H⁰計算同型・増大自然変換を使い、相対K-flat入力で比較を反転する。

## 規約と注意
相対K-flat性を入力右D加群に要求する。Homの局所K-flat性やkernelの射影性は要求しない。

## 使われ方
U16aのkernel合成比較を通常のbimodule結合子へ帰着するための計算API。
-/

@[expose] public section KernelAugmentation
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor CochainComplex HomComplex
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- 入力Homに対するtensorの作用は各E対象で既存rightHomMapに一致する。 -/
lemma kernelTensor_map_π (M N : RightModule A D) (e : E) :
    (kernelTensor A D E P).map M N ≫
      moduleHomπ A E ((kernelTensor A D E P).obj M) ((kernelTensor A D E P).obj N) e =
      BalancedTensor.rightHomMap A D M N (P.leftAt e) := by
  have h := BimoduleTensor.compose_leftMap_π A E D (RightModule A D) P
    (DGFunctor.id (RightModule A D)) M N e
  change (kernelTensor A D E P).map M N ≫
    moduleHomπ A E ((kernelTensor A D E P).obj M) ((kernelTensor A D E P).obj N) e =
      𝟙 _ ≫ BalancedTensor.rightHomMap A D M N (P.leftAt e) at h
  exact h.trans (Category.id_comp _)

/-- 通常入力射に対する作用を、各値の既存balanced tensor mapで計算する。 -/
lemma kernelTensor_map_eval {M N : ModuleCategory A D} (f : M ⟶ N) (e : E) :
    (moduleEvaluation A E e).map ((kernelTensor A D E P).onClosed.map f) =
      BalancedTensor.rightTensorMap A D (P.leftAt e) f := by
  apply Cochain.ofHom_injective
  rw [moduleEvaluation_cochain]
  change (moduleHomπ A E _ _ e).f 0
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f ≫
      (kernelTensor A D E P).map _ _)).val = _
  rw [cycleFromUnit_postcomp]
  have h := congrArg (fun k => k.f 0 (cycleFromUnit _
    (ForgetEnrichment.homTo (Complex A) f)).val)
    (kernelTensor_map_π A D E P (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) e)
  exact h.trans (BalancedTensor.rightHomMap_closedElement A D (P.leftAt e) f)

/-- 相対K-flat入力間の準同型を、任意kernelの通常tensor作用が保つ。 -/
lemma kernelTensor_relativeKFlat_quasiIso {M N : ModuleCategory A D}
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M))
    (hN : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) N))
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    moduleQuasiIso A E ((kernelTensor A D E P).onClosed.map f) := by
  intro e
  rw [kernelTensor_map_eval]
  exact BalancedTensor.rightTensor_relativeKFlat_quasiIso A D (P.leftAt e) hM hN f hf

/-- H⁰から主導来値への計算同型は、通常入力の射に自然。 -/
lemma kernelTensorHomotopyComputation_naturality {M N : ModuleCategory A D} (f : M ⟶ N) :
    (kernelHomotopyToDerived A D E P).map ((moduleToHomotopy A D).map f) ≫
        (kernelTensorHomotopyComputation A D E P N).hom =
      (kernelTensorHomotopyComputation A D E P M).hom ≫
        (moduleToDerived A E).map ((kernelTensor A D E P).onClosed.map f) := by
  have h := congrArg (moduleHomotopyToDerivedClosed A E).map
    ((eqToIso (kernelTensor A D E P).onHomotopy_fac).hom.naturality f)
  simp only [CategoryTheory.Functor.map_comp] at h
  dsimp only [kernelTensorHomotopyComputation, Iso.trans_hom, Functor.mapIso_hom,
    kernelHomotopyToDerived, Functor.comp_map]
  rw [← Category.assoc]
  erw [h]
  have hn := (moduleToHomotopyDerivedIso A E).hom.naturality
    ((kernelTensor A D E P).onClosed.map f)
  simp only [Functor.comp_map] at hn
  simp only [Functor.comp_map, Iso.app_hom]
  rw [Category.assoc]
  erw [hn]
  rw [Category.assoc]
  rfl

/-- H⁰計算の成分を、通常入力圏上の自然同型へ束ねる。 -/
def kernelTensorHomotopyComputationIso :
    moduleToHomotopy A D ⋙ kernelHomotopyToDerived A D E P ≅
      (kernelTensor A D E P).onClosed ⋙ moduleToDerived A E :=
  NatIso.ofComponents (kernelTensorHomotopyComputation A D E P)
    (fun f => kernelTensorHomotopyComputation_naturality A D E P f)

/-- 任意指定入力解像度族から通常tensorへの増大比較。 -/
def kernelResolutionTensorAugmentation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionHomotopyFunctor A D R ⋙ kernelHomotopyToDerived A D E P ⟶
      (kernelTensor A D E P).onClosed ⋙ moduleToDerived A E :=
  whiskerRight (kernelInputResolutionHomotopyAugmentation A D R)
      (kernelHomotopyToDerived A D E P) ≫
    (kernelTensorHomotopyComputationIso A D E P).hom

/-- 増大比較の成分は、解像度値の計算同型と実際のtensor増大の局所化像。 -/
lemma kernelResolutionTensorAugmentation_app
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : ModuleCategory A D) :
    (kernelResolutionTensorAugmentation A D E P R).app M =
      (kernelTensorHomotopyComputation A D E P (R M).obj).hom ≫
        (moduleToDerived A E).map ((kernelTensor A D E P).onClosed.map (R M).π) :=
  kernelTensorHomotopyComputation_naturality A D E P (R M).π

/-- 主導来作用から通常tensorへの、通常入力圏上で自然な増大比較。 -/
def kernelDerivedTensorAugmentation :
    moduleToDerived A D ⋙ kernelDerivedTensorOnBimodule A D E P ⟶
      (kernelTensor A D E P).onClosed ⋙ moduleToDerived A E :=
  whiskerRight (moduleDerivedResolutionFunctor_fac A D
      (moduleCanonicalProjectiveResolution A D)).hom (kernelHomotopyToDerived A D E P) ≫
    kernelResolutionTensorAugmentation A D E P (moduleCanonicalProjectiveResolution A D)

/-- 主導来増大比較は標準解像度の計算同型を通して実際のtensor増大に一致する。 -/
lemma kernelDerivedTensorAugmentation_app (M : ModuleCategory A D) :
    (kernelDerivedTensorAugmentation A D E P).app M =
      (kernelResolutionDerivedTensorComputation A D E P
        (moduleCanonicalProjectiveResolution A D) M).hom ≫
        (moduleToDerived A E).map
          ((kernelTensor A D E P).onClosed.map (moduleCanonicalProjectiveResolution A D M).π) := by
  change _ ≫ (kernelResolutionTensorAugmentation A D E P _).app M = _
  rw [kernelResolutionTensorAugmentation_app]
  simp only [kernelResolutionDerivedTensorComputation, Iso.trans_hom, Functor.mapIso_hom,
    whiskerRight_app, moduleDerivedResolutionComputation, Iso.app_hom, Category.assoc]

/-- 相対K-flatな入力では、主導来作用から通常tensorへの増大比較は同型。 -/
lemma kernelDerivedTensorAugmentation_isIso_of_relativeKFlat (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    IsIso ((kernelDerivedTensorAugmentation A D E P).app M) := by
  have hP := moduleHomotopicallyProjective_relativeKFlat A D
    (moduleCanonicalProjectiveResolution A D M).projective
  have hπ := kernelTensor_relativeKFlat_quasiIso A D E P hP hM
    (moduleCanonicalProjectiveResolution A D M).π
    (moduleCanonicalProjectiveResolution A D M).quasiIso
  have := moduleToDerived_inverts A E _ hπ
  rw [kernelDerivedTensorAugmentation_app]
  infer_instance

/-- 相対K-flatな通常入力では、主導来kernel作用を通常tensorの主導来像で計算できる。 -/
def kernelRelativeKFlatComputation (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    (kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj M) := by
  have := kernelDerivedTensorAugmentation_isIso_of_relativeKFlat A D E P M hM
  exact asIso ((kernelDerivedTensorAugmentation A D E P).app M)

end SerrePositivity.DifferentialGraded.Morita
end

end KernelAugmentation

/-! ## KernelResolutionModel（旧 SerrePositivity/DifferentialGraded/Morita/KernelResolutionModel.lean） -/

/-! # kernel作用の自然な射影解像度モデル

## 概要
通常入力上の導来作用を、選んだ射影解像度とのtensorを値に持つ関手で計算する。

## 方針
H⁰解像度関手の計算同型で値を移し、射を既存のliftによるtensor射と同定する。

## 規約と注意
解像度のliftは通常圏で厳密な関手とはしない。関手法則はH⁰と主導来圏を経由する。
局所Hom K-flat性は不要。

## 使われ方
U16aの作用の合成比較を、通常入力射に自然なモデルから主局所化へ延長する。
-/

@[expose] public section KernelResolutionModel
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)
  (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)

/-- H⁰解像度モデルの各値を、通常tensorの主導来像に置き換えた実際の関手。 -/
def kernelResolutionTensorModelFunctor : ModuleCategory A D ⥤ DerivedModuleCategory A E :=
  (moduleResolutionHomotopyFunctor A D R ⋙ kernelHomotopyToDerived A D E P).copyObj
    (fun M => (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj (R M).obj))
    (fun M => kernelTensorHomotopyComputation A D E P (R M).obj)

/-- 主導来作用を通常入力で計算する自然な解像度モデル。 -/
def kernelResolutionTensorModelIso :
    moduleToDerived A D ⋙ kernelResolutionDerivedTensor A D E P R ≅
      kernelResolutionTensorModelFunctor A D E P R :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleDerivedResolutionFunctor_fac A D R)
      (kernelHomotopyToDerived A D E P) ≪≫
    (moduleResolutionHomotopyFunctor A D R ⋙ kernelHomotopyToDerived A D E P).isoCopyObj
      _ (fun M => kernelTensorHomotopyComputation A D E P (R M).obj)

/-- 自然なモデルの射は、選んだliftの通常tensorを局所化した射そのもの。 -/
lemma kernelResolutionTensorModelFunctor_map {M N : ModuleCategory A D} (f : M ⟶ N) :
    (kernelResolutionTensorModelFunctor A D E P R).map f =
      (moduleToDerived A E).map
        ((kernelTensor A D E P).onClosed.map ((R M).lift (R N) f)) := by
  change (kernelTensorHomotopyComputation A D E P (R M).obj).inv ≫
      (kernelHomotopyToDerived A D E P).map
        ((moduleToHomotopy A D).map ((R M).lift (R N) f)) ≫
      (kernelTensorHomotopyComputation A D E P (R N).obj).hom = _
  rw [kernelTensorHomotopyComputation_naturality, Iso.inv_hom_id_assoc]

/-- 右相対K-flatなkernelの作用は、相対K-flat入力を相対K-flat出力に送る。 -/
lemma kernelTensor_relativeKFlat
    (hP : Bimodule.rightRelativeKFlat A E D P) (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    moduleRelativeKFlat A E
      ((kernelTensor A D E P).obj (ForgetEnrichment.to (Complex A) M)) := by
  intro N hN
  have hL : leftModuleAcyclic A D (BalancedTensor.Fubini.leftModule A E D P N) :=
    fun d => hP d N hN
  have h := hM (BalancedTensor.Fubini.leftModule A E D P N) hL
  exact cochainAcyclic_of_iso h
    (BalancedTensor.Fubini.iso A E D P (ForgetEnrichment.to (Complex A) M) N)

end SerrePositivity.DifferentialGraded.Morita
end

end KernelResolutionModel

/-! ## KernelAugmentationNaturality（旧 SerrePositivity/DifferentialGraded/Morita/KernelAugmentationNaturality.lean） -/

/-! # kernel射に対する計算同型と増大比較の自然性

## 概要
入力の解像度計算と通常tensorへの増大比較を、kernelの射について整合させる。

## 方針
H⁰計算の自然性と既存の主導来kernel射の定義を用い、同じ解像度族の比較を証明する。

## 規約と注意
任意可換環・独立宇宙。局所Hom K-flat条件は不要。

## 使われ方
U16aの合成比較をkernel射に自然な族にまとめるための計算API。
-/

@[expose] public section KernelAugmentationNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  {P P' : BimoduleCategory A E D} (f : P ⟶ P')

/-- H⁰計算同型は、任意の通常kernel射に自然。 -/
lemma kernelTensorHomotopyComputation_kernel_naturality (M : ModuleCategory A D) :
    (moduleHomotopyToDerivedClosed A E).map
        ((kernelTensorHomotopyMap A D E f).app ((moduleToHomotopy A D).obj M)) ≫
        (kernelTensorHomotopyComputation A D E (BimoduleCategory.underlying A E D P') M).hom =
      (kernelTensorHomotopyComputation A D E (BimoduleCategory.underlying A E D P) M).hom ≫
        (moduleToDerived A E).map ((kernelTensorMap A D E f).app M) := by
  have h := (moduleToHomotopyDerivedIso A E).hom.naturality
    ((kernelTensorMap A D E f).app M)
  simp only [Functor.comp_map] at h
  simp only [kernelTensorHomotopyComputation, Iso.trans_hom, Functor.mapIso_hom,
    kernelTensorHomotopyMap_app, eqToIso_refl, Iso.refl_hom,
    CategoryTheory.Functor.map_id, Iso.app_hom]
  erw [Category.id_comp, Category.id_comp]
  exact h

/-- 任意指定解像度の計算同型はkernel射について自然。 -/
lemma kernelResolutionDerivedTensorComputation_kernel_naturality
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (M : ModuleCategory A D) :
    (kernelResolutionDerivedTensorMap A D E R f).app ((moduleToDerived A D).obj M) ≫
        (kernelResolutionDerivedTensorComputation A D E
          (BimoduleCategory.underlying A E D P') R M).hom =
      (kernelResolutionDerivedTensorComputation A D E
          (BimoduleCategory.underlying A E D P) R M).hom ≫
        (moduleToDerived A E).map ((kernelTensorMap A D E f).app (R M).obj) := by
  have h := (whiskerRight (kernelTensorHomotopyMap A D E f)
    (moduleHomotopyToDerivedClosed A E)).naturality
    (moduleDerivedResolutionComputation A D R M).hom
  dsimp only [Functor.comp_map] at h
  dsimp only [kernelResolutionDerivedTensorComputation, Iso.trans_hom,
    Functor.mapIso_hom]
  change _ ≫ (_ ≫ _) = _
  rw [← Category.assoc]
  erw [← h]
  rw [Category.assoc]
  dsimp only [whiskerRight_app]
  erw [kernelTensorHomotopyComputation_kernel_naturality A D E f (R M).obj]
  rw [Category.assoc]
  rfl

/-- 解像度から通常tensorへの増大比較はkernel射に自然。 -/
lemma kernelDerivedTensorAugmentation_kernel_naturality (M : ModuleCategory A D) :
    (kernelResolutionDerivedTensorMap A D E (moduleCanonicalProjectiveResolution A D) f).app
        ((moduleToDerived A D).obj M) ≫
        (kernelDerivedTensorAugmentation A D E (BimoduleCategory.underlying A E D P')).app M =
      (kernelDerivedTensorAugmentation A D E (BimoduleCategory.underlying A E D P)).app M ≫
        (moduleToDerived A E).map ((kernelTensorMap A D E f).app M) := by
  rw [kernelDerivedTensorAugmentation_app, kernelDerivedTensorAugmentation_app]
  rw [← Category.assoc, kernelResolutionDerivedTensorComputation_kernel_naturality]
  rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun k =>
    (kernelResolutionDerivedTensorComputation A D E (BimoduleCategory.underlying A E D P)
      (moduleCanonicalProjectiveResolution A D) M).hom ≫ (moduleToDerived A E).map k)
    ((kernelTensorMap A D E f).naturality (moduleCanonicalProjectiveResolution A D M).π).symm

/-- 解像度tensorモデルのkernel変数に関する自然変換。 -/
def kernelResolutionTensorModelMap
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    kernelResolutionTensorModelFunctor A D E (BimoduleCategory.underlying A E D P) R ⟶
      kernelResolutionTensorModelFunctor A D E (BimoduleCategory.underlying A E D P') R where
  app M := (moduleToDerived A E).map ((kernelTensorMap A D E f).app (R M).obj)
  naturality {M N} g := by
    rw [kernelResolutionTensorModelFunctor_map, kernelResolutionTensorModelFunctor_map]
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (moduleToDerived A E).map
      ((kernelTensorMap A D E f).naturality ((R M).lift (R N) g))

/-- 解像度モデルの比較はkernel射にも自然。 -/
lemma kernelResolutionTensorModelIso_kernel_naturality
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    whiskerLeft (moduleToDerived A D) (kernelResolutionDerivedTensorMap A D E R f) ≫
        (kernelResolutionTensorModelIso A D E (BimoduleCategory.underlying A E D P') R).hom =
      (kernelResolutionTensorModelIso A D E (BimoduleCategory.underlying A E D P) R).hom ≫
        kernelResolutionTensorModelMap A D E f R := by
  apply NatTrans.ext
  funext M
  have h := kernelResolutionDerivedTensorComputation_kernel_naturality A D E f R M
  simp only [kernelResolutionDerivedTensorComputation, Iso.trans_hom, Functor.mapIso_hom,
    moduleDerivedResolutionComputation, Iso.app_hom] at h
  simp only [NatTrans.comp_app, whiskerLeft_app, kernelResolutionTensorModelMap,
    kernelResolutionTensorModelIso, Iso.trans_hom, whiskerRight_app,
    Iso.symm_hom, Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
    Functor.isoCopyObj_hom_app]
  erw [Category.id_comp, Category.id_comp]
  exact h

end SerrePositivity.DifferentialGraded.Morita
end

end KernelAugmentationNaturality

/-! ## CoherenceProjectiveExt（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceProjectiveExt.lean） -/

/-! # 射影入力上での主導来自然変換の一致判定

## 概要
主導来入力の自然変換は、射影的な通常入力の局所化像での成分から判定できる。

## 方針
標準射影解像度の増大は主局所化で同型であり、その自然性squareで成分を運ぶ。

## 規約と注意
終域は任意圏。dg圏の分解・局所Hom K-flat性を要求しない。

## 使われ方
U16aの単位・結合coherenceを同じ射影入力モデルへ帰着する。
-/

@[expose] public section CoherenceProjectiveExt
universe u v w w'

noncomputable section
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  {C : Type w} [Category.{w'} C]

/-- 主導来自然変換の成分は射影的通常入力だけで判定できる。 -/
lemma kernelActionNatTrans_ext_projective {F G : DerivedModuleCategory A D ⥤ C} {α β : F ⟶ G}
    (h : ∀ M : ModuleCategory A D, moduleHomotopicallyProjective A D M →
      α.app ((moduleToDerived A D).obj M) = β.app ((moduleToDerived A D).obj M)) : α = β := by
  apply moduleDerivedNatTrans_ext A D
  intro M
  let R := moduleCanonicalProjectiveResolution A D M
  have := moduleToDerived_inverts A D R.π R.quasiIso
  apply (cancel_epi (F.map ((moduleToDerived A D).map R.π))).1
  rw [α.naturality, β.naturality, h R.obj R.projective]

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceProjectiveExt

/-! ## CoherenceCompositionClosed（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceCompositionClosed.lean） -/

/-! # 通常kernel作用の合成と既存bimodule結合子

## 概要
二つの通常kernelの作用を順に行う関手を、合成kernelの通常作用へ比較する。

## 方針
主Homへの射を各出力対象で評価して入れ子表示を同定し、既存の全Hom自然な結合子を使う。

## 規約と注意
各dg圏のSmall.{u}を明示し、通常合成にはlocalHomKFlatを要求しない。
導来化した合成比較の同型性は、別途相対K-flatモデルを用いて証明する。

## 使われ方
U16aのkernelCompositionIsoを、通常結合子と入力の解像度計算へ接続する。
-/

@[expose] public section CoherenceCompositionClosed
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  (P : Bimodule A E D) (Q : Bimodule A F E)

/-- 二つのtensor作用の主Hom mapは、既存bimodule合成の入れ子表示のmapに一致する。 -/
lemma kernelTensorComposition_map (M N : RightModule A D) :
    (kernelTensor A D E P).map M N ≫
        (kernelTensor A E F Q).map ((kernelTensor A D E P).obj M)
          ((kernelTensor A D E P).obj N) =
      (BimoduleTensor.compose A F E (RightModule A D) Q
        (BimoduleTensor.compose A E D (RightModule A D) P
          (DGFunctor.id (RightModule A D)))).toFunctor.map M N := by
  apply moduleHom_ext
  intro f
  rw [Category.assoc, kernelTensor_map_π A E F Q]
  exact (compose_leftMap_π A F E (RightModule A D) Q
    (BimoduleTensor.compose A E D (RightModule A D) P (DGFunctor.id (RightModule A D))) M N f).symm

/-- 二つのtensor dg関手の合成と、同じ入れ子bimoduleのdg関手表示は一致する。 -/
lemma kernelTensorComposition_eq :
    (kernelTensor A D E P).comp (kernelTensor A E F Q) =
      (BimoduleTensor.compose A F E (RightModule A D) Q
        (BimoduleTensor.compose A E D (RightModule A D) P
          (DGFunctor.id (RightModule A D)))).toFunctor := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (kernelTensor A D E P).comp (kernelTensor A E F Q))
    (G := (BimoduleTensor.compose A F E (RightModule A D) Q
      (BimoduleTensor.compose A E D (RightModule A D) P
        (DGFunctor.id (RightModule A D)))).toFunctor) (fun _ => rfl)
  intro M N
  change ((kernelTensor A D E P).map M N ≫
    (kernelTensor A E F Q).map _ _) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact kernelTensorComposition_map A D E F P Q M N

/-- 閉零関手の合成を、入れ子bimoduleの閉零関手へ同定する。 -/
def kernelTensorCompositionSourceIso :
    (kernelTensor A D E P).onClosed ⋙ (kernelTensor A E F Q).onClosed ≅
      (BimoduleTensor.compose A F E (RightModule A D) Q
        (BimoduleTensor.compose A E D (RightModule A D) P
          (DGFunctor.id (RightModule A D)))).toFunctor.onClosed :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M N f
    simp only [Iso.refl_hom, Functor.comp_map, Category.comp_id, Category.id_comp]
    change ForgetEnrichment.homOf (Complex A)
        (ForgetEnrichment.homTo (Complex A)
          (ForgetEnrichment.homOf (Complex A)
            (ForgetEnrichment.homTo (Complex A) f ≫ (kernelTensor A D E P).map _ _)) ≫
          (kernelTensor A E F Q).map _ _) =
      ForgetEnrichment.homOf (Complex A)
        (ForgetEnrichment.homTo (Complex A) f ≫
          (BimoduleTensor.compose A F E (RightModule A D) Q
            (BimoduleTensor.compose A E D (RightModule A D) P
              (DGFunctor.id (RightModule A D)))).toFunctor.map _ _)
    rw [ForgetEnrichment.homTo_homOf, Category.assoc]
    erw [kernelTensorComposition_map A D E F P Q
      (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N)])

/-- 入れ子tensorを合成kernelの作用へ送る、既存bimodule結合子の閉零表示。 -/
def kernelTensorAssociatorClosedIso :
    (BimoduleTensor.compose A F E (RightModule A D) Q
        (BimoduleTensor.compose A E D (RightModule A D) P
          (DGFunctor.id (RightModule A D)))).toFunctor.onClosed ≅
      (kernelTensor A D F (BimoduleTensor.compose A F E D Q P)).onClosed :=
  NatIso.ofComponents (fun M =>
    (BimoduleCategory.evaluation A F (RightModule A D) (ForgetEnrichment.to (Complex A) M)).mapIso
      (associatorIso A F E D (RightModule A D) Q P (DGFunctor.id (RightModule A D))).symm)
    (fun f => (kernelClosedFamilyNatTrans A F (RightModule A D)
      (associatorIso A F E D (RightModule A D) Q P
        (DGFunctor.id (RightModule A D))).inv).naturality f)

/-- 通常kernel作用の関手合成は、通常合成kernelの作用と自然同型。 -/
def kernelTensorCompositionClosedIso :
    (kernelTensor A D E P).onClosed ⋙ (kernelTensor A E F Q).onClosed ≅
      (kernelTensor A D F (BimoduleTensor.compose A F E D Q P)).onClosed :=
  kernelTensorCompositionSourceIso A D E F P Q ≪≫
    kernelTensorAssociatorClosedIso A D E F P Q

/-- 通常kernelの合成比較を、入力のH⁰商と出力のH⁰商へ自然に降ろした同型。 -/
def kernelTensorCompositionHomotopyIso :
    (kernelTensor A D E P).onHomotopy ⋙ (kernelTensor A E F Q).onHomotopy ≅
      (kernelTensor A D F (BimoduleTensor.compose A F E D Q P)).onHomotopy :=
  CategoryTheory.Quotient.natIsoLift (boundaryRelation A (RightModule A D))
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (eqToIso (kernelTensor A D E P).onHomotopy_fac)
        (kernelTensor A E F Q).onHomotopy ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (kernelTensor A D E P).onClosed
        (eqToIso (kernelTensor A E F Q).onHomotopy_fac) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (kernelTensorCompositionClosedIso A D E F P Q)
        (moduleToHomotopy A F) ≪≫
      (eqToIso (kernelTensor A D F (BimoduleTensor.compose A F E D Q P)).onHomotopy_fac).symm)

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceCompositionClosed

/-! ## CoherenceCompositionKFlat（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceCompositionKFlat.lean） -/

/-! # 右相対K-flat kernelによる導来作用の合成

## 概要
最初のkernelの右相対K-flat性から、二つの主導来作用の合成を通常合成kernelの作用へ比較する。

## 方針
射影入力のtensorが相対K-flatになることをFubiniで示し、自然な解像度モデル上の同型を局所化から延長する。

## 規約と注意
局所Hom条件は不要。最初のkernelの右相対K-flat性を明示し、後のkernelには追加条件を課さない。

## 使われ方
U16aの全導来kernelの合成比較を、U12e-localのK-flat代表による計算へ接続する。
-/

@[expose] public section CoherenceCompositionKFlat
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  (P : Bimodule A E D) (Q : Bimodule A F E)
  (hP : Bimodule.rightRelativeKFlat A E D P)
  (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)

/-- 解像度モデル上で、後のkernelの導来作用を相対K-flat入力計算へ置き換える。 -/
def kernelResolutionTensorCompositionIso :
    kernelResolutionTensorModelFunctor A D E P R ⋙ kernelDerivedTensorOnBimodule A E F Q ≅
      kernelResolutionTensorModelFunctor A D F (BimoduleTensor.compose A F E D Q P) R :=
  NatIso.ofComponents (fun M =>
    kernelRelativeKFlatComputation A E F Q ((kernelTensor A D E P).onClosed.obj (R M).obj)
      (kernelTensor_relativeKFlat A D E P hP (R M).obj
        (moduleHomotopicallyProjective_relativeKFlat A D (R M).projective)) ≪≫
      (moduleToDerived A F).mapIso
        ((kernelTensorCompositionClosedIso A D E F P Q).app (R M).obj)) (by
    intro M N f
    simp only [Functor.comp_map, kernelResolutionTensorModelFunctor_map]
    change (kernelDerivedTensorOnBimodule A E F Q).map
        ((moduleToDerived A E).map ((kernelTensor A D E P).onClosed.map ((R M).lift (R N) f))) ≫
        ((kernelDerivedTensorAugmentation A E F Q).app _ ≫
          (moduleToDerived A F).map
            ((kernelTensorCompositionClosedIso A D E F P Q).hom.app (R N).obj)) =
      ((kernelDerivedTensorAugmentation A E F Q).app _ ≫
          (moduleToDerived A F).map
            ((kernelTensorCompositionClosedIso A D E F P Q).hom.app (R M).obj)) ≫ _
    rw [← Category.assoc]
    have hn := (kernelDerivedTensorAugmentation A E F Q).naturality
      ((kernelTensor A D E P).onClosed.map ((R M).lift (R N) f))
    simp only [Functor.comp_map] at hn
    rw [hn]
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun k => (kernelDerivedTensorAugmentation A E F Q).app _ ≫
      (moduleToDerived A F).map k)
      ((kernelTensorCompositionClosedIso A D E F P Q).hom.naturality ((R M).lift (R N) f)))

/-- 右相対K-flatな最初のkernelについて、主導来作用の合成は通常合成kernelの作用と同型。 -/
def kernelDerivedTensorOnBimoduleCompositionIso :
    kernelDerivedTensorOnBimodule A D E P ⋙ kernelDerivedTensorOnBimodule A E F Q ≅
      kernelDerivedTensorOnBimodule A D F (BimoduleTensor.compose A F E D Q P) := by
  let R := moduleCanonicalProjectiveResolution A D
  let G := kernelDerivedTensorOnBimodule A D E P ⋙ kernelDerivedTensorOnBimodule A E F Q
  let H := kernelDerivedTensorOnBimodule A D F (BimoduleTensor.compose A F E D Q P)
  let e : moduleToDerived A D ⋙ G ≅ moduleToDerived A D ⋙ H :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (kernelResolutionTensorModelIso A D E P R)
        (kernelDerivedTensorOnBimodule A E F Q) ≪≫
      kernelResolutionTensorCompositionIso A D E F P Q hP R ≪≫
      (kernelResolutionTensorModelIso A D F (BimoduleTensor.compose A F E D Q P) R).symm
  exact Localization.liftNatIso (moduleToDerived A D) (moduleQuasiIso A D)
    (moduleToDerived A D ⋙ G) (moduleToDerived A D ⋙ H) G H e

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceCompositionKFlat

/-! ## CoherenceCompositionNaturality（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceCompositionNaturality.lean） -/

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

@[expose] public section CoherenceCompositionNaturality
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end CoherenceCompositionNaturality

/-! ## CoherenceCompositionKFlatNaturality（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceCompositionKFlatNaturality.lean） -/

/-! # K-flat解像度モデル上の導来作用合成のkernel自然性

## 概要
右相対K-flatな最初のkernelの任意の射と、後のkernelの任意の射に関する合成squareを証明する。

## 方針
後の作用の増大のkernel自然性・入力自然性と通常合成の自然性を同じ成分で接続する。

## 規約と注意
任意の入力射影解像度族を使う。局所Hom条件は不要。主導来kernel射への降下は別途行う。

## 使われ方
U16aのkernelCompositionIsoを全kernel射に自然な族へ運ぶモデル上の接続。
-/

@[expose] public section CoherenceCompositionKFlatNaturality
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  {P P' : BimoduleCategory A E D} {Q Q' : BimoduleCategory A F E}
  (f : P ⟶ P') (g : Q ⟶ Q')
local notation "P₀" => BimoduleCategory.underlying A E D P
local notation "P₁" => BimoduleCategory.underlying A E D P'
local notation "Q₀" => BimoduleCategory.underlying A F E Q
local notation "Q₁" => BimoduleCategory.underlying A F E Q'

/-- 解像度モデル上の合成比較の成分を、二つの既存の自然な比較射で計算する。 -/
lemma kernelResolutionTensorCompositionIso_hom_app
    (P : Bimodule A E D) (Q : Bimodule A F E)
    (hP : Bimodule.rightRelativeKFlat A E D P)
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (M : ModuleCategory A D) :
    (kernelResolutionTensorCompositionIso A D E F P Q hP R).hom.app M =
      (kernelDerivedTensorAugmentation A E F Q).app
          ((kernelTensor A D E P).onClosed.obj (R M).obj) ≫
        (moduleToDerived A F).map
          ((kernelTensorCompositionClosedIso A D E F P Q).hom.app (R M).obj) := rfl

/-- 自然な解像度モデル上の合成比較は、両kernelの閉零射に自然。 -/
lemma kernelResolutionTensorCompositionIso_kernel_naturality
    (hP : Bimodule.rightRelativeKFlat A E D P₀)
    (hP' : Bimodule.rightRelativeKFlat A E D P₁)
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    NatTrans.hcomp (kernelResolutionTensorModelMap A D E f R)
        (kernelResolutionDerivedTensorMap A E F (moduleCanonicalProjectiveResolution A E) g) ≫
        (kernelResolutionTensorCompositionIso A D E F P₁ Q₁ hP' R).hom =
      (kernelResolutionTensorCompositionIso A D E F P₀ Q₀ hP R).hom ≫
        kernelResolutionTensorModelMap A D F (BimoduleTensor.composeMap A F E D g f) R := by
  apply NatTrans.ext
  funext M
  have hi := (kernelDerivedTensorAugmentation A E F Q₁).naturality
    ((kernelTensorMap A D E f).app (R M).obj)
  simp only [Functor.comp_map] at hi
  have hk := kernelDerivedTensorAugmentation_kernel_naturality A E F g
    ((kernelTensor A D E P₀).onClosed.obj (R M).obj)
  have hc := congrArg (moduleToDerived A F).map
    (NatTrans.congr_app (kernelTensorCompositionClosedIso_kernel_naturality A D E F f g)
      (R M).obj)
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, Functor.map_comp] at hc
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, Category.assoc]
  rw [kernelResolutionTensorCompositionIso_hom_app,
    kernelResolutionTensorCompositionIso_hom_app]
  dsimp only [kernelResolutionTensorModelMap]
  slice_lhs 2 3 => erw [hi]
  slice_lhs 1 2 => erw [hk]
  simp only [Category.assoc]
  simpa only [Category.assoc] using congrArg (fun k =>
    (kernelDerivedTensorAugmentation A E F Q₀).app
    ((kernelTensor A D E P₀).onClosed.obj (R M).obj) ≫ k) hc

/-- 全導来入力へ延長した通常kernel合成比較は、元の入力では指定モデルの比較を計算する。 -/
lemma kernelDerivedTensorOnBimoduleCompositionIso_hom_app
    (P : Bimodule A E D) (Q : Bimodule A F E)
    (hP : Bimodule.rightRelativeKFlat A E D P) (M : ModuleCategory A D) :
    (kernelDerivedTensorOnBimoduleCompositionIso A D E F P Q hP).hom.app
        ((moduleToDerived A D).obj M) =
      ((kernelDerivedTensorOnBimodule A E F Q).map
          ((kernelResolutionTensorModelIso A D E P
            (moduleCanonicalProjectiveResolution A D)).hom.app M) ≫
        (kernelResolutionTensorCompositionIso A D E F P Q hP
          (moduleCanonicalProjectiveResolution A D)).hom.app M) ≫
        (kernelResolutionTensorModelIso A D F (BimoduleTensor.compose A F E D Q P)
          (moduleCanonicalProjectiveResolution A D)).inv.app M := by
  simp only [kernelDerivedTensorOnBimoduleCompositionIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app]
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, whiskerRight_app, Functor.associator_inv_app]
  erw [Category.id_comp, Category.comp_id, Category.id_comp]
  rw [Category.assoc]

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceCompositionKFlatNaturality

/-! ## CoherenceCompositionAugmentation（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceCompositionAugmentation.lean） -/

/-! # 導来作用合成と通常tensor増大の互換性

## 概要
主導来作用の合成比較を、解像度の増大を通して通常のtensor結合比較へ接続する。

## 方針
同じ標準解像度の計算同型を消去し、増大と通常結合比較の入力自然性を使う。

## 規約と注意
最初のkernelの右相対K-flat性を明示し、局所Hom K-flat性は要求しない。

## 使われ方
U16aの単位・結合の作用coherenceを通常のbimoduleのcoherenceに帰着する。
-/

@[expose] public section CoherenceCompositionAugmentation
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 自然な解像度モデルの成分は指定解像度の計算同型そのもの。 -/
lemma kernelResolutionTensorModelIso_hom_app (P : Bimodule A E D)
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : ModuleCategory A D) :
    (kernelResolutionTensorModelIso A D E P R).hom.app M =
      (kernelResolutionDerivedTensorComputation A D E P R M).hom := by
  simp only [kernelResolutionTensorModelIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, whiskerRight_app,
    kernelResolutionDerivedTensorComputation, Functor.mapIso_hom]
  erw [Category.id_comp]
  rfl

/-- 自然な標準解像度モデルと通常tensor増大の可換square。 -/
lemma kernelResolutionTensorModelIso_augmentation (P : Bimodule A E D)
    (M : ModuleCategory A D) :
    (kernelResolutionTensorModelIso A D E P
        (moduleCanonicalProjectiveResolution A D)).hom.app M ≫
      (moduleToDerived A E).map
        ((kernelTensor A D E P).onClosed.map (moduleCanonicalProjectiveResolution A D M).π) =
      (kernelDerivedTensorAugmentation A D E P).app M := by
  rw [kernelResolutionTensorModelIso_hom_app]
  exact (kernelDerivedTensorAugmentation_app A D E P M).symm

variable (F : Type z) [DGCategory A F] [Small.{u} F]

/-- 導来合成比較と増大を通る経路は、二つの増大と通常合成比較を通る経路に一致する。 -/
lemma kernelDerivedTensorOnBimoduleCompositionIso_augmentation
    (P : Bimodule A E D) (Q : Bimodule A F E)
    (hP : Bimodule.rightRelativeKFlat A E D P) (M : ModuleCategory A D) :
    (kernelDerivedTensorOnBimoduleCompositionIso A D E F P Q hP).hom.app
        ((moduleToDerived A D).obj M) ≫
      (kernelDerivedTensorAugmentation A D F (BimoduleTensor.compose A F E D Q P)).app M =
    (kernelDerivedTensorOnBimodule A E F Q).map
        ((kernelDerivedTensorAugmentation A D E P).app M) ≫
      (kernelDerivedTensorAugmentation A E F Q).app ((kernelTensor A D E P).onClosed.obj M) ≫
        (moduleToDerived A F).map ((kernelTensorCompositionClosedIso A D E F P Q).hom.app M) := by
  let R := moduleCanonicalProjectiveResolution A D
  let C := BimoduleTensor.compose A F E D Q P
  let π := (R M).π
  let eP := (kernelResolutionTensorModelIso A D E P R).app M
  let eC := (kernelResolutionTensorModelIso A D F C R).app M
  have hC : eC.inv ≫ (kernelDerivedTensorAugmentation A D F C).app M =
      (moduleToDerived A F).map ((kernelTensor A D F C).onClosed.map π) := by
    rw [← kernelResolutionTensorModelIso_augmentation A D F C M]
    exact eC.inv_hom_id_assoc _
  have hN := (kernelTensorCompositionClosedIso A D E F P Q).hom.naturality π
  simp only [Functor.comp_map] at hN
  have hNc := congrArg (moduleToDerived A F).map hN
  simp only [Functor.map_comp] at hNc
  have hA := (kernelDerivedTensorAugmentation A E F Q).naturality
    ((kernelTensor A D E P).onClosed.map π)
  simp only [Functor.comp_map] at hA
  rw [kernelDerivedTensorOnBimoduleCompositionIso_hom_app,
    kernelResolutionTensorCompositionIso_hom_app]
  change (((kernelDerivedTensorOnBimodule A E F Q).map eP.hom ≫
    (kernelDerivedTensorAugmentation A E F Q).app ((kernelTensor A D E P).onClosed.obj (R M).obj) ≫
    (moduleToDerived A F).map ((kernelTensorCompositionClosedIso A D E F P Q).hom.app (R M).obj)) ≫
    eC.inv) ≫ _ = _
  rw [Category.assoc, hC]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [← hNc]
  slice_lhs 2 3 => erw [← hA]
  simp only [Category.assoc]
  slice_lhs 1 2 => rw [← Functor.map_comp]
  have hPaug := kernelResolutionTensorModelIso_augmentation A D E P M
  change eP.hom ≫ (moduleToDerived A E).map ((kernelTensor A D E P).onClosed.map π) = _ at hPaug
  rw [hPaug, Category.assoc]

/-- 相対K-flat入力では、導来合成比較は通常合成の同じ計算図式を与える。 -/
lemma kernelDerivedTensorOnBimoduleCompositionIso_relativeKFlat
    (P : Bimodule A E D) (Q : Bimodule A F E)
    (hP : Bimodule.rightRelativeKFlat A E D P) (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    (kernelDerivedTensorOnBimoduleCompositionIso A D E F P Q hP).app
        ((moduleToDerived A D).obj M) ≪≫
      kernelRelativeKFlatComputation A D F (BimoduleTensor.compose A F E D Q P) M hM =
    (kernelDerivedTensorOnBimodule A E F Q).mapIso (kernelRelativeKFlatComputation A D E P M hM) ≪≫
      kernelRelativeKFlatComputation A E F Q ((kernelTensor A D E P).onClosed.obj M)
        (kernelTensor_relativeKFlat A D E P hP M hM) ≪≫
      (moduleToDerived A F).mapIso ((kernelTensorCompositionClosedIso A D E F P Q).app M) := by
  apply Iso.ext
  exact kernelDerivedTensorOnBimoduleCompositionIso_augmentation A D E F P Q hP M

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceCompositionAugmentation

/-! ## CoherenceCompositionDerivedNaturality（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceCompositionDerivedNaturality.lean） -/

/-! # 全導来入力上の通常kernel合成比較の自然性

## 概要
右相対K-flatな最初のkernelと任意の後のkernelの作用合成比較を、両kernelの射に自然にする。

## 方針
解像度モデルとの比較squareを合成し、指定主局所化からの自然変換の一意性を使う。

## 規約と注意
局所Hom K-flat条件は不要。kernelの主局所化に関する自然性は別途降ろす。

## 使われ方
U16aの全導来kernel合成比較をkernel射に自然な族にまとめるための接続。
-/

@[expose] public section CoherenceCompositionDerivedNaturality
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  {P P' : BimoduleCategory A E D} {Q Q' : BimoduleCategory A F E}
  (f : P ⟶ P') (g : Q ⟶ Q')
local notation "P₀" => BimoduleCategory.underlying A E D P
local notation "P₁" => BimoduleCategory.underlying A E D P'
local notation "Q₀" => BimoduleCategory.underlying A F E Q
local notation "Q₁" => BimoduleCategory.underlying A F E Q'
local notation "R" => moduleCanonicalProjectiveResolution A D
local notation "S" => moduleCanonicalProjectiveResolution A E

/-- 二つの作用射の水平合成と、最初の作用の解像度モデル比較が可換。 -/
lemma kernelCompositionSourceModelSquare (M : ModuleCategory A D) :
    (NatTrans.hcomp (kernelResolutionDerivedTensorMap A D E R f)
        (kernelResolutionDerivedTensorMap A E F S g)).app ((moduleToDerived A D).obj M) ≫
        (kernelDerivedTensorOnBimodule A E F Q₁).map
          ((kernelResolutionTensorModelIso A D E P₁ R).hom.app M) =
      (kernelDerivedTensorOnBimodule A E F Q₀).map
          ((kernelResolutionTensorModelIso A D E P₀ R).hom.app M) ≫
        (NatTrans.hcomp (kernelResolutionTensorModelMap A D E f R)
          (kernelResolutionDerivedTensorMap A E F S g)).app M := by
  have hf := congrArg (kernelDerivedTensorOnBimodule A E F Q₁).map
    (NatTrans.congr_app (kernelResolutionTensorModelIso_kernel_naturality A D E f R) M)
  simp only [NatTrans.comp_app, whiskerLeft_app, Functor.map_comp] at hf
  have hg := (kernelResolutionDerivedTensorMap A E F S g).naturality
    ((kernelResolutionTensorModelIso A D E P₀ R).hom.app M)
  simp only [NatTrans.hcomp_app, Category.assoc]
  slice_lhs 2 3 => erw [hf]
  slice_lhs 1 2 => erw [← hg]
  rw [Category.assoc]
  rfl

/-- 通常kernelの主導来作用の合成比較は、両kernelの閉零射に自然。 -/
lemma kernelDerivedTensorOnBimoduleCompositionIso_kernel_naturality
    (hP : Bimodule.rightRelativeKFlat A E D P₀)
    (hP' : Bimodule.rightRelativeKFlat A E D P₁) :
    NatTrans.hcomp (kernelResolutionDerivedTensorMap A D E R f)
        (kernelResolutionDerivedTensorMap A E F S g) ≫
        (kernelDerivedTensorOnBimoduleCompositionIso A D E F P₁ Q₁ hP').hom =
      (kernelDerivedTensorOnBimoduleCompositionIso A D E F P₀ Q₀ hP).hom ≫
        kernelResolutionDerivedTensorMap A D F R (BimoduleTensor.composeMap A F E D g f) := by
  apply Localization.natTrans_ext (moduleToDerived A D) (moduleQuasiIso A D)
  intro M
  have hs := kernelCompositionSourceModelSquare A D E F f g M
  have ht := NatTrans.congr_app (kernelResolutionTensorModelIso_kernel_naturality A D F
    (BimoduleTensor.composeMap A F E D g f) R) M
  simp only [NatTrans.comp_app, whiskerLeft_app] at ht
  change (kernelResolutionDerivedTensorMap A D F R
      (BimoduleTensor.composeMap A F E D g f)).app ((moduleToDerived A D).obj M) ≫
      (kernelResolutionTensorModelIso A D F (BimoduleTensor.compose A F E D Q₁ P₁) R).hom.app M =
    (kernelResolutionTensorModelIso A D F (BimoduleTensor.compose A F E D Q₀ P₀) R).hom.app M ≫
      (kernelResolutionTensorModelMap A D F (BimoduleTensor.composeMap A F E D g f) R).app M at ht
  have hm := NatTrans.congr_app
    (kernelResolutionTensorCompositionIso_kernel_naturality A D E F f g hP hP' R) M
  simp only [NatTrans.comp_app] at hm
  simp only [NatTrans.comp_app]
  rw [kernelDerivedTensorOnBimoduleCompositionIso_hom_app,
    kernelDerivedTensorOnBimoduleCompositionIso_hom_app]
  apply (cancel_mono ((kernelResolutionTensorModelIso A D F
    (BimoduleTensor.compose A F E D Q₁ P₁) R).hom.app M)).1
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  slice_rhs 4 5 => erw [ht]
  slice_rhs 3 4 => erw [Iso.inv_hom_id_app]
  slice_lhs 1 2 => erw [hs]
  slice_lhs 2 3 => erw [hm]
  simp only [Category.id_comp]

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceCompositionDerivedNaturality

/-! ## CoherenceCompositionNaturalIso（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceCompositionNaturalIso.lean） -/

/-! # 全導来kernel射に自然な作用合成の同型

## 概要
二つの主導来kernelの作用合成を、導来合成kernelの作用へ自然な族として比較する。

## 方針
K-flat代表上の三つの自然な比較を合成し、指定準同型の積局所化から自然同型を延長する。

## 規約と注意
任意可換環・非有界。必要な局所Hom条件は始域Dだけ。分解変更の一般経路は経由しない。

## 使われ方
U16aの公開kernelCompositionIsoを全kernel射に自然な同型として実装し、U16dのhNatを供給する。
-/

@[expose] public section CoherenceCompositionNaturalIso
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]

/-- モデル上の導来合成kernelの作用を、通常合成kernelの作用へ計算する同型。 -/
def kernelCompositionTargetIso (hD : localHomKFlat A D)
    (P : RightKFlatBimoduleCategory A E D) (Q : BimoduleCategory A F E) :
    kernelDerivedTensor A D F (kernelCompose A D E F hD
        ((bimoduleToDerived A E D).obj P.obj) ((bimoduleToDerived A F E).obj Q)) ≅
      kernelDerivedTensorOnBimodule A D F
        (BimoduleTensor.compose A F E D (BimoduleCategory.underlying A F E Q)
          (BimoduleCategory.underlying A E D P.obj)) :=
  (kernelDerivedTensorFunctor A D F).mapIso
      (derivedBimoduleComposeKFlatValueIso A F E D hD P Q) ≪≫
    kernelDerivedTensorOnBimoduleIso A D F (BimoduleCategory.of A F D
      (BimoduleTensor.compose A F E D (BimoduleCategory.underlying A F E Q)
        (BimoduleCategory.underlying A E D P.obj)))

/-- 導来合成kernelのモデル計算は、両kernel射に自然。 -/
lemma kernelCompositionTargetIso_naturality (hD : localHomKFlat A D)
    {P P' : RightKFlatBimoduleCategory A E D} {Q Q' : BimoduleCategory A F E}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (kernelDerivedTensorFunctor A D F).map
        (kernelComposeMap A D E F hD ((bimoduleToDerived A E D).map f.hom)
          ((bimoduleToDerived A F E).map g)) ≫
        (kernelCompositionTargetIso A D E F hD P' Q').hom =
      (kernelCompositionTargetIso A D E F hD P Q).hom ≫
        kernelResolutionDerivedTensorMap A D F (moduleCanonicalProjectiveResolution A D)
          (composeMap A F E D g f.hom) := by
  have hv := congrArg (kernelDerivedTensorFunctor A D F).map
    (kernelComposeKFlatValueIso_naturality A D E F hD f g)
  simp only [Functor.map_comp] at hv
  have he := kernelDerivedTensorOnBimoduleIso_naturality A D F (composeMap A F E D g f.hom)
  dsimp only [kernelCompositionTargetIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hv, Category.assoc, he, ← Category.assoc]

/-- K-flat代表と通常代表の上の、自然な三つの比較を合成した作用合成同型。 -/
def kernelCompositionModelIso (hD : localHomKFlat A D)
    (P : RightKFlatBimoduleCategory A E D) (Q : BimoduleCategory A F E) :
    kernelDerivedTensor A D E ((bimoduleToDerived A E D).obj P.obj) ⋙
        kernelDerivedTensor A E F ((bimoduleToDerived A F E).obj Q) ≅
      kernelDerivedTensor A D F (kernelCompose A D E F hD
        ((bimoduleToDerived A E D).obj P.obj) ((bimoduleToDerived A F E).obj Q)) :=
  NatIso.hcomp (kernelDerivedTensorOnBimoduleIso A D E P.obj)
      (kernelDerivedTensorOnBimoduleIso A E F Q) ≪≫
    kernelDerivedTensorOnBimoduleCompositionIso A D E F
      (BimoduleCategory.underlying A E D P.obj) (BimoduleCategory.underlying A F E Q)
      P.property ≪≫
    (kernelCompositionTargetIso A D E F hD P Q).symm

/-- K-flatモデル上の作用合成同型は、両kernelの任意の射に自然。 -/
lemma kernelCompositionModelIso_naturality (hD : localHomKFlat A D)
    {P P' : RightKFlatBimoduleCategory A E D} {Q Q' : BimoduleCategory A F E}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    NatTrans.hcomp
        ((kernelDerivedTensorFunctor A D E).map ((bimoduleToDerived A E D).map f.hom))
        ((kernelDerivedTensorFunctor A E F).map ((bimoduleToDerived A F E).map g)) ≫
        (kernelCompositionModelIso A D E F hD P' Q').hom =
      (kernelCompositionModelIso A D E F hD P Q).hom ≫
        (kernelDerivedTensorFunctor A D F).map
          (kernelComposeMap A D E F hD ((bimoduleToDerived A E D).map f.hom)
            ((bimoduleToDerived A F E).map g)) := by
  have hs := kernelDerivedTensorOnBimoduleIso_hcomp_naturality A D E F f.hom g
  have hm := kernelDerivedTensorOnBimoduleCompositionIso_kernel_naturality A D E F
    f.hom g P.property P'.property
  have ht := kernelCompositionTargetIso_naturality A D E F hD f g
  dsimp only [kernelCompositionModelIso, Iso.trans_hom, Iso.symm_hom]
  apply (cancel_mono (kernelCompositionTargetIso A D E F hD P' Q').hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  slice_rhs 4 5 => rw [ht]
  slice_rhs 3 4 => rw [Iso.inv_hom_id]
  slice_lhs 1 2 => rw [hs]
  slice_lhs 2 3 => rw [hm]
  simp only [Category.id_comp]

/-- 指定モデルの積圏上で作用合成比較を自然同型へ束ねる。 -/
def kernelCompositionModelNatIso (hD : localHomKFlat A D) :
    kernelCompositionModels A D E F ⋙ kernelActionCompositionBifunctor A D E F ≅
      kernelCompositionModels A D E F ⋙ kernelCompositeActionBifunctor A D E F hD :=
  NatIso.ofComponents (fun X => kernelCompositionModelIso A D E F hD X.1 X.2) (by
    intro X Y f
    simp only [Functor.comp_map, kernelActionCompositionBifunctor_map,
      kernelCompositeActionBifunctor_map]
    exact kernelCompositionModelIso_naturality A D E F hD f.1 f.2)

/-- 全主導来kernelの積圏上の、任意のkernel射に自然な作用合成同型。 -/
def kernelCompositionNaturalIso (hD : localHomKFlat A D) :
    kernelActionCompositionBifunctor A D E F ≅ kernelCompositeActionBifunctor A D E F hD := by
  let := kernelCompositionModels_isLocalization A D E F hD
  exact Localization.liftNatIso (kernelCompositionModels A D E F)
    (kernelCompositionModelQuasiIso A D E F)
    (kernelCompositionModels A D E F ⋙ kernelActionCompositionBifunctor A D E F)
    (kernelCompositionModels A D E F ⋙ kernelCompositeActionBifunctor A D E F hD)
    (kernelActionCompositionBifunctor A D E F) (kernelCompositeActionBifunctor A D E F hD)
    (kernelCompositionModelNatIso A D E F hD)

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceCompositionNaturalIso
