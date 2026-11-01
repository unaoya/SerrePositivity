module

public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKernel
public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Pentagon
public import SerrePositivity.DifferentialGraded.Morita.Kernel

/-!
# Morita.CoherenceAssociator

## 概要
15 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

universe u v w z t x

/-! ## CoherenceComposition（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceComposition.lean） -/

/-! # 主導来kernelの作用の合成比較

## 概要
両kernelが指定bimodule局所化の任意対象であるとき、作用の合成を導来合成kernelの作用へ比較する。

## 方針
K-flat代表上の自然な作用比較を、指定準同型の積局所化から全kernelへ延長する。

## 規約と注意
kernelはD→Eについて右E・左D。必要な局所Hom条件は始域Dだけ。
入力導来加群と全導来kernel射に自然。単位・結合coherenceは別途検証する。

## 使われ方
U16aの公開kernelCompositionIsoと、U16dのPerf合成比較の具体的入力を提供する。
-/

@[expose] public section CoherenceComposition

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]

/-- K-flat代表と通常代表について、導来合成kernelの作用を実際の通常合成作用へ比較する。 -/
def kernelCompositionKFlatIso (hD : localHomKFlat A D)
    (P : RightKFlatBimoduleCategory A E D) (Q : BimoduleCategory A F E) :
    kernelDerivedTensor A D E ((bimoduleToDerived A E D).obj P.obj) ⋙
        kernelDerivedTensor A E F ((bimoduleToDerived A F E).obj Q) ≅
      kernelDerivedTensor A D F
        (kernelCompose A D E F hD ((bimoduleToDerived A E D).obj P.obj)
          ((bimoduleToDerived A F E).obj Q)) :=
  Functor.isoWhiskerRight (kernelDerivedTensorOnBimoduleIso A D E P.obj)
      (kernelDerivedTensor A E F ((bimoduleToDerived A F E).obj Q)) ≪≫
    Functor.isoWhiskerLeft
      (kernelDerivedTensorOnBimodule A D E (BimoduleCategory.underlying A E D P.obj))
      (kernelDerivedTensorOnBimoduleIso A E F Q) ≪≫
    kernelDerivedTensorOnBimoduleCompositionIso A D E F
      (BimoduleCategory.underlying A E D P.obj) (BimoduleCategory.underlying A F E Q)
      P.property ≪≫
    (kernelDerivedTensorOnBimoduleIso A D F (BimoduleCategory.of A F D
      (BimoduleTensor.compose A F E D (BimoduleCategory.underlying A F E Q)
        (BimoduleCategory.underlying A E D P.obj)))).symm ≪≫
    (kernelDerivedTensorFunctor A D F).mapIso
      (derivedBimoduleComposeKFlatValueIso A F E D hD P Q).symm

/-- 任意の主導来kernelの作用の合成比較。必要な局所Hom条件はDだけ。 -/
def kernelCompositionIso (hD : localHomKFlat A D)
    (P : Kernel A D E) (Q : Kernel A E F) :
    kernelDerivedTensor A D E P ⋙ kernelDerivedTensor A E F Q ≅
      kernelDerivedTensor A D F (kernelCompose A D E F hD P Q) :=
  (kernelCompositionNaturalIso A D E F hD).app (P, Q)

/-- 公開した作用合成比較は、両kernelの任意の主導来射に自然。 -/
lemma kernelCompositionIso_naturality (hD : localHomKFlat A D)
    {P P' : Kernel A D E} {Q Q' : Kernel A E F} (f : P ⟶ P') (g : Q ⟶ Q') :
    NatTrans.hcomp ((kernelDerivedTensorFunctor A D E).map f)
        ((kernelDerivedTensorFunctor A E F).map g) ≫
        (kernelCompositionIso A D E F hD P' Q').hom =
      (kernelCompositionIso A D E F hD P Q).hom ≫
        (kernelDerivedTensorFunctor A D F).map (kernelComposeMap A D E F hD f g) := by
  have h := (kernelCompositionNaturalIso A D E F hD).hom.naturality
    (show (P, Q) ⟶ (P', Q') from (f, g))
  simp only [kernelActionCompositionBifunctor_map, kernelCompositeActionBifunctor_map] at h
  exact h

/-- 公開合成比較はK-flat代表上では、同じ指定モデルの自然な比較そのものを計算する。 -/
lemma kernelCompositionIso_model (hD : localHomKFlat A D)
    (P : RightKFlatBimoduleCategory A E D) (Q : BimoduleCategory A F E) :
    kernelCompositionIso A D E F hD ((bimoduleToDerived A E D).obj P.obj)
        ((bimoduleToDerived A F E).obj Q) =
      kernelCompositionModelIso A D E F hD P Q := by
  apply Iso.ext
  change (kernelCompositionNaturalIso A D E F hD).hom.app
    ((kernelCompositionModels A D E F).obj (P, Q)) = _
  simp only [kernelCompositionNaturalIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app]
  change 𝟙 _ ≫ (kernelCompositionModelNatIso A D E F hD).hom.app (P, Q) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]
  rfl

/-- 自然なモデル比較は、既存のK-flat代表上の合成比較と一致する。 -/
lemma kernelCompositionModelIso_eq_kFlat (hD : localHomKFlat A D)
    (P : RightKFlatBimoduleCategory A E D) (Q : BimoduleCategory A F E) :
    kernelCompositionModelIso A D E F hD P Q = kernelCompositionKFlatIso A D E F hD P Q := by
  apply Iso.ext
  simp only [kernelCompositionModelIso, kernelCompositionKFlatIso, kernelCompositionTargetIso,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatIso.hcomp_hom,
    NatTrans.hcomp_eq_whiskerRight_comp_whiskerLeft, Category.assoc]

/-- 全導来kernelの公開比較は、K-flat代表上で既存の計算比較を保つ。 -/
lemma kernelCompositionIso_kFlat (hD : localHomKFlat A D)
    (P : RightKFlatBimoduleCategory A E D) (Q : BimoduleCategory A F E) :
    kernelCompositionIso A D E F hD ((bimoduleToDerived A E D).obj P.obj)
        ((bimoduleToDerived A F E).obj Q) = kernelCompositionKFlatIso A D E F hD P Q := by
  rw [kernelCompositionIso_model, kernelCompositionModelIso_eq_kFlat]

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceComposition

/-! ## CoherenceCompositionWhisker（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceCompositionWhisker.lean） -/

/-! # 公開作用合成比較の片側自然性

## 概要
両kernelの全導来射に関する既存自然性を、片側のwhiskeringに読み替える。

## 方針
他方の射を恒等に特殊化し、主導来合成の同じ射を計算する。

## 規約と注意
既存の比較を変更しない。合成の始域の局所Hom K-flat性だけを保持する。

## 使われ方
U16aの結合図式でモデル計算の射を合成経路の末尾へ運ぶ。
-/

@[expose] public section CoherenceCompositionWhisker

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]

/-- 最初のkernelの全導来射に関する作用合成比較のwhiskering自然性。 -/
lemma kernelCompositionIso_first_naturality (hD : localHomKFlat A D)
    {P P' : Kernel A D E} (f : P ⟶ P') (Q : Kernel A E F) :
    whiskerRight ((kernelDerivedTensorFunctor A D E).map f) (kernelDerivedTensor A E F Q) ≫
      (kernelCompositionIso A D E F hD P' Q).hom =
    (kernelCompositionIso A D E F hD P Q).hom ≫
      (kernelDerivedTensorFunctor A D F).map
        (((derivedBimoduleComposeFunctor A F E D hD).map f).app Q) := by
  have h := kernelCompositionIso_naturality A D E F hD f (𝟙 Q)
  simp only [kernelComposeMap, CategoryTheory.Functor.map_id] at h
  erw [Category.comp_id] at h
  apply NatTrans.ext
  funext X
  have hx := NatTrans.congr_app h X
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, NatTrans.id_app, whiskerRight_app,
    Category.id_comp] at hx ⊢
  convert hx using 1
  rfl

/-- 後のkernelの全導来射に関する作用合成比較のwhiskering自然性。 -/
lemma kernelCompositionIso_second_naturality (hD : localHomKFlat A D)
    (P : Kernel A D E) {Q Q' : Kernel A E F} (g : Q ⟶ Q') :
    whiskerLeft (kernelDerivedTensor A D E P) ((kernelDerivedTensorFunctor A E F).map g) ≫
      (kernelCompositionIso A D E F hD P Q').hom =
    (kernelCompositionIso A D E F hD P Q).hom ≫
      (kernelDerivedTensorFunctor A D F).map
        (((derivedBimoduleComposeFunctor A F E D hD).obj P).map g) := by
  have h := kernelCompositionIso_naturality A D E F hD (𝟙 P) g
  simp only [kernelComposeMap, CategoryTheory.Functor.map_id, NatTrans.id_app] at h
  erw [Category.id_comp] at h
  apply NatTrans.ext
  funext X
  have hx := NatTrans.congr_app h X
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, NatTrans.id_app, whiskerLeft_app,
    CategoryTheory.Functor.map_id, Category.comp_id] at hx ⊢
  convert hx using 1
  rfl

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceCompositionWhisker

/-! ## CoherenceIdentityAugmentation（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceIdentityAugmentation.lean） -/

/-! # 恒等kernelの作用比較と通常tensor増大

## 概要
恒等作用の既存比較を、通常の対角tensor単位子と解像度増大へ接続する。

## 方針
H⁰への単位子の降下と主導来局所化での計算を明示し、比較の選択を保つ。

## 規約と注意
局所Hom K-flat性を仮定しない。公開kernelIdentityIsoの定義を変更しない。

## 使われ方
U16aの合成比較と恒等比較の単位coherence。
-/

@[expose] public section CoherenceIdentityAugmentation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- H⁰に降ろした恒等比較の通常入力での成分。 -/
lemma kernelIdentityHomotopyIso_hom_app (M : ModuleCategory A D) :
    (kernelIdentityHomotopyIso A D).hom.app ((moduleToHomotopy A D).obj M) =
      (eqToIso (congrArg (fun G => G.obj M)
        (kernelTensor A D D (Bimodule.diagonal A D)).onHomotopy_fac)).hom ≫
      (moduleToHomotopy A D).map ((kernelIdentityClosedIso A D).hom.app M) := by
  simp only [kernelIdentityHomotopyIso, Quotient.natIsoLift_hom, Quotient.natTransLift_app,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    whiskerRight_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    eqToIso.hom, eqToHom_app]
  erw [Category.comp_id, Category.comp_id]

/-- H⁰恒等比較は元の通常単位子の主導来像を計算する。 -/
lemma kernelIdentityHomotopyIso_computation (M : ModuleCategory A D) :
    (kernelTensorHomotopyComputation A D D (Bimodule.diagonal A D) M).hom ≫
      (moduleToDerived A D).map ((kernelIdentityClosedIso A D).hom.app M) =
    (moduleHomotopyToDerivedClosed A D).map
        ((kernelIdentityHomotopyIso A D).hom.app ((moduleToHomotopy A D).obj M)) ≫
      (moduleToHomotopyDerivedIso A D).hom.app M := by
  have hn := (moduleToHomotopyDerivedIso A D).hom.naturality
    ((kernelIdentityClosedIso A D).hom.app M)
  simp only [Functor.comp_map] at hn
  dsimp only [kernelTensorHomotopyComputation, Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc]
  erw [← hn]
  rw [← Category.assoc, ← Functor.map_comp]
  rw [kernelIdentityHomotopyIso_hom_app]
  rfl

/-- 入力解像度の導来余単位は、通常入力で増大射そのものを計算する。 -/
lemma kernelInputResolutionDerivedCounitIso_hom_app
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : ModuleCategory A D) :
    (kernelInputResolutionDerivedCounitIso A D R).hom.app ((moduleToDerived A D).obj M) =
      (moduleHomotopyToDerivedClosed A D).map
          ((moduleDerivedResolutionFunctor_fac A D R).hom.app M) ≫
        (moduleHomotopyToDerivedClosed A D).map ((moduleToHomotopy A D).map (R M).π) ≫
          (moduleToHomotopyDerivedIso A D).hom.app M := by
  simp only [kernelInputResolutionDerivedCounitIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, whiskerRight_app,
    kernelInputResolutionDerivedAugmentationIso, asIso_hom]
  erw [Category.id_comp, Category.comp_id, Category.id_comp]
  rfl

/-- 導来恒等比較は標準解像度上の通常単位子と入力増大を計算する。 -/
lemma kernelDerivedTensorOnBimoduleIdentityIso_model (M : ModuleCategory A D) :
    (kernelDerivedTensorOnBimoduleIdentityIso A D).hom.app ((moduleToDerived A D).obj M) =
      (kernelResolutionDerivedTensorComputation A D D (Bimodule.diagonal A D)
        (moduleCanonicalProjectiveResolution A D) M).hom ≫
      (moduleToDerived A D).map ((kernelIdentityClosedIso A D).hom.app
        (moduleCanonicalProjectiveResolution A D M).obj) ≫
      (moduleToDerived A D).map (moduleCanonicalProjectiveResolution A D M).π := by
  let R := moduleCanonicalProjectiveResolution A D
  let Γ := (moduleDerivedResolutionFunctor_fac A D R).hom.app M
  let H := moduleHomotopyToDerivedClosed A D
  let τ := kernelIdentityHomotopyIso A D
  have hτ := τ.hom.naturality Γ
  simp only [Functor.id_map] at hτ
  have hτH : H.map (τ.hom.app ((moduleDerivedResolutionFunctor A D R).obj
        ((moduleToDerived A D).obj M))) ≫ H.map Γ =
      H.map ((kernelTensor A D D (Bimodule.diagonal A D)).onHomotopy.map Γ) ≫
        H.map (τ.hom.app ((moduleToHomotopy A D).obj (R M).obj)) := by
    have hh := congrArg H.map hτ
    simp only [H.map_comp] at hh
    exact hh.symm
  have hβ := (moduleToHomotopyDerivedIso A D).hom.naturality (R M).π
  simp only [Functor.comp_map] at hβ
  change (H.map (τ.hom.app _) ≫ 𝟙 _) ≫
    (kernelInputResolutionDerivedCounitIso A D R).hom.app ((moduleToDerived A D).obj M) = _
  rw [Category.comp_id, kernelInputResolutionDerivedCounitIso_hom_app]
  change H.map (τ.hom.app _) ≫ (H.map Γ ≫ H.map ((moduleToHomotopy A D).map (R M).π) ≫
      (moduleToHomotopyDerivedIso A D).hom.app M) =
    (((kernelHomotopyToDerived A D D (Bimodule.diagonal A D)).map Γ ≫
      (kernelTensorHomotopyComputation A D D (Bimodule.diagonal A D) (R M).obj).hom) ≫ _ ≫ _)
  simp only [Category.assoc]
  slice_rhs 2 3 => rw [kernelIdentityHomotopyIso_computation]
  slice_rhs 3 4 => erw [← hβ]
  slice_lhs 1 2 => rw [hτH]
  change ((H.map ((kernelTensor A D D (Bimodule.diagonal A D)).onHomotopy.map Γ) ≫
    H.map (τ.hom.app ((moduleToHomotopy A D).obj (R M).obj))) ≫
    H.map ((moduleToHomotopy A D).map (R M).π)) ≫ (moduleToHomotopyDerivedIso A D).hom.app M =
    H.map ((kernelTensor A D D (Bimodule.diagonal A D)).onHomotopy.map Γ) ≫
      H.map (τ.hom.app ((moduleToHomotopy A D).obj (R M).obj)) ≫
      H.map ((moduleToHomotopy A D).map (R M).π) ≫ (moduleToHomotopyDerivedIso A D).hom.app M
  simp only [Category.assoc]

/-- 導来恒等比較は通常tensor増大と元の対角単位子を通る経路に一致する。 -/
lemma kernelDerivedTensorOnBimoduleIdentityIso_augmentation (M : ModuleCategory A D) :
    (kernelDerivedTensorOnBimoduleIdentityIso A D).hom.app ((moduleToDerived A D).obj M) =
      (kernelDerivedTensorAugmentation A D D (Bimodule.diagonal A D)).app M ≫
        (moduleToDerived A D).map ((kernelIdentityClosedIso A D).hom.app M) := by
  rw [kernelDerivedTensorOnBimoduleIdentityIso_model, kernelDerivedTensorAugmentation_app]
  have h := congrArg (moduleToDerived A D).map
    ((kernelIdentityClosedIso A D).hom.naturality (moduleCanonicalProjectiveResolution A D M).π)
  simp only [Functor.map_comp, Functor.id_map] at h
  simp only [Category.assoc]
  rw [h]

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceIdentityAugmentation

/-! ## CoherenceUnitClosed（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceUnitClosed.lean） -/

/-! # 通常kernel作用の単位coherence

## 概要
通常のkernel合成比較と対角kernelの恒等比較が、既存bimodule単位子と整合する。

## 方針
bimodule射を入力加群で評価して作用の射へ比較し、既存三角図式を同じ評価で運ぶ。

## 規約と注意
局所Hom K-flat性は不要。全右加群型のSmallを仮定しない。

## 使われ方
U16aの公開導来作用の単位coherenceの計算モデル。
-/

@[expose] public section CoherenceUnitClosed

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 入力族のbimodule射をtensorして評価すると、通常kernel作用の入力射になる。 -/
lemma kernelTensorFamilyMap (P : Bimodule A E D)
    (C : Type z) [DGCategory A C] {S T : BimoduleCategory A D C}
    (f : S ⟶ T) (c : C) :
    (BimoduleCategory.evaluation A E C c).map
      (composeMap A E D C (𝟙 (BimoduleCategory.of A E D P)) f) =
    (kernelTensor A D E P).onClosed.map ((BimoduleCategory.evaluation A D C c).map f) := by
  apply moduleMorphism_ext
  intro e
  change (BimoduleCategory.valueEvaluation A E C e c).map
      (composeMap A E D C (𝟙 (BimoduleCategory.of A E D P)) f) = _
  rw [composeMap_value_eval, kernelTensor_map_eval]
  unfold composeValueMap BalancedTensor.rightTensorMap BalancedTensor.rightTensorFunctor
  simp only [CategoryTheory.Functor.map_id]
  rfl

/-- 恒等kernelを先に作用させる比較は、通常bimodule右単位子と整合する。 -/
lemma kernelTensorCompositionClosedIso_rightUnit (P : Bimodule A E D)
    (M : ModuleCategory A D) :
    (kernelTensorCompositionClosedIso A D D E (Bimodule.diagonal A D) P).hom.app M ≫
      (kernelTensorMap A D E (rightBimoduleUnitIso A E D P).hom).app M =
    (kernelTensor A D E P).onClosed.map ((kernelIdentityClosedIso A D).hom.app M) := by
  let V := BimoduleCategory.evaluation A E (RightModule A D)
    (ForgetEnrichment.to (Complex A) M)
  let α := associatorIso A E D D (RightModule A D) P (Bimodule.diagonal A D)
    (DGFunctor.id (RightModule A D))
  have ht := triangle A E D (RightModule A D) P (DGFunctor.id (RightModule A D))
  have hi : α.inv ≫ composeMap A E D (RightModule A D) (rightBimoduleUnitIso A E D P).hom
      (𝟙 (BimoduleCategory.of A D (RightModule A D) (DGFunctor.id (RightModule A D)))) =
      composeMap A E D (RightModule A D) (𝟙 (BimoduleCategory.of A E D P))
        (leftBimoduleUnitIso A D (RightModule A D) (DGFunctor.id (RightModule A D))).hom := by
    rw [ht]
    exact α.inv_hom_id_assoc _
  have hv := congrArg V.map hi
  simp only [Functor.map_comp] at hv
  rw [kernelTensorCompositionClosedIso_hom_app]
  change V.map α.inv ≫ V.map
    (composeMap A E D (RightModule A D) (rightBimoduleUnitIso A E D P).hom
      (𝟙 (BimoduleCategory.of A D (RightModule A D) (DGFunctor.id (RightModule A D))))) = _
  rw [hv, kernelTensorFamilyMap]
  rfl

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceUnitClosed

/-! ## CoherenceUnitDerived（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceUnitDerived.lean） -/

/-! # 通常kernelの導来作用の右単位coherence

## 概要
恒等kernelを先に作用させる導来比較を、元のbimodule右単位子と整合させる。

## 方針
相対K-flat入力で増大を反転して通常単位図式へ帰着し、射影解像度から全入力へ拡張する。

## 規約と注意
局所Hom K-flat性や指定kernelの右相対K-flat性は不要。恒等kernelのK-flat性だけを使う。

## 使われ方
U16aの主導来kernel全体での単位coherenceへの計算入口。
-/

@[expose] public section CoherenceUnitDerived

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- 相対K-flat入力での導来作用の右単位図式。 -/
lemma kernelDerivedTensorOnBimoduleCompositionIso_rightUnit_app
    (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    (kernelDerivedTensorOnBimoduleCompositionIso A D D E (Bimodule.diagonal A D) P
        (Bimodule.diagonal_rightRelativeKFlat A D)).hom.app ((moduleToDerived A D).obj M) ≫
      (kernelResolutionDerivedTensorMap A D E (moduleCanonicalProjectiveResolution A D)
        (rightBimoduleUnitIso A E D P).hom).app ((moduleToDerived A D).obj M) =
    (kernelDerivedTensorOnBimodule A D E P).map
      ((kernelDerivedTensorOnBimoduleIdentityIso A D).hom.app ((moduleToDerived A D).obj M)) := by
  let LP := kernelDerivedTensorOnBimodule A D E P
  let aug := (kernelDerivedTensorAugmentation A D E P).app M
  have := kernelDerivedTensorAugmentation_isIso_of_relativeKFlat A D E P M hM
  apply (cancel_mono aug).1
  rw [Category.assoc]
  dsimp only [aug]
  erw [kernelDerivedTensorAugmentation_kernel_naturality A D E
    (rightBimoduleUnitIso A E D P).hom M]
  rw [← Category.assoc]
  erw [kernelDerivedTensorOnBimoduleCompositionIso_augmentation]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [← Functor.map_comp, kernelTensorCompositionClosedIso_rightUnit]
  have hn := (kernelDerivedTensorAugmentation A D E P).naturality
    ((kernelIdentityClosedIso A D).hom.app M)
  simp only [Functor.comp_map] at hn
  slice_lhs 2 3 => erw [← hn]
  slice_lhs 1 2 => rw [← Functor.map_comp, ← kernelDerivedTensorOnBimoduleIdentityIso_augmentation]
  rfl

/-- 導来作用の合成比較は、恒等kernelを先に作用させる右単位図式を満たす。 -/
lemma kernelDerivedTensorOnBimoduleCompositionIso_rightUnit :
    (kernelDerivedTensorOnBimoduleCompositionIso A D D E (Bimodule.diagonal A D) P
        (Bimodule.diagonal_rightRelativeKFlat A D)).hom ≫
      kernelResolutionDerivedTensorMap A D E (moduleCanonicalProjectiveResolution A D)
        (rightBimoduleUnitIso A E D P).hom =
    whiskerRight (kernelDerivedTensorOnBimoduleIdentityIso A D).hom
        (kernelDerivedTensorOnBimodule A D E P) ≫
      (Functor.leftUnitor (kernelDerivedTensorOnBimodule A D E P)).hom := by
  apply kernelActionNatTrans_ext_projective A D
  intro M hM
  simp only [NatTrans.comp_app, whiskerRight_app, Functor.leftUnitor_hom_app]
  erw [Category.comp_id]
  exact kernelDerivedTensorOnBimoduleCompositionIso_rightUnit_app A D E P M
    (moduleHomotopicallyProjective_relativeKFlat A D hM)

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceUnitDerived

/-! ## CoherenceUnitMain（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceUnitMain.lean） -/

/-! # 主導来kernel作用の右単位coherence

## 概要
公開された主導来kernel作用の合成・恒等比較が、U12e-localの右単位子と整合する。

## 方針
恒等kernelは右K-flatなので同じ合成モデルを使い、通常kernel計算から主局所化の任意対象へ運ぶ。

## 規約と注意
合成に必要な始域Dの局所Hom K-flat性だけを要求し、指定kernelの列の射影性は要求しない。

## 使われ方
U16aの作用coherenceとU16dのPerfへの制限。
-/

@[expose] public section CoherenceUnitMain

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 主導来右単位子の作用と、通常右単位子の作用を同じ合成モデルで比較する。 -/
lemma kernelCompositionTargetIso_rightUnit (hD : localHomKFlat A D) (P : BimoduleCategory A E D) :
    (kernelDerivedTensorFunctor A D E).map
        ((derivedBimoduleRightUnitIso A E D hD).hom.app ((bimoduleToDerived A E D).obj P)) ≫
      (kernelDerivedTensorOnBimoduleIso A D E P).hom =
    (kernelCompositionTargetIso A D D E hD (rightKFlatDiagonal A D) P).hom ≫
      kernelResolutionDerivedTensorMap A D E (moduleCanonicalProjectiveResolution A D)
        (rightBimoduleUnitIso A E D (BimoduleCategory.underlying A E D P)).hom := by
  rw [derivedBimoduleRightUnitIso_base_app, Functor.map_comp, Category.assoc]
  erw [kernelDerivedTensorOnBimoduleIso_naturality A D E
    (rightBimoduleUnitIso A E D (BimoduleCategory.underlying A E D P)).hom]
  exact (Category.assoc _ _ _).symm

/-- 恒等kernelを先に作用させる公開合成比較は、主導来右単位子と整合する。 -/
lemma kernelCompositionIso_rightUnit (hD : localHomKFlat A D) (P : Kernel A D E) :
    (kernelCompositionIso A D D E hD (kernelIdentity A D) P).hom ≫
      (kernelDerivedTensorFunctor A D E).map ((derivedBimoduleRightUnitIso A E D hD).hom.app P) =
    whiskerRight (kernelIdentityIso A D).hom (kernelDerivedTensor A D E P) ≫
      (Functor.leftUnitor (kernelDerivedTensor A D E P)).hom := by
  obtain ⟨⟨Q⟩⟩ := P
  let eQ := kernelDerivedTensorOnBimoduleIso A D E Q
  let eΔ := kernelDerivedTensorOnBimoduleIso A D D (rightKFlatDiagonal A D).obj
  apply (cancel_mono eQ.hom).1
  rw [Category.assoc]
  erw [kernelCompositionTargetIso_rightUnit A D E hD Q]
  erw [kernelCompositionIso_model A D D E hD (rightKFlatDiagonal A D) Q]
  dsimp only [kernelCompositionModelIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  slice_lhs 3 5 => rw [Iso.inv_hom_id_assoc]
  slice_lhs 2 3 => erw [kernelDerivedTensorOnBimoduleCompositionIso_rightUnit A D E
    (BimoduleCategory.underlying A E D Q)]
  apply NatTrans.ext
  funext X
  simp only [NatTrans.comp_app, NatIso.hcomp_hom, NatTrans.hcomp_app, whiskerRight_app,
    Functor.leftUnitor_hom_app]
  erw [Category.comp_id, Category.id_comp]
  change (eQ.hom.app _ ≫ (kernelDerivedTensorOnBimodule A D E
      (BimoduleCategory.underlying A E D Q)).map (eΔ.hom.app X)) ≫
      (kernelDerivedTensorOnBimodule A D E (BimoduleCategory.underlying A E D Q)).map
        ((kernelDerivedTensorOnBimoduleIdentityIso A D).hom.app X) =
    (kernelDerivedTensor A D E ((bimoduleToDerived A E D).obj Q)).map
      ((kernelIdentityIso A D).hom.app X) ≫ eQ.hom.app X
  rw [Category.assoc, ← Functor.map_comp]
  exact (eQ.hom.naturality ((kernelIdentityIso A D).hom.app X)).symm

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceUnitMain

/-! ## CoherenceAssociatorClosed（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceAssociatorClosed.lean） -/

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

@[expose] public section CoherenceAssociatorClosed

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end CoherenceAssociatorClosed

/-! ## CoherenceAssociatorAugmentation（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceAssociatorAugmentation.lean） -/

/-! # 三因子の導来作用比較と共通の増大経路

## 概要
三因子作用の結合図式の二経路を、同じ三重tensor増大を通る通常図式へ接続する。

## 方針
二因子の増大squareと入力自然性を順に適用し、三つの増大を先頭にそろえる。

## 規約と注意
最初の二kernelの右相対K-flat性を明示し、局所Hom K-flat性は要求しない。

## 使われ方
U16aの通常kernelによる導来作用の結合coherence。
-/

@[expose] public section CoherenceAssociatorAugmentation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  (G : Type t) [DGCategory A G] [Small.{u} G]
  (P : Bimodule A E D) (Q : Bimodule A F E) (R : Bimodule A G F)

/-- 三つの通常kernel作用の導来増大を順に適用した共通経路。 -/
def kernelTripleAugmentation (M : ModuleCategory A D) :
    (kernelDerivedTensorOnBimodule A F G R).obj
      ((kernelDerivedTensorOnBimodule A E F Q).obj
        ((kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M))) ⟶
    (moduleToDerived A G).obj ((kernelTensor A F G R).onClosed.obj
      ((kernelTensor A E F Q).onClosed.obj ((kernelTensor A D E P).onClosed.obj M))) :=
  (kernelDerivedTensorOnBimodule A F G R).map
      ((kernelDerivedTensorOnBimodule A E F Q).map
        ((kernelDerivedTensorAugmentation A D E P).app M)) ≫
    (kernelDerivedTensorOnBimodule A F G R).map
      ((kernelDerivedTensorAugmentation A E F Q).app ((kernelTensor A D E P).onClosed.obj M)) ≫
    (kernelDerivedTensorAugmentation A F G R).app
      ((kernelTensor A E F Q).onClosed.obj ((kernelTensor A D E P).onClosed.obj M))

/-- 前二因子を先に合成する導来経路は、共通増大と通常の同じ経路を計算する。 -/
lemma kernelAssociatorLeft_augmentation
    (hP : Bimodule.rightRelativeKFlat A E D P) (hQ : Bimodule.rightRelativeKFlat A F E Q)
    (M : ModuleCategory A D) :
    (kernelDerivedTensorOnBimodule A F G R).map
        ((kernelDerivedTensorOnBimoduleCompositionIso A D E F P Q hP).hom.app
          ((moduleToDerived A D).obj M)) ≫
      (kernelDerivedTensorOnBimoduleCompositionIso A D F G (BimoduleTensor.compose A F E D Q P) R
        (Bimodule.rightRelativeKFlat_compose A F E D Q P hQ hP)).hom.app
          ((moduleToDerived A D).obj M) ≫
      (kernelDerivedTensorAugmentation A D G
        (BimoduleTensor.compose A G F D R (BimoduleTensor.compose A F E D Q P))).app M =
    kernelTripleAugmentation A D E F G P Q R M ≫
      (moduleToDerived A G).map ((kernelTensor A F G R).onClosed.map
        ((kernelTensorCompositionClosedIso A D E F P Q).hom.app M)) ≫
      (moduleToDerived A G).map
        ((kernelTensorCompositionClosedIso A D F G
          (BimoduleTensor.compose A F E D Q P) R).hom.app M) := by
  have hn := (kernelDerivedTensorAugmentation A F G R).naturality
    ((kernelTensorCompositionClosedIso A D E F P Q).hom.app M)
  simp only [Functor.comp_map] at hn
  slice_lhs 2 3 => rw [kernelDerivedTensorOnBimoduleCompositionIso_augmentation]
  slice_lhs 1 2 => rw [← Functor.map_comp, kernelDerivedTensorOnBimoduleCompositionIso_augmentation]
  simp only [Functor.map_comp, Category.assoc]
  slice_lhs 3 4 => erw [hn]
  simp only [kernelTripleAugmentation, Category.assoc]
  rfl

/-- 後二因子を先に合成する導来経路も、同じ三重増大と通常経路を計算する。 -/
lemma kernelAssociatorRight_augmentation
    (hP : Bimodule.rightRelativeKFlat A E D P) (hQ : Bimodule.rightRelativeKFlat A F E Q)
    (M : ModuleCategory A D) :
    (kernelDerivedTensorOnBimoduleCompositionIso A E F G Q R hQ).hom.app
        ((kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M)) ≫
      (kernelDerivedTensorOnBimoduleCompositionIso A D E G P
        (BimoduleTensor.compose A G F E R Q) hP).hom.app ((moduleToDerived A D).obj M) ≫
      (kernelResolutionDerivedTensorMap A D G (moduleCanonicalProjectiveResolution A D)
        (associatorIso A G F E D R Q P).hom).app ((moduleToDerived A D).obj M) ≫
      (kernelDerivedTensorAugmentation A D G
        (BimoduleTensor.compose A G F D R (BimoduleTensor.compose A F E D Q P))).app M =
    kernelTripleAugmentation A D E F G P Q R M ≫
      (moduleToDerived A G).map ((kernelTensorCompositionClosedIso A E F G Q R).hom.app
        ((kernelTensor A D E P).onClosed.obj M)) ≫
      (moduleToDerived A G).map
        ((kernelTensorCompositionClosedIso A D E G P
          (BimoduleTensor.compose A G F E R Q)).hom.app M) ≫
      (moduleToDerived A G).map
        ((kernelTensorMap A D G (associatorIso A G F E D R Q P).hom).app M) := by
  have hn := (kernelDerivedTensorOnBimoduleCompositionIso A E F G Q R hQ).hom.naturality
    ((kernelDerivedTensorAugmentation A D E P).app M)
  simp only [Functor.comp_map] at hn
  slice_lhs 3 4 => erw [kernelDerivedTensorAugmentation_kernel_naturality A D G
    (associatorIso A G F E D R Q P).hom M]
  slice_lhs 2 3 => erw [kernelDerivedTensorOnBimoduleCompositionIso_augmentation A D E G P
    (BimoduleTensor.compose A G F E R Q) hP M]
  slice_lhs 1 2 => erw [← hn]
  slice_lhs 2 3 => erw [kernelDerivedTensorOnBimoduleCompositionIso_augmentation A E F G Q R hQ
    ((kernelTensor A D E P).onClosed.obj M)]
  simp only [kernelTripleAugmentation, Category.assoc]

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceAssociatorAugmentation

/-! ## CoherenceAssociatorKFlat（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceAssociatorKFlat.lean） -/

/-! # 右K-flat kernelモデルでの導来作用の結合coherence

## 概要
最初の二kernelを右相対K-flatとした通常代表で、全導来入力の結合図式を証明する。

## 方針
射影入力で両経路に同じ増大を合成し、通常作用の結合図式へ帰着してから増大を消去する。

## 規約と注意
局所Hom K-flat性は不要。最後のkernelにはK-flat性を要求しない。

## 使われ方
U16aの主導来kernel全体の結合coherenceの計算モデル。
-/

@[expose] public section CoherenceAssociatorKFlat

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  (G : Type t) [DGCategory A G] [Small.{u} G]
  (P : Bimodule A E D) (Q : Bimodule A F E) (R : Bimodule A G F)
  (hP : Bimodule.rightRelativeKFlat A E D P) (hQ : Bimodule.rightRelativeKFlat A F E Q)

/-- 相対K-flat入力での三因子導来作用の結合図式。 -/
lemma kernelDerivedTensorOnBimoduleCompositionIso_associator_app
    (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    (kernelDerivedTensorOnBimodule A F G R).map
        ((kernelDerivedTensorOnBimoduleCompositionIso A D E F P Q hP).hom.app
          ((moduleToDerived A D).obj M)) ≫
      (kernelDerivedTensorOnBimoduleCompositionIso A D F G
        (BimoduleTensor.compose A F E D Q P) R
        (Bimodule.rightRelativeKFlat_compose A F E D Q P hQ hP)).hom.app
          ((moduleToDerived A D).obj M) =
    (kernelDerivedTensorOnBimoduleCompositionIso A E F G Q R hQ).hom.app
        ((kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M)) ≫
      (kernelDerivedTensorOnBimoduleCompositionIso A D E G P
        (BimoduleTensor.compose A G F E R Q) hP).hom.app ((moduleToDerived A D).obj M) ≫
      (kernelResolutionDerivedTensorMap A D G (moduleCanonicalProjectiveResolution A D)
        (associatorIso A G F E D R Q P).hom).app ((moduleToDerived A D).obj M) := by
  let C := BimoduleTensor.compose A G F D R (BimoduleTensor.compose A F E D Q P)
  have := kernelDerivedTensorAugmentation_isIso_of_relativeKFlat A D G C M hM
  apply (cancel_mono ((kernelDerivedTensorAugmentation A D G C).app M)).1
  simp only [Category.assoc]
  rw [kernelAssociatorLeft_augmentation A D E F G P Q R hP hQ M,
    kernelAssociatorRight_augmentation A D E F G P Q R hP hQ M]
  have hc := congrArg (moduleToDerived A G).map
    (kernelTensorCompositionClosedIso_associator A D E F G P Q R M)
  simp only [Functor.map_comp] at hc
  simpa only [Category.assoc] using congrArg
    (fun k => kernelTripleAugmentation A D E F G P Q R M ≫ k) hc

/-- 指定した右K-flat二因子の導来作用の合成比較は、元の結合子と整合する。 -/
lemma kernelDerivedTensorOnBimoduleCompositionIso_associator :
    whiskerRight (kernelDerivedTensorOnBimoduleCompositionIso A D E F P Q hP).hom
        (kernelDerivedTensorOnBimodule A F G R) ≫
      (kernelDerivedTensorOnBimoduleCompositionIso A D F G
        (BimoduleTensor.compose A F E D Q P) R
        (Bimodule.rightRelativeKFlat_compose A F E D Q P hQ hP)).hom =
    (Functor.associator (kernelDerivedTensorOnBimodule A D E P)
      (kernelDerivedTensorOnBimodule A E F Q) (kernelDerivedTensorOnBimodule A F G R)).hom ≫
      whiskerLeft (kernelDerivedTensorOnBimodule A D E P)
        (kernelDerivedTensorOnBimoduleCompositionIso A E F G Q R hQ).hom ≫
      (kernelDerivedTensorOnBimoduleCompositionIso A D E G P
        (BimoduleTensor.compose A G F E R Q) hP).hom ≫
      kernelResolutionDerivedTensorMap A D G (moduleCanonicalProjectiveResolution A D)
        (associatorIso A G F E D R Q P).hom := by
  apply kernelActionNatTrans_ext_projective A D
  intro M hM
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app]
  erw [Category.id_comp]
  exact kernelDerivedTensorOnBimoduleCompositionIso_associator_app A D E F G P Q R hP hQ M
    (moduleHomotopicallyProjective_relativeKFlat A D hM)

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceAssociatorKFlat

/-! ## CoherenceAssociatorModels（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceAssociatorModels.lean） -/

/-! # 主導来kernel結合子と二つの右K-flat計算モデル

## 概要
公開主導来合成の結合子と、二つの通常三因子モデルを同じ計算同型で結ぶ。

## 方針
既存の全導来結合子のK-flat計算squareを評価し、kernelの向きへ読み替える。

## 規約と注意
合成の始域Dと次の圏Eの局所Hom K-flat性を明示。最後のkernelは任意。

## 使われ方
U16aの主導来kernel全体での作用結合coherenceへの移送。
-/

@[expose] public section CoherenceAssociatorModels

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  (G : Type t) [DGCategory A G] [Small.{u} G]

/-- kernelの作用順に読んだ、既存U12e-localの主導来結合子。 -/
def kernelAssociatorIso (hD : localHomKFlat A D) (hE : localHomKFlat A E)
    (P : Kernel A D E) (Q : Kernel A E F) (R : Kernel A F G) :
    kernelCompose A D E G hD P (kernelCompose A E F G hE Q R) ≅
      kernelCompose A D F G hD (kernelCompose A D E F hD P Q) R :=
  (derivedBimoduleAssociator A G F E D hE hD Q P).app R

variable (hD : localHomKFlat A D) (hE : localHomKFlat A E)
  (P : RightKFlatBimoduleCategory A E D) (Q : RightKFlatBimoduleCategory A F E)
  (R : BimoduleCategory A G F)

/-- 後二作用の合成を先に計算する三因子kernelの通常モデル。 -/
def kernelAssociatorPairModelIso :
    kernelCompose A D E G hD ((bimoduleToDerived A E D).obj P.obj)
      (kernelCompose A E F G hE ((bimoduleToDerived A F E).obj Q.obj)
        ((bimoduleToDerived A G F).obj R)) ≅
    (bimoduleToDerived A G D).obj (BimoduleCategory.of A G D
      (BimoduleTensor.compose A G E D
        (BimoduleTensor.compose A G F E (BimoduleCategory.underlying A G F R)
          (BimoduleCategory.underlying A F E Q.obj)) (BimoduleCategory.underlying A E D P.obj))) :=
  ((derivedBimoduleComposeFunctor A G E D hD).obj
      ((bimoduleToDerived A E D).obj P.obj)).mapIso
        (derivedBimoduleComposeKFlatValueIso A G F E hE Q R) ≪≫
    derivedBimoduleComposeKFlatValueIso A G E D hD P (BimoduleCategory.of A G E
      (BimoduleTensor.compose A G F E (BimoduleCategory.underlying A G F R)
        (BimoduleCategory.underlying A F E Q.obj)))

/-- 前二作用のkernelを先に計算する三因子kernelの通常モデル。 -/
def kernelAssociatorNestedModelIso :
    kernelCompose A D F G hD
      (kernelCompose A D E F hD ((bimoduleToDerived A E D).obj P.obj)
        ((bimoduleToDerived A F E).obj Q.obj)) ((bimoduleToDerived A G F).obj R) ≅
    (bimoduleToDerived A G D).obj (BimoduleCategory.of A G D
      (BimoduleTensor.compose A G F D (BimoduleCategory.underlying A G F R)
        (BimoduleTensor.compose A F E D (BimoduleCategory.underlying A F E Q.obj)
          (BimoduleCategory.underlying A E D P.obj)))) :=
  ((derivedBimoduleComposeFunctor A G F D hD).mapIso
    (derivedBimoduleComposeKFlatValueIso A F E D hD P Q.obj)).app
      ((bimoduleToDerived A G F).obj R) ≪≫
    derivedBimoduleComposeKFlatValueIso A G F D hD (rightKFlatCompose A F E D Q P) R

/-- 主導来kernel結合子の二モデル計算は、同じ通常結合子の局所化像と整合する。 -/
lemma kernelAssociatorIso_model_fac :
    (kernelAssociatorIso A D E F G hD hE
        ((bimoduleToDerived A E D).obj P.obj) ((bimoduleToDerived A F E).obj Q.obj)
        ((bimoduleToDerived A G F).obj R)).hom ≫
      (kernelAssociatorNestedModelIso A D E F G hD P Q R).hom =
    (kernelAssociatorPairModelIso A D E F G hD hE P Q R).hom ≫
      (bimoduleToDerived A G D).map (associatorIso A G F E D
        (BimoduleCategory.underlying A G F R) (BimoduleCategory.underlying A F E Q.obj)
        (BimoduleCategory.underlying A E D P.obj)).hom := by
  have h := NatTrans.congr_app
    (derivedBimoduleAssociatorIso_kFlat_fac A G F E D hE hD Q P)
      ((bimoduleToDerived A G F).obj R)
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at h
  rw [rightKFlatDerivedAssociator_base_app] at h
  exact h

/-- 主導来結合子の作用も、同じ通常結合子の作用のモデルsquareを満たす。 -/
lemma kernelAssociatorIso_action_model_fac :
    (kernelDerivedTensorFunctor A D G).map
        (kernelAssociatorIso A D E F G hD hE
          ((bimoduleToDerived A E D).obj P.obj) ((bimoduleToDerived A F E).obj Q.obj)
          ((bimoduleToDerived A G F).obj R)).hom ≫
      (kernelDerivedTensorFunctor A D G).map
        (kernelAssociatorNestedModelIso A D E F G hD P Q R).hom =
    (kernelDerivedTensorFunctor A D G).map
        (kernelAssociatorPairModelIso A D E F G hD hE P Q R).hom ≫
      kernelResolutionDerivedTensorMap A D G (moduleCanonicalProjectiveResolution A D)
        (associatorIso A G F E D (BimoduleCategory.underlying A G F R)
          (BimoduleCategory.underlying A F E Q.obj)
          (BimoduleCategory.underlying A E D P.obj)).hom := by
  rw [← Functor.map_comp, kernelAssociatorIso_model_fac, Functor.map_comp,
    kernelDerivedTensorFunctor_map_base]

/-- 右K-flat代表上の公開合成比較は、通常kernel作用の同じ比較を計算する。 -/
lemma kernelCompositionIso_kFlat_fac (P' : RightKFlatBimoduleCategory A E D)
    (Q' : BimoduleCategory A F E) :
    (kernelCompositionIso A D E F hD ((bimoduleToDerived A E D).obj P'.obj)
        ((bimoduleToDerived A F E).obj Q')).hom ≫
      (kernelDerivedTensorFunctor A D F).map
        (derivedBimoduleComposeKFlatValueIso A F E D hD P' Q').hom =
    (kernelDerivedTensorOnBimoduleCompositionIso A D E F
      (BimoduleCategory.underlying A E D P'.obj) (BimoduleCategory.underlying A F E Q')
      P'.property).hom := by
  rw [kernelCompositionIso_model]
  apply NatTrans.ext
  funext X
  simp only [kernelCompositionModelIso, kernelCompositionTargetIso, Iso.trans_hom,
    Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app, Functor.mapIso_inv,
    kernelDerivedTensorOnBimoduleIso_refl, Iso.refl_hom, Iso.refl_inv,
    NatIso.hcomp_hom, NatTrans.hcomp_app, NatTrans.id_app]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.id_comp]
  rw [Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, Iso.inv_hom_id]
  erw [CategoryTheory.Functor.map_id]
  rw [NatTrans.id_app]
  erw [Category.comp_id]

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceAssociatorModels

/-! ## CoherenceAssociatorPaths（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceAssociatorPaths.lean） -/

/-! # 公開kernel作用結合図式の二経路とモデル計算

## 概要
三因子の公開作用の結合図式を二経路として固定し、同じK-flatモデルへ接続する。

## 方針
公開比較の片側自然性でK-flat計算射を末尾へ移し、通常作用比較の計算式を適用する。

## 規約と注意
経路の定義は全主導来kernelで行う。モデル計算の最初の二代表のK-flat性は明示する。

## 使われ方
U16aの全主導来kernel上の結合coherenceを、同じ二経路の自然性で証明する。
-/

@[expose] public section CoherenceAssociatorPaths

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  (G : Type t) [DGCategory A G] [Small.{u} G]

/-- 前二作用を先に合成する公開結合図式の経路。 -/
def kernelAssociatorLeftPath (hD : localHomKFlat A D)
    (P : Kernel A D E) (Q : Kernel A E F) (R : Kernel A F G) :
    (kernelDerivedTensor A D E P ⋙ kernelDerivedTensor A E F Q) ⋙ kernelDerivedTensor A F G R ⟶
      kernelDerivedTensor A D G
        (kernelCompose A D F G hD (kernelCompose A D E F hD P Q) R) :=
  whiskerRight (kernelCompositionIso A D E F hD P Q).hom (kernelDerivedTensor A F G R) ≫
    (kernelCompositionIso A D F G hD (kernelCompose A D E F hD P Q) R).hom

/-- 後二作用を先に合成し、主導来kernel結合子で同じ標的へ進む公開経路。 -/
def kernelAssociatorRightPath (hD : localHomKFlat A D) (hE : localHomKFlat A E)
    (P : Kernel A D E) (Q : Kernel A E F) (R : Kernel A F G) :
    (kernelDerivedTensor A D E P ⋙ kernelDerivedTensor A E F Q) ⋙ kernelDerivedTensor A F G R ⟶
      kernelDerivedTensor A D G
        (kernelCompose A D F G hD (kernelCompose A D E F hD P Q) R) :=
  (Functor.associator (kernelDerivedTensor A D E P) (kernelDerivedTensor A E F Q)
      (kernelDerivedTensor A F G R)).hom ≫
    whiskerLeft (kernelDerivedTensor A D E P) (kernelCompositionIso A E F G hE Q R).hom ≫
    (kernelCompositionIso A D E G hD P (kernelCompose A E F G hE Q R)).hom ≫
    (kernelDerivedTensorFunctor A D G).map (kernelAssociatorIso A D E F G hD hE P Q R).hom

variable (hD : localHomKFlat A D) (hE : localHomKFlat A E)
  (P : RightKFlatBimoduleCategory A E D) (Q : RightKFlatBimoduleCategory A F E)
  (R : BimoduleCategory A G F)
local notation "pK" => CategoryTheory.Functor.obj (bimoduleToDerived A E D) P.obj
local notation "qK" => CategoryTheory.Functor.obj (bimoduleToDerived A F E) Q.obj
local notation "rK" => CategoryTheory.Functor.obj (bimoduleToDerived A G F) R
local notation "P₀" => BimoduleCategory.underlying A E D P.obj
local notation "Q₀" => BimoduleCategory.underlying A F E Q.obj
local notation "R₀" => BimoduleCategory.underlying A G F R

/-- 公開左経路は、同じ三因子モデルの左経路を計算する。 -/
lemma kernelAssociatorLeftPath_model_fac :
    kernelAssociatorLeftPath A D E F G hD pK qK rK ≫
      (kernelDerivedTensorFunctor A D G).map
        (kernelAssociatorNestedModelIso A D E F G hD P Q R).hom =
    whiskerRight (kernelDerivedTensorOnBimoduleCompositionIso A D E F P₀ Q₀ P.property).hom
        (kernelDerivedTensorOnBimodule A F G R₀) ≫
      (kernelDerivedTensorOnBimoduleCompositionIso A D F G
        (BimoduleTensor.compose A F E D Q₀ P₀) R₀
        (Bimodule.rightRelativeKFlat_compose A F E D Q₀ P₀ Q.property P.property)).hom := by
  dsimp only [kernelAssociatorLeftPath, kernelAssociatorNestedModelIso,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← kernelCompositionIso_first_naturality]
  slice_lhs 3 4 => erw [kernelCompositionIso_kFlat_fac A D F G hD
    (rightKFlatCompose A F E D Q P) R]
  slice_lhs 1 2 => rw [← whiskerRight_comp, kernelCompositionIso_kFlat_fac A D E F hD P Q.obj]
  rfl

/-- 公開右経路のkernel結合子より前の部分は、同じ通常モデルの右経路を計算する。 -/
lemma kernelAssociatorPairPath_model_fac :
    whiskerLeft (kernelDerivedTensor A D E pK) (kernelCompositionIso A E F G hE qK rK).hom ≫
      (kernelCompositionIso A D E G hD pK (kernelCompose A E F G hE qK rK)).hom ≫
      (kernelDerivedTensorFunctor A D G).map
        (kernelAssociatorPairModelIso A D E F G hD hE P Q R).hom =
    whiskerLeft (kernelDerivedTensorOnBimodule A D E P₀)
        (kernelDerivedTensorOnBimoduleCompositionIso A E F G Q₀ R₀ Q.property).hom ≫
      (kernelDerivedTensorOnBimoduleCompositionIso A D E G P₀
        (BimoduleTensor.compose A G F E R₀ Q₀) P.property).hom := by
  dsimp only [kernelAssociatorPairModelIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Functor.map_comp]
  slice_lhs 2 3 => rw [← kernelCompositionIso_second_naturality]
  slice_lhs 3 4 => rw [kernelCompositionIso_kFlat_fac A D E G hD P
    (BimoduleCategory.of A G E (BimoduleTensor.compose A G F E R₀ Q₀))]
  slice_lhs 1 2 => rw [← whiskerLeft_comp, kernelCompositionIso_kFlat_fac A E F G hE Q R]
  rfl

/-- 公開右経路全体は、同じ通常モデルの右経路と元の結合子の作用を計算する。 -/
lemma kernelAssociatorRightPath_model_fac :
    kernelAssociatorRightPath A D E F G hD hE pK qK rK ≫
      (kernelDerivedTensorFunctor A D G).map
        (kernelAssociatorNestedModelIso A D E F G hD P Q R).hom =
    (Functor.associator (kernelDerivedTensorOnBimodule A D E P₀)
      (kernelDerivedTensorOnBimodule A E F Q₀) (kernelDerivedTensorOnBimodule A F G R₀)).hom ≫
      whiskerLeft (kernelDerivedTensorOnBimodule A D E P₀)
        (kernelDerivedTensorOnBimoduleCompositionIso A E F G Q₀ R₀ Q.property).hom ≫
      (kernelDerivedTensorOnBimoduleCompositionIso A D E G P₀
        (BimoduleTensor.compose A G F E R₀ Q₀) P.property).hom ≫
      kernelResolutionDerivedTensorMap A D G (moduleCanonicalProjectiveResolution A D)
        (associatorIso A G F E D R₀ Q₀ P₀).hom := by
  dsimp only [kernelAssociatorRightPath]
  simp only [Category.assoc]
  slice_lhs 4 5 => rw [kernelAssociatorIso_action_model_fac]
  slice_lhs 2 4 => rw [kernelAssociatorPairPath_model_fac]
  simp only [Category.assoc]
  rfl

/-- 指定右K-flat二因子の通常代表で、公開主導来作用の結合図式の二経路は一致する。 -/
lemma kernelCompositionIso_associator_model :
    kernelAssociatorLeftPath A D E F G hD pK qK rK =
      kernelAssociatorRightPath A D E F G hD hE pK qK rK := by
  apply (cancel_mono ((kernelDerivedTensorFunctor A D G).map
    (kernelAssociatorNestedModelIso A D E F G hD P Q R).hom)).1
  rw [kernelAssociatorLeftPath_model_fac, kernelAssociatorRightPath_model_fac]
  exact kernelDerivedTensorOnBimoduleCompositionIso_associator A D E F G
    P₀ Q₀ R₀ P.property Q.property

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceAssociatorPaths

/-! ## CoherenceAssociatorNaturality（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceAssociatorNaturality.lean） -/

/-! # kernel結合子と公開左経路の全導来射自然性

## 概要
最初の二kernelの射について、主導来kernel結合子と公開左経路の自然性を証明する。

## 方針
既存のcurried結合自然同型を評価し、合成比較の片側自然性を順に適用する。

## 規約と注意
射は主導来kernel圏の任意射。代表のK-flat性を仮定しない。

## 使われ方
U16aの結合coherenceをK-flat代表の同型に沿って任意kernelへ移す。
-/

@[expose] public section CoherenceAssociatorNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  (G : Type t) [DGCategory A G] [Small.{u} G]
  (hD : localHomKFlat A D) (hE : localHomKFlat A E)

/-- 最初のkernelの任意導来射に関する主導来kernel結合子の自然性。 -/
lemma kernelAssociatorIso_first_naturality {P P' : Kernel A D E} (f : P ⟶ P')
    (Q : Kernel A E F) (R : Kernel A F G) :
    (((derivedBimoduleComposeFunctor A G E D hD).map f).app
        (kernelCompose A E F G hE Q R)) ≫
      (kernelAssociatorIso A D E F G hD hE P' Q R).hom =
    (kernelAssociatorIso A D E F G hD hE P Q R).hom ≫
      (((derivedBimoduleComposeFunctor A G F D hD).map
        (((derivedBimoduleComposeFunctor A F E D hD).map f).app Q)).app R) := by
  have h := NatTrans.congr_app (NatTrans.congr_app
    ((derivedBimoduleAssociatorIso A G F E D hE hD).hom.naturality f) Q) R
  exact h

/-- 二番目のkernelの任意導来射に関する主導来kernel結合子の自然性。 -/
lemma kernelAssociatorIso_second_naturality (P : Kernel A D E)
    {Q Q' : Kernel A E F} (g : Q ⟶ Q') (R : Kernel A F G) :
    ((derivedBimoduleComposeFunctor A G E D hD).obj P).map
        (((derivedBimoduleComposeFunctor A G F E hE).map g).app R) ≫
      (kernelAssociatorIso A D E F G hD hE P Q' R).hom =
    (kernelAssociatorIso A D E F G hD hE P Q R).hom ≫
      (((derivedBimoduleComposeFunctor A G F D hD).map
        (((derivedBimoduleComposeFunctor A F E D hD).obj P).map g)).app R) := by
  have h := NatTrans.congr_app
    (((derivedBimoduleAssociatorIso A G F E D hE hD).hom.app P).naturality g) R
  exact h

/-- 最初のkernelの射について公開左経路は自然。 -/
lemma kernelAssociatorLeftPath_first_naturality {P P' : Kernel A D E} (f : P ⟶ P')
    (Q : Kernel A E F) (R : Kernel A F G) :
    whiskerRight (whiskerRight ((kernelDerivedTensorFunctor A D E).map f)
        (kernelDerivedTensor A E F Q)) (kernelDerivedTensor A F G R) ≫
      kernelAssociatorLeftPath A D E F G hD P' Q R =
    kernelAssociatorLeftPath A D E F G hD P Q R ≫
      (kernelDerivedTensorFunctor A D G).map
        (((derivedBimoduleComposeFunctor A G F D hD).map
          (((derivedBimoduleComposeFunctor A F E D hD).map f).app Q)).app R) := by
  dsimp only [kernelAssociatorLeftPath]
  slice_lhs 1 2 => rw [← whiskerRight_comp, kernelCompositionIso_first_naturality]
  rw [whiskerRight_comp]
  simp only [Category.assoc]
  slice_lhs 2 3 => erw [kernelCompositionIso_first_naturality A D F G hD
    (((derivedBimoduleComposeFunctor A F E D hD).map f).app Q) R]
  rfl

/-- 二番目のkernelの射について公開左経路は自然。 -/
lemma kernelAssociatorLeftPath_second_naturality (P : Kernel A D E)
    {Q Q' : Kernel A E F} (g : Q ⟶ Q') (R : Kernel A F G) :
    whiskerRight (whiskerLeft (kernelDerivedTensor A D E P)
        ((kernelDerivedTensorFunctor A E F).map g)) (kernelDerivedTensor A F G R) ≫
      kernelAssociatorLeftPath A D E F G hD P Q' R =
    kernelAssociatorLeftPath A D E F G hD P Q R ≫
      (kernelDerivedTensorFunctor A D G).map
        (((derivedBimoduleComposeFunctor A G F D hD).map
          (((derivedBimoduleComposeFunctor A F E D hD).obj P).map g)).app R) := by
  dsimp only [kernelAssociatorLeftPath]
  slice_lhs 1 2 => rw [← whiskerRight_comp, kernelCompositionIso_second_naturality]
  rw [whiskerRight_comp]
  simp only [Category.assoc]
  slice_lhs 2 3 => erw [kernelCompositionIso_first_naturality A D F G hD
    (((derivedBimoduleComposeFunctor A F E D hD).obj P).map g) R]
  rfl

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceAssociatorNaturality

/-! ## CoherenceAssociatorRightNaturality（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceAssociatorRightNaturality.lean） -/

/-! # 公開結合図式の右経路の全導来射自然性

## 概要
公開右経路が最初の二kernelの全導来射に自然であることを証明する。

## 方針
関手結合子の成分を計算し、後二作用の比較・前作用の比較・kernel結合子の三squareを貼る。

## 規約と注意
代表のK-flat性や同型性を要求せず、任意の導来射で成立する。

## 使われ方
U16aの結合二経路の等式を指定K-flat代表から任意kernelへ移送する。
-/

@[expose] public section CoherenceAssociatorRightNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  (G : Type t) [DGCategory A G] [Small.{u} G]
  (hD : localHomKFlat A D) (hE : localHomKFlat A E)

/-- 最初のkernelの全導来射に関する公開右経路の自然性。 -/
lemma kernelAssociatorRightPath_first_naturality {P P' : Kernel A D E} (f : P ⟶ P')
    (Q : Kernel A E F) (R : Kernel A F G) :
    whiskerRight (whiskerRight ((kernelDerivedTensorFunctor A D E).map f)
        (kernelDerivedTensor A E F Q)) (kernelDerivedTensor A F G R) ≫
      kernelAssociatorRightPath A D E F G hD hE P' Q R =
    kernelAssociatorRightPath A D E F G hD hE P Q R ≫
      (kernelDerivedTensorFunctor A D G).map
        (((derivedBimoduleComposeFunctor A G F D hD).map
          (((derivedBimoduleComposeFunctor A F E D hD).map f).app Q)).app R) := by
  apply NatTrans.ext
  funext X
  have hc := (kernelCompositionIso A E F G hE Q R).hom.naturality
    (((kernelDerivedTensorFunctor A D E).map f).app X)
  simp only [Functor.comp_map] at hc
  have hp := NatTrans.congr_app (kernelCompositionIso_first_naturality A D E G hD f
    (kernelCompose A E F G hE Q R)) X
  simp only [NatTrans.comp_app, whiskerRight_app] at hp
  have ha := congrArg (kernelDerivedTensorFunctor A D G).map
    (kernelAssociatorIso_first_naturality A D E F G hD hE f Q R)
  simp only [Functor.map_comp] at ha
  have hax := NatTrans.congr_app ha X
  simp only [NatTrans.comp_app] at hax
  dsimp only [kernelAssociatorRightPath]
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app, Category.assoc]
  erw [Category.id_comp, Category.id_comp]
  slice_lhs 1 2 => erw [hc]
  slice_lhs 2 3 => erw [hp]
  slice_lhs 3 4 => erw [hax]
  rfl

/-- 二番目のkernelの全導来射に関する公開右経路の自然性。 -/
lemma kernelAssociatorRightPath_second_naturality (P : Kernel A D E)
    {Q Q' : Kernel A E F} (g : Q ⟶ Q') (R : Kernel A F G) :
    whiskerRight (whiskerLeft (kernelDerivedTensor A D E P)
        ((kernelDerivedTensorFunctor A E F).map g)) (kernelDerivedTensor A F G R) ≫
      kernelAssociatorRightPath A D E F G hD hE P Q' R =
    kernelAssociatorRightPath A D E F G hD hE P Q R ≫
      (kernelDerivedTensorFunctor A D G).map
        (((derivedBimoduleComposeFunctor A G F D hD).map
          (((derivedBimoduleComposeFunctor A F E D hD).obj P).map g)).app R) := by
  apply NatTrans.ext
  funext X
  have hc := NatTrans.congr_app (kernelCompositionIso_first_naturality A E F G hE g R)
    ((kernelDerivedTensor A D E P).obj X)
  simp only [NatTrans.comp_app, whiskerRight_app] at hc
  have hp := NatTrans.congr_app (kernelCompositionIso_second_naturality A D E G hD P
    (((derivedBimoduleComposeFunctor A G F E hE).map g).app R)) X
  simp only [NatTrans.comp_app, whiskerLeft_app] at hp
  have ha := congrArg (kernelDerivedTensorFunctor A D G).map
    (kernelAssociatorIso_second_naturality A D E F G hD hE P g R)
  simp only [Functor.map_comp] at ha
  have hax := NatTrans.congr_app ha X
  simp only [NatTrans.comp_app] at hax
  dsimp only [kernelAssociatorRightPath]
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app, Category.assoc]
  erw [Category.id_comp, Category.id_comp]
  slice_lhs 1 2 => erw [hc]
  slice_lhs 2 3 => erw [hp]
  slice_lhs 3 4 => erw [hax]
  rfl

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceAssociatorRightNaturality

/-! ## CoherenceAssociatorMain（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceAssociatorMain.lean） -/

/-! # 任意の主導来kernel作用の結合coherence

## 概要
公開作用合成比較と主導来kernel結合子の二経路を任意kernelで同定する。

## 方針
最初の二kernelを右相対K-flat代表で計算し、両経路の自然性により代表同型を消去する。

## 規約と注意
局所Hom条件はD・Eのみ。最後のkernelにK-flat性や列の射影性を追加しない。

## 使われ方
U16a受入と、U16dの実際のPerf制限への結合coherenceの移送。
-/

@[expose] public section CoherenceAssociatorMain

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  (G : Type t) [DGCategory A G] [Small.{u} G]
  (hD : localHomKFlat A D) (hE : localHomKFlat A E)

/-- 最初のkernelの同型に沿って、公開結合二経路の一致を運ぶ。 -/
lemma kernelAssociatorPaths_eq_of_first_iso {P P' : Kernel A D E} (e : P ≅ P')
    (Q : Kernel A E F) (R : Kernel A F G)
    (h : kernelAssociatorLeftPath A D E F G hD P Q R =
      kernelAssociatorRightPath A D E F G hD hE P Q R) :
    kernelAssociatorLeftPath A D E F G hD P' Q R =
      kernelAssociatorRightPath A D E F G hD hE P' Q R := by
  let s := Functor.isoWhiskerRight
    (Functor.isoWhiskerRight ((kernelDerivedTensorFunctor A D E).mapIso e)
      (kernelDerivedTensor A E F Q)) (kernelDerivedTensor A F G R)
  apply (cancel_epi s.hom).1
  change whiskerRight (whiskerRight ((kernelDerivedTensorFunctor A D E).map e.hom)
      (kernelDerivedTensor A E F Q)) (kernelDerivedTensor A F G R) ≫ _ =
    whiskerRight (whiskerRight ((kernelDerivedTensorFunctor A D E).map e.hom)
      (kernelDerivedTensor A E F Q)) (kernelDerivedTensor A F G R) ≫ _
  exact (kernelAssociatorLeftPath_first_naturality A D E F G hD e.hom Q R).trans
    ((congrArg (fun k => k ≫ _) h).trans
      (kernelAssociatorRightPath_first_naturality A D E F G hD hE e.hom Q R).symm)

/-- 二番目のkernelの同型に沿って、公開結合二経路の一致を運ぶ。 -/
lemma kernelAssociatorPaths_eq_of_second_iso (P : Kernel A D E)
    {Q Q' : Kernel A E F} (e : Q ≅ Q') (R : Kernel A F G)
    (h : kernelAssociatorLeftPath A D E F G hD P Q R =
      kernelAssociatorRightPath A D E F G hD hE P Q R) :
    kernelAssociatorLeftPath A D E F G hD P Q' R =
      kernelAssociatorRightPath A D E F G hD hE P Q' R := by
  let s := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (kernelDerivedTensor A D E P)
      ((kernelDerivedTensorFunctor A E F).mapIso e)) (kernelDerivedTensor A F G R)
  apply (cancel_epi s.hom).1
  change whiskerRight (whiskerLeft (kernelDerivedTensor A D E P)
      ((kernelDerivedTensorFunctor A E F).map e.hom)) (kernelDerivedTensor A F G R) ≫ _ =
    whiskerRight (whiskerLeft (kernelDerivedTensor A D E P)
      ((kernelDerivedTensorFunctor A E F).map e.hom)) (kernelDerivedTensor A F G R) ≫ _
  exact (kernelAssociatorLeftPath_second_naturality A D E F G hD P e.hom R).trans
    ((congrArg (fun k => k ≫ _) h).trans
      (kernelAssociatorRightPath_second_naturality A D E F G hD hE P e.hom R).symm)

/-- 任意の主導来kernelで、実際の作用の結合図式の二経路は一致する。 -/
theorem kernelCompositionIso_associator (P : Kernel A D E)
    (Q : Kernel A E F) (R : Kernel A F G) :
    kernelAssociatorLeftPath A D E F G hD P Q R =
      kernelAssociatorRightPath A D E F G hD hE P Q R := by
  obtain ⟨P₀, ⟨eP⟩⟩ := exists_rightKFlat_derived_iso A E D hD P
  obtain ⟨Q₀, ⟨eQ⟩⟩ := exists_rightKFlat_derived_iso A F E hE Q
  obtain ⟨⟨R₀⟩⟩ := R
  apply kernelAssociatorPaths_eq_of_second_iso A D E F G hD hE P eQ
  apply kernelAssociatorPaths_eq_of_first_iso A D E F G hD hE eP
  exact kernelCompositionIso_associator_model A D E F G hD hE P₀ Q₀ R₀

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceAssociatorMain

/-! ## CoherenceLeftUnitMain（旧 SerrePositivity/DifferentialGraded/Morita/CoherenceLeftUnitMain.lean） -/

/-! # 主導来kernel作用の左単位coherence

## 概要
恒等kernelを後に作用させる公開合成比較と主導来左単位子の整合性を証明する。

## 方針
kernel三角図式と作用結合図式を恒等kernel二個に適用し、既存右単位図式へ帰着する。
恒等kernelの作用は恒等関手に同型なので、その後合成を打ち消せる。

## 規約と注意
局所Hom条件はD・Eに明示する。一般の分解変更coherenceは使用しない。

## 使われ方
U16aの両単位・結合整合性の最後の入口。
-/

@[expose] public section CoherenceLeftUnitMain

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (hD : localHomKFlat A D) (hE : localHomKFlat A E)

/-- 恒等kernel二個を含む主導来三角図式。 -/
lemma kernelAssociatorIso_identity_triangle (P : Kernel A D E) :
    (kernelAssociatorIso A D E E E hD hE P (kernelIdentity A E) (kernelIdentity A E)).hom ≫
      (((derivedBimoduleComposeFunctor A E E D hD).map
        ((derivedBimoduleLeftUnitIso A E D hD).hom.app P)).app (kernelIdentity A E)) =
    ((derivedBimoduleComposeFunctor A E E D hD).obj P).map
      ((derivedBimoduleRightUnitIso A E E hE).hom.app (kernelIdentity A E)) := by
  exact NatTrans.congr_app (derivedBimoduleTriangle_app A E E D hE hD P) (kernelIdentity A E)

include hE in
/-- 後に恒等kernelを作用させる公開合成比較は、主導来左単位子と整合する。 -/
theorem kernelCompositionIso_leftUnit (P : Kernel A D E) :
    (kernelCompositionIso A D E E hD P (kernelIdentity A E)).hom ≫
      (kernelDerivedTensorFunctor A D E).map ((derivedBimoduleLeftUnitIso A E D hD).hom.app P) =
    whiskerLeft (kernelDerivedTensor A D E P) (kernelIdentityIso A E).hom ≫
      (Functor.rightUnitor (kernelDerivedTensor A D E P)).hom := by
  let I := kernelIdentity A E
  let T := kernelDerivedTensor A E E I
  let c := kernelCompositionIso A D E E hD P I
  let l := (derivedBimoduleLeftUnitIso A E D hD).hom.app P
  let j := (kernelDerivedTensorFunctor A D E).map l
  let r := (derivedBimoduleRightUnitIso A E E hE).hom.app I
  let kl := ((derivedBimoduleComposeFunctor A E E D hD).map l).app I
  let kr := ((derivedBimoduleComposeFunctor A E E D hD).obj P).map r
  have ht : (kernelAssociatorIso A D E E E hD hE P I I).hom ≫ kl = kr :=
    kernelAssociatorIso_identity_triangle A D E hD hE P
  have hta : (kernelDerivedTensorFunctor A D E).map
      (kernelAssociatorIso A D E E E hD hE P I I).hom ≫
      (kernelDerivedTensorFunctor A D E).map kl =
      (kernelDerivedTensorFunctor A D E).map kr := by
    rw [← Functor.map_comp, ht]
  have hf := kernelCompositionIso_first_naturality A D E E hD l I
  have hs := kernelCompositionIso_second_naturality A D E E hD P r
  have hr := kernelCompositionIso_rightUnit A E E hE I
  have ha := kernelCompositionIso_associator A D E E E hD hE P I I
  have heq : whiskerRight (c.hom ≫ j) T ≫ c.hom =
      (Functor.associator (kernelDerivedTensor A D E P) T T).hom ≫
        whiskerLeft (kernelDerivedTensor A D E P)
          (whiskerRight (kernelIdentityIso A E).hom T ≫ (Functor.leftUnitor T).hom) ≫ c.hom := by
    calc
      _ = kernelAssociatorLeftPath A D E E E hD P I I ≫
          (kernelDerivedTensorFunctor A D E).map kl := by
        rw [whiskerRight_comp, Category.assoc]
        erw [hf]
        simp only [kernelAssociatorLeftPath, Category.assoc]
        rfl
      _ = kernelAssociatorRightPath A D E E E hD hE P I I ≫
          (kernelDerivedTensorFunctor A D E).map kl := congrArg (fun k => k ≫ _) ha
      _ = (Functor.associator (kernelDerivedTensor A D E P) T T).hom ≫
          whiskerLeft (kernelDerivedTensor A D E P) (kernelCompositionIso A E E E hE I I).hom ≫
          (kernelCompositionIso A D E E hD P (kernelCompose A E E E hE I I)).hom ≫
          (kernelDerivedTensorFunctor A D E).map kr := by
        dsimp only [kernelAssociatorRightPath]
        simp only [Category.assoc]
        rw [hta]
      _ = (Functor.associator (kernelDerivedTensor A D E P) T T).hom ≫
          whiskerLeft (kernelDerivedTensor A D E P) (kernelCompositionIso A E E E hE I I).hom ≫
          whiskerLeft (kernelDerivedTensor A D E P) ((kernelDerivedTensorFunctor A E E).map r) ≫
          c.hom := by
        slice_lhs 3 4 => erw [← hs]
        rfl
      _ = _ := by
        slice_lhs 2 3 => erw [← whiskerLeft_comp]
        erw [hr]
  apply NatTrans.ext
  funext X
  have hx := NatTrans.congr_app heq X
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app, Functor.leftUnitor_hom_app, Functor.map_comp] at hx
  erw [Category.comp_id, Category.id_comp] at hx
  have hx' := (cancel_mono (c.hom.app X)).1 hx
  let : T.Faithful := Functor.Faithful.of_iso (kernelIdentityIso A E).symm
  rw [← T.map_comp] at hx'
  have hm := T.map_injective hx'
  simp only [NatTrans.comp_app, whiskerLeft_app, Functor.rightUnitor_hom_app]
  erw [Category.comp_id]
  exact hm

end SerrePositivity.DifferentialGraded.Morita
end

end CoherenceLeftUnitMain
