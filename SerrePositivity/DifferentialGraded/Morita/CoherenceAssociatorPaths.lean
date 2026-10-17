module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceAssociatorModels
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionWhisker

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
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
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
