module
public import SerrePositivity.KST.SConstruction.LeftTensorYonedaParameter
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
public import SerrePositivity.DifferentialGraded.Tensor.Fubini

/-! # 実双加群の右単位比較の任意パラメータ自然性
概要：対角双加群との右単位比較は、任意複体 K の双加群変換にも自然である。
方針：全対象で左 tensor の Yoneda 評価へ帰着し、全加群 Hom の評価で反映する。
規約：閉零自然変換だけで代用しない。使われ方：graph 合成の右入力自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [Small.{u} B] [DGCategory A C] [Small.{u} C]

/-- 元の右単位の各値は、任意 K の元の双加群変換と全次数で可換。 -/
lemma bimoduleRightUnitParameter_value {K : Complex A} {P P' : Bimodule A B C}
    (τ : BimoduleParamTrans A B C K P P') (b : B) (c : C) :
    BimoduleTensor.firstParamHom A B C C (Bimodule.diagonal A C) τ b c ≫
        homPostcompose ((BimoduleTensor.compose A B C C P (Bimodule.diagonal A C)).value b c)
          (BimoduleTensor.rightUnitValueIso A B C P' b c).hom =
      Bimodule.paramValue A B C τ b c ≫
        homPrecompose (BimoduleTensor.rightUnitValueIso A B C P b c).hom (P'.value b c) :=
  dgLeftParamHom_yoneda_naturality A C (Bimodule.paramLeftAt A B C τ b) c

/-- 元の右単位の加群同型は、任意 K の双加群変換と全 Hom 複体で可換。 -/
lemma bimoduleRightUnitParameter_naturality {K : Complex A} {P P' : Bimodule A B C}
    (τ : BimoduleParamTrans A B C K P P') (c : C) :
    (BimoduleTensor.firstParam A B C C (Bimodule.diagonal A C) τ).app c ≫
        moduleHomPostcompose A B _ _ _ (BimoduleTensor.rightUnitIso A B C P' c).hom =
      τ.app c ≫ moduleHomPrecompose A B _ _ _ (BimoduleTensor.rightUnitIso A B C P c).hom := by
  apply moduleHom_ext
  intro b
  simp only [Category.assoc, moduleHomPostcompose_π, moduleHomPrecompose_π,
    BimoduleTensor.rightUnitIso_hom_component]
  simp only [← Category.assoc]
  change Bimodule.paramValue A B C
      (BimoduleTensor.firstParam A B C C (Bimodule.diagonal A C) τ) b c ≫ _ =
    Bimodule.paramValue A B C τ b c ≫ _
  rw [BimoduleTensor.firstParam_value]
  exact bimoduleRightUnitParameter_value A B C τ b c

end SerrePositivity.KST.SConstruction
