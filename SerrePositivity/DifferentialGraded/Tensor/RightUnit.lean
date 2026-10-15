module
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule
public import SerrePositivity.DifferentialGraded.Tensor.YonedaRepresentative
public import SerrePositivity.DifferentialGraded.Bimodule.Identity
public import SerrePositivity.DifferentialGraded.Module.Isomorphism
public import SerrePositivity.DifferentialGraded.Module.HomWhisker

/-! # 対角bimoduleとの右単位比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

/-- 各B対象での右単位はrepresentable tensorのYoneda同型。 -/
def rightUnitValueIso (P : Bimodule A B C) (b : B) (c : C) :
    (compose A B C C P (Bimodule.diagonal A C)).value b c ≅ P.value b c :=
  BalancedTensor.yonedaIso A C c (P.leftAt b)

/-- 右単位の比較は右Bの全Homに関して自然。 -/
lemma rightUnitValue_naturality (P : Bimodule A B C) (b b' : Bᵒᵖ) (c : C) :
    ((compose A B C C P (Bimodule.diagonal A C)).rightAt c).map b b' ≫
      homPostcompose ((compose A B C C P (Bimodule.diagonal A C)).value b.unop c)
        (rightUnitValueIso A B C P b'.unop c).hom =
    (P.rightAt c).map b b' ≫
      homPrecompose (rightUnitValueIso A B C P b.unop c).hom (P.value b'.unop c) := by
  change (P.transposeHom b b' ≫
      BalancedTensor.leftHomMap A C (representable A c) (P.leftAt b.unop) (P.leftAt b'.unop)) ≫
        homPostcompose (BalancedTensor.obj A C (representable A c) (P.leftAt b.unop))
          (BalancedTensor.yonedaEvaluation A C c (P.leftAt b'.unop)) =
    (P.rightAt c).map b b' ≫
      homPrecompose (BalancedTensor.yonedaEvaluation A C c (P.leftAt b.unop)) (P.value b'.unop c)
  rw [Category.assoc, BalancedTensor.yonedaEvaluation_enriched_naturality, ← Category.assoc]
  change (P.transposeHom b b' ≫ moduleHomπ A Cᵒᵖ
      (P.leftAt b.unop).toRightOpposite (P.leftAt b'.unop).toRightOpposite (op c)) ≫ _ = _
  rw [Bimodule.transposeHom_π]
  rfl

/-- 全次数自然な成分同型を実際の右B加群同型へ束ねる。 -/
def rightUnitIso (P : Bimodule A B C) (c : C) :
    ForgetEnrichment.of (Complex A) ((compose A B C C P (Bimodule.diagonal A C)).rightAt c) ≅
      ForgetEnrichment.of (Complex A) (P.rightAt c) :=
  moduleIsoMk A B (fun b => rightUnitValueIso A B C P b.unop c)
    (fun b b' => rightUnitValue_naturality A B C P b b' c)

@[simp]
lemma rightUnitIso_hom_eval (P : Bimodule A B C) (b : B) (c : C) :
    (moduleEvaluation A B b).map
      (X := ForgetEnrichment.of (Complex A)
        ((compose A B C C P (Bimodule.diagonal A C)).rightAt c))
      (Y := ForgetEnrichment.of (Complex A) (P.rightAt c)) (rightUnitIso A B C P c).hom =
      (rightUnitValueIso A B C P b c).hom :=
  moduleIsoMk_hom_eval A B _ _ b

@[simp]
lemma rightUnitIso_inv_eval (P : Bimodule A B C) (b : B) (c : C) :
    (moduleEvaluation A B b).map
      (X := ForgetEnrichment.of (Complex A) (P.rightAt c))
      (Y := ForgetEnrichment.of (Complex A)
        ((compose A B C C P (Bimodule.diagonal A C)).rightAt c)) (rightUnitIso A B C P c).inv =
      (rightUnitValueIso A B C P b c).inv :=
  moduleIsoMk_inv_eval A B _ _ b

/-- 右単位の比較は左Cの全Homにも自然。 -/
lemma rightUnitValue_left_naturality (P : Bimodule A B C) (b : B) (c c' : C) :
    (compose A B C C P (Bimodule.diagonal A C)).toFunctor.map c c' ≫
      moduleHomπ A B (rightAt A B C C P (Bimodule.diagonal A C) c)
        (rightAt A B C C P (Bimodule.diagonal A C) c') b ≫
      homPostcompose ((compose A B C C P (Bimodule.diagonal A C)).value b c)
        (rightUnitValueIso A B C P b c').hom =
    P.toFunctor.map c c' ≫ moduleHomπ A B (P.rightAt c) (P.rightAt c') b ≫
      homPrecompose (rightUnitValueIso A B C P b c).hom (P.value b c') := by
  change ((compose A B C C P (Bimodule.diagonal A C)).toFunctor.map c c' ≫
      moduleHomπ A B (rightAt A B C C P (Bimodule.diagonal A C) c)
        (rightAt A B C C P (Bimodule.diagonal A C) c') b) ≫
      homPostcompose (BalancedTensor.obj A C (representable A c) (P.leftAt b))
        (BalancedTensor.yonedaEvaluation A C c' (P.leftAt b)) =
    (P.leftAt b).map c c' ≫
      homPrecompose (BalancedTensor.yonedaEvaluation A C c (P.leftAt b)) (P.value b c')
  rw [compose_leftMap_π]
  change yonedaHom A C c c' ≫
      BalancedTensor.rightHomMap A C (representable A c) (representable A c') (P.leftAt b) ≫
        homPostcompose (BalancedTensor.obj A C (representable A c) (P.leftAt b))
          (BalancedTensor.yonedaEvaluation A C c' (P.leftAt b)) =
    (P.leftAt b).map c c' ≫
      homPrecompose (BalancedTensor.yonedaEvaluation A C c (P.leftAt b)) (P.value b c')
  exact BalancedTensor.yonedaEvaluation_representative_naturality A C (P.leftAt b) c c'

@[simp]
lemma rightUnitIso_hom_component (P : Bimodule A B C) (b : B) (c : C) :
    moduleMorphismComponent A B
      ((compose A B C C P (Bimodule.diagonal A C)).rightAt c) (P.rightAt c)
      (rightUnitIso A B C P c).hom b = (rightUnitValueIso A B C P b c).hom :=
  moduleIsoMk_hom_eval A B _ _ b

/-- 成分での自然性を右B加群の全Hom endの等式へ束ねる。 -/
lemma rightUnitIso_naturality (P : Bimodule A B C) (c c' : C) :
    (compose A B C C P (Bimodule.diagonal A C)).toFunctor.map c c' ≫
      moduleHomPostcompose A B
        ((compose A B C C P (Bimodule.diagonal A C)).rightAt c)
        ((compose A B C C P (Bimodule.diagonal A C)).rightAt c') (P.rightAt c')
        (rightUnitIso A B C P c').hom =
    P.toFunctor.map c c' ≫ moduleHomPrecompose A B
      ((compose A B C C P (Bimodule.diagonal A C)).rightAt c) (P.rightAt c) (P.rightAt c')
      (rightUnitIso A B C P c).hom := by
  apply moduleHom_ext
  intro b
  simp only [Category.assoc]
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  simp only [rightUnitIso_hom_component]
  exact rightUnitValue_left_naturality A B C P b c c'

end SerrePositivity.DifferentialGraded.BimoduleTensor
