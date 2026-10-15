module
public import SerrePositivity.DifferentialGraded.Tensor.RightUnit
public import SerrePositivity.DifferentialGraded.Tensor.LeftDiagonalUnit
public import SerrePositivity.DifferentialGraded.Tensor.LeftDiagonalHom

/-! # 対角bimoduleとの左単位比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 対角の左制限を既存leftRepresentableへ比較した左単位同型。 -/
def leftUnitValueIso (P : Bimodule A B C) (b : B) (c : C) :
    (compose A B B C (Bimodule.diagonal A B) P).value b c ≅ P.value b c :=
  BalancedTensor.leftUnitValueIso A B (P.rightAt c) b

@[reassoc (attr := simp)]
lemma ι_leftUnitValueIso_hom (P : Bimodule A B C) (b x : B) (c : C) :
    BalancedTensor.ι A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b) x ≫
      (leftUnitValueIso A B C P b c).hom = BalancedTensor.rightAction A B (P.rightAt c) b x :=
  BalancedTensor.ι_leftUnitValueIso_hom A B (P.rightAt c) b x

lemma leftUnitValueIso_hom_element (P : Bimodule A B C) (b x : B) (c : C)
    {r s n : ℤ} (m : (P.value x c).X r) (f : GradedHom A b x s) (hn : r + s = n) :
    (leftUnitValueIso A B C P b c).hom.f n
      (BalancedTensor.element A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b) x m f hn) =
    (r * s).negOnePow • moduleAction A (P.rightAt c) f m hn :=
  BalancedTensor.leftUnitValueIso_hom_element A B (P.rightAt c) b x m f hn

/-- 型を明示した左単位の射。等式輸送を含む同型の展開を避ける入口。 -/
def leftUnitValueHom (P : Bimodule A B C) (b : B) (c : C) :
    BalancedTensor.obj A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b) ⟶ P.value b c :=
  (leftUnitValueIso A B C P b c).hom

lemma leftUnitValueHom_element (P : Bimodule A B C) (b x : B) (c : C)
    {r s n : ℤ} (m : (P.value x c).X r) (f : GradedHom A b x s) (hn : r + s = n) :
    (leftUnitValueHom A B C P b c).f n
      (BalancedTensor.element A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b) x m f hn) =
    (r * s).negOnePow • moduleAction A (P.rightAt c) f m hn :=
  leftUnitValueIso_hom_element A B C P b x c m f hn

/-- 左単位の比較は残る右Bの全Homに関して自然。 -/
lemma leftUnitValue_naturality (P : Bimodule A B C) (b b' : B) (c : C) :
    ((compose A B B C (Bimodule.diagonal A B) P).rightAt c).map (op b) (op b') ≫
      homPostcompose (BalancedTensor.obj A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b))
        (Q := BalancedTensor.obj A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b'))
        (T := (P.rightAt c).obj (op b')) (leftUnitValueHom A B C P b' c) =
    (P.rightAt c).map (op b) (op b') ≫
      homPrecompose
        (P := BalancedTensor.obj A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b))
        (Q := (P.rightAt c).obj (op b)) (leftUnitValueHom A B C P b c)
        ((P.rightAt c).obj (op b')) := by
  change ((Bimodule.diagonal A B).transposeHom (op b) (op b') ≫
      BalancedTensor.leftHomMap A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b)
        ((Bimodule.diagonal A B).leftAt b')) ≫
      homPostcompose _ (BalancedTensor.leftUnitValueHom A B (P.rightAt c) b') =
    (P.rightAt c).map (op b) (op b') ≫
      homPrecompose (BalancedTensor.leftUnitValueHom A B (P.rightAt c) b) _
  exact BalancedTensor.leftUnitValue_naturality A B (P.rightAt c) b b'

/-- 値ごとの左単位を実際の右B加群同型へ束ねる。 -/
def leftUnitIso (P : Bimodule A B C) (c : C) :
    ForgetEnrichment.of (Complex A) ((compose A B B C (Bimodule.diagonal A B) P).rightAt c) ≅
      ForgetEnrichment.of (Complex A) (P.rightAt c) :=
  moduleIsoMk A B (fun b => leftUnitValueIso A B C P b.unop c)
    (fun b b' => by
      change ((compose A B B C (Bimodule.diagonal A B) P).rightAt c).map b b' ≫
          homPostcompose
            (BalancedTensor.obj A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b.unop))
            (leftUnitValueIso A B C P b'.unop c).hom =
        (P.rightAt c).map b b' ≫
          homPrecompose (leftUnitValueIso A B C P b.unop c).hom ((P.rightAt c).obj b')
      have h := leftUnitValue_naturality A B C P b.unop b'.unop c
      simpa only [Opposite.op_unop, leftUnitValueHom] using h)

@[simp]
lemma leftUnitIso_hom_eval (P : Bimodule A B C) (b : B) (c : C) :
    (moduleEvaluation A B b).map
      (X := ForgetEnrichment.of (Complex A)
        ((compose A B B C (Bimodule.diagonal A B) P).rightAt c))
      (Y := ForgetEnrichment.of (Complex A) (P.rightAt c)) (leftUnitIso A B C P c).hom =
      (leftUnitValueIso A B C P b c).hom :=
  moduleIsoMk_hom_eval A B _ _ b

@[simp]
lemma leftUnitIso_inv_eval (P : Bimodule A B C) (b : B) (c : C) :
    (moduleEvaluation A B b).map
      (X := ForgetEnrichment.of (Complex A) (P.rightAt c))
      (Y := ForgetEnrichment.of (Complex A)
        ((compose A B B C (Bimodule.diagonal A B) P).rightAt c)) (leftUnitIso A B C P c).inv =
      (leftUnitValueIso A B C P b c).inv :=
  moduleIsoMk_inv_eval A B _ _ b

@[simp]
lemma leftUnitIso_hom_component (P : Bimodule A B C) (b : B) (c : C) :
    moduleMorphismComponent A B
      ((compose A B B C (Bimodule.diagonal A B) P).rightAt c) (P.rightAt c)
      (leftUnitIso A B C P c).hom b = (leftUnitValueIso A B C P b c).hom :=
  moduleIsoMk_hom_eval A B _ _ b

/-- 左単位は左Cの全Homにも自然。Cの対象のsmallnessは不要。 -/
lemma leftUnitValue_left_naturality (P : Bimodule A B C) (b : B) (c c' : C) :
    (compose A B B C (Bimodule.diagonal A B) P).toFunctor.map c c' ≫
      moduleHomπ A B (rightAt A B B C (Bimodule.diagonal A B) P c)
        (rightAt A B B C (Bimodule.diagonal A B) P c') b ≫
      homPostcompose ((compose A B B C (Bimodule.diagonal A B) P).value b c)
        (leftUnitValueIso A B C P b c').hom =
    P.toFunctor.map c c' ≫ moduleHomπ A B (P.rightAt c) (P.rightAt c') b ≫
      homPrecompose (leftUnitValueIso A B C P b c).hom (P.value b c') := by
  change ((compose A B B C (Bimodule.diagonal A B) P).toFunctor.map c c' ≫
      moduleHomπ A B (rightAt A B B C (Bimodule.diagonal A B) P c)
        (rightAt A B B C (Bimodule.diagonal A B) P c') b) ≫
      homPostcompose (BalancedTensor.obj A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b))
        (BalancedTensor.leftUnitValueHom A B (P.rightAt c') b) =
    (P.toFunctor.map c c' ≫ moduleHomπ A B (P.rightAt c) (P.rightAt c') b) ≫
      homPrecompose (BalancedTensor.leftUnitValueHom A B (P.rightAt c) b) (P.value b c')
  rw [compose_leftMap_π]
  rw [Category.assoc, BalancedTensor.leftUnitValueHom_enriched_naturality, ← Category.assoc]

/-- 値ごとの自然性を右B加群の主Hom endへ束ねる。 -/
lemma leftUnitIso_naturality (P : Bimodule A B C) (c c' : C) :
    (compose A B B C (Bimodule.diagonal A B) P).toFunctor.map c c' ≫
      moduleHomPostcompose A B
        ((compose A B B C (Bimodule.diagonal A B) P).rightAt c)
        ((compose A B B C (Bimodule.diagonal A B) P).rightAt c') (P.rightAt c')
        (leftUnitIso A B C P c').hom =
    P.toFunctor.map c c' ≫ moduleHomPrecompose A B
      ((compose A B B C (Bimodule.diagonal A B) P).rightAt c) (P.rightAt c) (P.rightAt c')
      (leftUnitIso A B C P c).hom := by
  apply moduleHom_ext
  intro b
  simp only [Category.assoc]
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  simp only [leftUnitIso_hom_component]
  exact leftUnitValue_left_naturality A B C P b c c'

end SerrePositivity.DifferentialGraded.BimoduleTensor
