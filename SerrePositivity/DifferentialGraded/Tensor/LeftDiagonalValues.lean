module
public import SerrePositivity.DifferentialGraded.Tensor.YonedaRepresentative
public import SerrePositivity.DifferentialGraded.Tensor.ChangeLeft
public import SerrePositivity.DifferentialGraded.Tensor.ElementMap
public import SerrePositivity.DifferentialGraded.Tensor.LeftUnitSigns
public import SerrePositivity.DifferentialGraded.Bimodule.IdentityTranspose

/-! # 対角bimoduleとの左単位比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]

/-- 対角の左制限を既存leftRepresentableへ比較した左単位同型。 -/
def leftUnitValueIso (M : RightModule A B) (b : B) :
    obj A B M ((Bimodule.diagonal A B).leftAt b) ≅ M.obj (op b) :=
  BalancedTensor.changeLeft A B M (Bimodule.diagonal_leftAt A B b) ≪≫
    BalancedTensor.leftYonedaIso A B b M

@[reassoc (attr := simp)]
lemma ι_leftUnitValueIso_hom (M : RightModule A B) (b x : B) :
    BalancedTensor.ι A B M ((Bimodule.diagonal A B).leftAt b) x ≫
      (leftUnitValueIso A B M b).hom = BalancedTensor.rightAction A B M b x := by
  change BalancedTensor.ι A B M ((Bimodule.diagonal A B).leftAt b) x ≫
      (BalancedTensor.changeLeft A B M (Bimodule.diagonal_leftAt A B b)).hom ≫
        BalancedTensor.leftYonedaEvaluation A B b M = _
  rw [BalancedTensor.ι_changeLeft_hom_assoc]
  change 𝟙 _ ≫ BalancedTensor.ι A B M (leftRepresentable A b) x ≫
    BalancedTensor.leftYonedaEvaluation A B b M = _
  rw [Category.id_comp, BalancedTensor.ι_leftYonedaEvaluation]

lemma leftUnitValueIso_hom_element (M : RightModule A B) (b x : B)
    {r s n : ℤ} (m : (M.obj (op x)).X r) (f : GradedHom A b x s) (hn : r + s = n) :
    (leftUnitValueIso A B M b).hom.f n
      (BalancedTensor.element A B M ((Bimodule.diagonal A B).leftAt b) x m f hn) =
    (r * s).negOnePow • moduleAction A M f m hn := by
  have h := BalancedTensor.element_postcompose A B M
    ((Bimodule.diagonal A B).leftAt b) x (leftUnitValueIso A B M b).hom
    (BalancedTensor.rightAction A B M b x)
    (ι_leftUnitValueIso_hom A B M b x) m f hn
  exact h.trans (BalancedTensor.rightAction_apply A B M b x r s n hn m f)

/-- 型を明示した左単位の射。等式輸送を含む同型の展開を避ける入口。 -/
def leftUnitValueHom (M : RightModule A B) (b : B) :
    BalancedTensor.obj A B M ((Bimodule.diagonal A B).leftAt b) ⟶ M.obj (op b) :=
  (leftUnitValueIso A B M b).hom

lemma leftUnitValueHom_element (M : RightModule A B) (b x : B)
    {r s n : ℤ} (m : (M.obj (op x)).X r) (f : GradedHom A b x s) (hn : r + s = n) :
    (leftUnitValueHom A B M b).f n
      (BalancedTensor.element A B M ((Bimodule.diagonal A B).leftAt b) x m f hn) =
    (r * s).negOnePow • moduleAction A M f m hn :=
  leftUnitValueIso_hom_element A B M b x m f hn

end SerrePositivity.DifferentialGraded.BalancedTensor
