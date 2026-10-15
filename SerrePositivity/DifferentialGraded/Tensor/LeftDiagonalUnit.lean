module
public import SerrePositivity.DifferentialGraded.Tensor.LeftDiagonalValues

/-! # 左単位比較の全Hom自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]

/-- 対角の転置と左tensor作用を、値のHom複体の射として固定する。 -/
def diagonalTensorHomMap (M : RightModule A B) (b b' : B) :
    (op b ⟶[Complex A] op b') ⟶
      homComplex A (obj A B M ((Bimodule.diagonal A B).leftAt b))
        (obj A B M ((Bimodule.diagonal A B).leftAt b')) :=
  (Bimodule.diagonal A B).transposeHom (op b) (op b') ≫
    leftHomMap A B M ((Bimodule.diagonal A B).leftAt b) ((Bimodule.diagonal A B).leftAt b')

lemma diagonalTensorHomMap_element (M : RightModule A B) (b b' x : B)
    {p r s a n : ℤ} (ha : r + s = a) (hn : a + p = n)
    (f : GradedHom A (op b) (op b') p) (m : (M.obj (op x)).X r)
    (h : GradedHom A b x s) :
    ((diagonalTensorHomMap A B M b b').f p f).v a n hn
      (element A B M ((Bimodule.diagonal A B).leftAt b) x m h ha) =
    (p * r).negOnePow • element A B M ((Bimodule.diagonal A B).leftAt b') x m
      (forward A (D := B) (x := b') (y := b) (z := x) (n := p + s) f h (by omega))
      (by omega) := by
  have he := leftHomMap_element_of_sum A B M
    (((Bimodule.diagonal A B).transposeHom (op b) (op b')).f p f) x m h ha rfl hn
  have hd := Bimodule.diagonal_transpose_element A B (b := op b) (b' := op b')
    x f h (show s + p = p + s by omega)
  exact he.trans (congrArg (fun t => (p * r).negOnePow •
    element A B M ((Bimodule.diagonal A B).leftAt b') x m t (by omega)) hd)

/-- 左単位の自然性を純粋斉次生成元で計算する。 -/
lemma leftUnitValue_element_naturality_of_evaluation (M : RightModule A B) (b b' x : B)
    (ε : obj A B M ((Bimodule.diagonal A B).leftAt b) ⟶ M.obj (op b))
    (ε' : obj A B M ((Bimodule.diagonal A B).leftAt b') ⟶ M.obj (op b'))
    (he : ∀ (x : B) (r s a : ℤ) (m : (M.obj (op x)).X r) (h : GradedHom A b x s)
      (ha : r + s = a), ε.f a
        (element A B M ((Bimodule.diagonal A B).leftAt b) x m h ha) =
      (r * s).negOnePow • moduleAction A M h m ha)
    (he' : ∀ (x : B) (r s a : ℤ) (m : (M.obj (op x)).X r) (h : GradedHom A b' x s)
      (ha : r + s = a), ε'.f a
        (element A B M ((Bimodule.diagonal A B).leftAt b') x m h ha) =
      (r * s).negOnePow • moduleAction A M h m ha)
    (p r s a n : ℤ) (ha : r + s = a) (hn : a + p = n)
    (f : GradedHom A (op b) (op b') p) (m : (M.obj (op x)).X r)
    (h : GradedHom A b x s) :
    ε'.f n
      (((diagonalTensorHomMap A B M b b').f p f).v a n hn
        (element A B M ((Bimodule.diagonal A B).leftAt b) x m h ha)) =
    ((M.map (op b) (op b')).f p f).v a n hn
      (ε.f a
        (element A B M ((Bimodule.diagonal A B).leftAt b) x m h ha)) := by
  rw [diagonalTensorHomMap_element]
  simp only [Units.smul_def, map_zsmul]
  rw [he', he]
  simp only [Units.smul_def, map_zsmul]
  change (p * r).negOnePow • ((r * (p + s)).negOnePow •
      moduleAction A M (x := op x) (y := op b')
        (forward A (D := B) (x := b') (y := b) (z := x) (n := p + s) f h (by omega)) m (by omega)) =
    (r * s).negOnePow • moduleAction A M f
      (moduleAction A M h m ha) hn
  exact moduleAction_signed_representable A B M b b' x p r s a n ha hn f h m

/-- 左単位の自然性を純粋斉次生成元で計算する。 -/
lemma leftUnitValue_element_naturality (M : RightModule A B) (b b' x : B)
    (p r s a n : ℤ) (ha : r + s = a) (hn : a + p = n)
    (f : GradedHom A (op b) (op b') p) (m : (M.obj (op x)).X r)
    (h : GradedHom A b x s) :
    (leftUnitValueHom A B M b').f n
      (((diagonalTensorHomMap A B M b b').f p f).v a n hn
        (element A B M ((Bimodule.diagonal A B).leftAt b) x m h ha)) =
    ((M.map (op b) (op b')).f p f).v a n hn
      ((leftUnitValueHom A B M b).f a
        (element A B M ((Bimodule.diagonal A B).leftAt b) x m h ha)) :=
  leftUnitValue_element_naturality_of_evaluation A B M b b' x
    (leftUnitValueHom A B M b) (leftUnitValueHom A B M b')
    (fun x _r _s _a m h ha => leftUnitValueHom_element A B M b x m h ha)
    (fun x _r _s _a m h ha => leftUnitValueHom_element A B M b' x m h ha)
    p r s a n ha hn f m h

/-- 左単位の比較は残る右Bの全Homに関して自然。 -/
lemma leftUnitValue_naturality (M : RightModule A B) (b b' : B) :
    diagonalTensorHomMap A B M b b' ≫
      homPostcompose (BalancedTensor.obj A B M ((Bimodule.diagonal A B).leftAt b))
        (Q := BalancedTensor.obj A B M ((Bimodule.diagonal A B).leftAt b'))
        (T := M.obj (op b')) (leftUnitValueHom A B M b') =
    M.map (op b) (op b') ≫
      homPrecompose
        (P := BalancedTensor.obj A B M ((Bimodule.diagonal A B).leftAt b))
        (Q := M.obj (op b)) (leftUnitValueHom A B M b)
        (M.obj (op b')) := by
  exact homMap_post_pre_eq A B M ((Bimodule.diagonal A B).leftAt b)
    (diagonalTensorHomMap A B M b b')
    (M.map (op b) (op b')) (leftUnitValueHom A B M b') (leftUnitValueHom A B M b)
    (fun p f x r s a n ha hn m h =>
      leftUnitValue_element_naturality A B M b b' x p r s a n ha hn f m h)

end SerrePositivity.DifferentialGraded.BalancedTensor
