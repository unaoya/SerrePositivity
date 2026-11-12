module
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle
/-!
概要：斉次 tensor の同じ Leibniz 則・双線形性・零・閉性を照合する。
方針：同じ斉次 tensor の微分を端点次数0・1で評価して、実境界式へ接続する。
規約：Small 性や平坦性は不要。使われ方：二つの実 dg nerve 単体の tensor 構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory HomologicalComplex
variable (R : Type u) [CommRing R]
variable (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
/-- 同じ全次数の tensor 要素の実微分・線形性・閉性。 -/
lemma dgTensorElement_differential {x y : DGTensorCategory R B C} {p q n : ℤ}
    (f : GradedHom R x.1 y.1 p) (g : GradedHom R x.2 y.2 q) (hn : p + q = n) :
    differential R (dgTensorElement R f g hn) =
      dgTensorElement R (differential R f) g (by omega) +
        p.negOnePow • dgTensorElement R f (differential R g) (by omega) := by
  exact SerrePositivity.cochainTensor_d_apply_ι _ _ p q n hn f g
/-- 同じ全次数の tensor 要素の実微分・線形性・閉性。 -/
lemma dgTensorElement_add_left {x y : DGTensorCategory R B C} {p q n : ℤ}
    (f f' : GradedHom R x.1 y.1 p) (g : GradedHom R x.2 y.2 q) (hn : p + q = n) :
    dgTensorElement R (f + f') g hn = dgTensorElement R f g hn + dgTensorElement R f' g hn := by
  simp [dgTensorElement, TensorProduct.add_tmul]
/-- 同じ全次数の tensor 要素の実微分・線形性・閉性。 -/
lemma dgTensorElement_add_right {x y : DGTensorCategory R B C} {p q n : ℤ}
    (f : GradedHom R x.1 y.1 p) (g g' : GradedHom R x.2 y.2 q) (hn : p + q = n) :
    dgTensorElement R f (g + g') hn = dgTensorElement R f g hn + dgTensorElement R f g' hn := by
  simp [dgTensorElement, TensorProduct.tmul_add]
/-- 同じ全次数の tensor 要素の実微分・線形性・閉性。 -/
lemma dgTensorElement_sub_left {x y : DGTensorCategory R B C} {p q n : ℤ}
    (f f' : GradedHom R x.1 y.1 p) (g : GradedHom R x.2 y.2 q) (hn : p + q = n) :
    dgTensorElement R (f - f') g hn = dgTensorElement R f g hn - dgTensorElement R f' g hn := by
  simp [dgTensorElement, TensorProduct.sub_tmul]
/-- 同じ全次数の tensor 要素の実微分・線形性・閉性。 -/
lemma dgTensorElement_sub_right {x y : DGTensorCategory R B C} {p q n : ℤ}
    (f : GradedHom R x.1 y.1 p) (g g' : GradedHom R x.2 y.2 q) (hn : p + q = n) :
    dgTensorElement R f (g - g') hn = dgTensorElement R f g hn - dgTensorElement R f g' hn := by
  simp [dgTensorElement, TensorProduct.tmul_sub]
/-- 同じ全次数の tensor 要素の実微分・線形性・閉性。 -/
lemma dgTensorElement_zero_left {x y : DGTensorCategory R B C} {p q n : ℤ}
    (g : GradedHom R x.2 y.2 q) (hn : p + q = n) :
    dgTensorElement R (0 : GradedHom R x.1 y.1 p) g hn = 0 := by
  simp [dgTensorElement]
/-- 同じ全次数の tensor 要素の実微分・線形性・閉性。 -/
lemma dgTensorElement_zero_right {x y : DGTensorCategory R B C} {p q n : ℤ}
    (f : GradedHom R x.1 y.1 p) (hn : p + q = n) :
    dgTensorElement R f (0 : GradedHom R x.2 y.2 q) hn = 0 := by
  simp [dgTensorElement]
/-- 同じ全次数の tensor 要素の実微分・線形性・閉性。 -/
lemma dgTensorElement_closed {x y : DGTensorCategory R B C}
    (f : GradedHom R x.1 y.1 0) (g : GradedHom R x.2 y.2 0)
    (hf : differential R f = 0) (hg : differential R g = 0) :
    differential R (dgTensorElement R f g (show (0 : ℤ) + 0 = 0 from rfl)) = 0 := by
  rw [dgTensorElement_differential, hf, hg, dgTensorElement_zero_left,
    dgTensorElement_zero_right, smul_zero, add_zero]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
