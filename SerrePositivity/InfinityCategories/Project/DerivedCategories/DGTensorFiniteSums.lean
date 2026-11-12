module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGTensorElementCalculus
/-!
概要：同じ指定次数の斉次 tensor が左右の有限和を保つことを照合する。
方針：元の HA 項、選択点の有限和、第二切断合成の実微分の同定を使う。
規約：同じ実 cochain を使う。使われ方：tensor 候補の全 HA の有限和の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped BigOperators
variable (R : Type u) [CommRing R]
/-- 元の実成分の微分と有限和の照合。 -/
lemma dgTensorElement_sum_left (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
    {ι : Type*} {x y : DGTensorCategory R B C} {p q n : ℤ} (S : Finset ι)
    (f : ι → GradedHom R x.1 y.1 p) (g : GradedHom R x.2 y.2 q) (hn : p + q = n) :
    dgTensorElement R (∑ i ∈ S, f i) g hn = ∑ i ∈ S, dgTensorElement R (f i) g hn := by
  simp [dgTensorElement, TensorProduct.sum_tmul]
/-- 元の実成分の微分と有限和の照合。 -/
lemma dgTensorElement_sum_right (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
    {ι : Type*} {x y : DGTensorCategory R B C} {p q n : ℤ} (S : Finset ι)
    (f : GradedHom R x.1 y.1 p) (g : ι → GradedHom R x.2 y.2 q) (hn : p + q = n) :
    dgTensorElement R f (∑ i ∈ S, g i) hn = ∑ i ∈ S, dgTensorElement R f (g i) hn := by
  simp [dgTensorElement, TensorProduct.tmul_sum]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
