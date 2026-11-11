module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGTensorElementCalculus
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexTensorBoundary
/-!
概要：二つの局所 Hom の実境界 cochain の tensor 和の微分式。
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
/-- 指定した二原始元の tensor 和は、同じ二閉射の tensor の差を境界に持つ。 -/
lemma dgTensorBoundary (x y : DGTensorCategory R B C)
    (f₀ f₁ : GradedHom R x.1 y.1 0) (g₀ g₁ : GradedHom R x.2 y.2 0)
    (h : GradedHom R x.1 y.1 (-1)) (k : GradedHom R x.2 y.2 (-1))
    (hf : (x.1 ⟶[Complex R] y.1).d 0 1 f₀ = 0)
    (hg : (x.2 ⟶[Complex R] y.2).d 0 1 g₁ = 0)
    (hh : (x.1 ⟶[Complex R] y.1).d (-1) 0 h = f₁ - f₀)
    (hk : (x.2 ⟶[Complex R] y.2).d (-1) 0 k = g₁ - g₀) :
    differential R (dgTensorElement R h g₁ (by decide : (-1 : ℤ) + 0 = -1) +
      dgTensorElement R f₀ k (by decide : (0 : ℤ) + -1 = -1)) =
    dgTensorElement R f₁ g₁ (by decide : (0 : ℤ) + 0 = 0) -
      dgTensorElement R f₀ g₀ (by decide : (0 : ℤ) + 0 = 0) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTensorBoundary R (x.1 ⟶[Complex R] y.1) (x.2 ⟶[Complex R] y.2)
    f₀ f₁ g₀ g₁ h k hf hg hh hk
end SerrePositivity.InfinityCategories.Project.DerivedCategories
