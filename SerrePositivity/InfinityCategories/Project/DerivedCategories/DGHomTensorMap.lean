module
public import SerrePositivity.DifferentialGraded.Category.ObjectImage
public import SerrePositivity.DifferentialGraded.Bimodule.Tensor
public import SerrePositivity.DifferentialGraded.Bimodule.Basic
/-!
概要：任意の大きさの dg 圏の同じ局所 Hom から、二入力の実 Hom 鎖写像を作る。
方針：同じ代表作用を、小さい対角双加群と有限実充満像の局所計算へ比較する。
規約：元の dg 圏に Small 性を追加しない。使われ方：二変数の導来 Hom の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory Opposite
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
/-- 同じ二つの代表 Hom 写像と複体の実合成による、全 Hom 鎖写像。 -/
def dgHomTensorMap (x y : DGTensorCategory R Cᵒᵖ C) :
    (x ⟶[Complex R] y) ⟶ homComplex R
      (homObject R C x.1.unop x.2) (homObject R C y.1.unop y.2) :=
  ((representable R x.2).map x.1 y.1 ⊗ₘ (leftRepresentable R y.1.unop).map x.2 y.2) ≫
    enrichedComposition _ _ _
/-- 小さい dg 圏では、同じ対角双加群の実 Hom 写像そのもの。 -/
lemma dgHomTensorMap_diagonal [Small.{u} C] (x y : DGTensorCategory R Cᵒᵖ C) :
    dgHomTensorMap R C x y = (Bimodule.diagonal R C).uncurryHom x y := by
  dsimp only [dgHomTensorMap, Bimodule.uncurryHom]
  simp only [Bimodule.diagonal_rightAt]
  have h := congr_arg_heq (fun F : LeftModule R C => F.map x.2 y.2)
    (Bimodule.diagonal_leftAt R C y.1.unop)
  rw [eq_of_heq h]
  rfl
/-- 任意のラベル付き実充満像に沿い、同じ全 Hom 写像は厳密に一致する。 -/
lemma dgHomTensorMap_objectImage {I : Type w} (f : I → C)
    (a b c d : _root_.SerrePositivity.InfinityCategories.DGObjectImage f) :
    dgHomTensorMap R (_root_.SerrePositivity.InfinityCategories.DGObjectImage f) (op a, b) (op c, d) =
      dgHomTensorMap R C (op (f a.label), f b.label) (op (f c.label), f d.label) := by
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
