module
public import SerrePositivity.DifferentialGraded.Resolution.Free.Words
public import SerrePositivity.DifferentialGraded.Tensor.KFlatColimits

/-! # 自由dg圏の候補Hom複体：恒等pathと非空pathの直和

ここでは内部微分と辺のchain mapだけを使う。cellを付ける追加微分はまだ含めない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v)

/-- 恒等pathの添字は端点の等式を持つ。非空pathは内部頂点のリスト。 -/
abbrev PathIndex (x y : D) := PLift (x = y) ⊕ List D

/-- 恒等pathは単位複体、非空pathは辺のtensor。 -/
def pathTensor (K : ComplexQuiver A D) {x y : D} : PathIndex D x y → Complex A
  | .inl _ => 𝟙_ (Complex A)
  | .inr w => wordTensor A D K w x y

variable [Small.{u} D]

instance pathIndexSmall (x y : D) : Small.{u} (PathIndex D x y) := inferInstance

/-- 内部微分を持つ自由Hom候補。各次数は全有限pathの直和である。 -/
abbrev homComplex (K : ComplexQuiver A D) (x y : D) : Complex A :=
  ∐ (pathTensor A D K (x := x) (y := y))

def pathInclusion (K : ComplexQuiver A D) (x y : D) (p : PathIndex D x y) :
    pathTensor A D K p ⟶ homComplex A D K x y := Sigma.ι _ p

/-- 恒等pathからの単位候補。 -/
def unitInclusion (K : ComplexQuiver A D) (x : D) :
    𝟙_ (Complex A) ⟶ homComplex A D K x x := pathInclusion A D K x x (.inl ⟨rfl⟩)

/-- 一辺pathの包含。恒等pathとは添字を分けて保持する。 -/
def edgeInclusion (K : ComplexQuiver A D) (x y : D) :
    K x y ⟶ homComplex A D K x y := pathInclusion A D K x y (.inr [])

lemma homComplex_ext (K : ComplexQuiver A D) (x y : D) {T : Complex A}
    (f g : homComplex A D K x y ⟶ T)
    (h : ∀ p, pathInclusion A D K x y p ≫ f = pathInclusion A D K x y p ≫ g) : f = g :=
  Sigma.hom_ext f g h

omit [Small.{u} D] in
lemma pathTensor_kFlat (K : ComplexQuiver A D) (hK : ∀ x y, complexKFlat A (K x y))
    {x y : D} (p : PathIndex D x y) : complexKFlat A (pathTensor A D K p) := by
  cases p with
  | inl _ => exact complexKFlat_unit A
  | inr w => exact wordTensor_kFlat A D K hK w x y

/-- 全path直和のK-flat性は辺のK-flat性から従う。 -/
lemma homComplex_kFlat (K : ComplexQuiver A D) (hK : ∀ x y, complexKFlat A (K x y))
    (x y : D) : complexKFlat A (homComplex A D K x y) := by
  have : HasExactColimitsOfShape (Discrete (PathIndex D x y)) (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (Discrete.equivalence (equivShrink.{u} (PathIndex D x y)).symm)
  exact complexKFlat_colimit A (Discrete.functor (pathTensor A D K (x := x) (y := y)))
    (fun p => pathTensor_kFlat A D K hK p.as)

end SerrePositivity.DifferentialGraded.FreeDGCategory
