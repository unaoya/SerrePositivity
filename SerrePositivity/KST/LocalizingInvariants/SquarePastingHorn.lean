module

public import SerrePositivity.InfinityCategories.Core.EquivalencePathInnerFibration
public import SerrePositivity.InfinityCategories.Stable.PastingShapes
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：共有辺が一致する二つの正方形を、内ホーン上の矢印族として貼る。
方針：転置した正方形を curry して、二次内ホーンの押し出しを使う。
規約：両正方形と四つの水平辺を厳密に保持。使われ方：指定合成を持つ長方形の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SquarePastingHorn
variable {X : SSet.{u}} (L R : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X)
  (h : squareRightEdge ≫ L = squareLeftEdge ≫ R)

def transposed (S : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) :
    (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  curry ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ S)

include h in
lemma compatible : stdSimplex.δ (0 : Fin 2) ≫ transposed L =
    stdSimplex.δ (1 : Fin 2) ≫ transposed R := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, transposed, transposed,
    uncurry_curry, uncurry_curry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  have ht : t = PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) n := by
    apply SSet.stdSimplex.ext
    intro j
    apply Fin.ext
    have ht := (t j).isLt
    have hc := (PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) n j).isLt
    omega
  subst t
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋n⦌)) s
  exact he

def diagram : (horn 2 1 : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  horn₂₁.isPushout.desc (transposed L) (transposed R) (compatible L R h)

lemma diagram_left : horn₂₁.ι₀₁ ≫ diagram L R h = transposed L :=
  horn₂₁.isPushout.inl_desc _ _ _

lemma diagram_right : horn₂₁.ι₁₂ ≫ diagram L R h = transposed R :=
  horn₂₁.isPushout.inr_desc _ _ _

lemma transposed_bottom (S : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) :
    transposed S ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      squareBottomEdge ≫ S := by
  rw [transposed, curry_evaluateFunctorAt_interval]
  rfl

lemma transposed_top (S : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) :
    transposed S ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      squareTopEdge ≫ S := by
  rw [transposed, curry_evaluateFunctorAt_interval]
  rfl

end SerrePositivity.KST.LocalizingInvariants.SquarePastingHorn
