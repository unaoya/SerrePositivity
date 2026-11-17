module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.UniversalCech
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Milnor.ArcIntervalOverlap

/-!
概要：重なる二つの区間の係数列を、任意の基底代数Tの加群の短複体として固定する。
方針：Tの構造射を左右へ送り、二つの制限のtensor射の差を取る。
規約：この構成ではTの平坦性・完全性を要求せず、元の指定区間と構造射を保つ。
使われ方：2iのO04、BM18 Proposition 4.8(5)の図式(6)のT係数版。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity
open SerrePositivity.BhattScholze.Perfectoidization
open scoped TensorProduct
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

set_option backward.isDefEq.respectTransparency false

/-- 計画O04：任意のTへの係数移送後の、元の単位と制限の差による短複体。 -/
def overlapTensorModuleComplex {V T : Type u} [CommRing V] [CommRing T]
    [Algebra V T] {a b : PrimeSpectrum V} (h : a ≤ b) :
    ShortComplex (ModuleCat.{u} T) := by
  let L := Localization.AtPrime b.asIdeal
  let Q := V ⧸ a.asIdeal
  let I := ValuationIntervalRing h
  let rL : T ⊗[V] L →ₗ[T] T ⊗[V] I :=
    (Algebra.TensorProduct.map (AlgHom.id T T) (Arc.localizationToInterval h)).toLinearMap
  let rQ : T ⊗[V] Q →ₗ[T] T ⊗[V] I :=
    (Algebra.TensorProduct.map (AlgHom.id T T) (IsScalarTower.toAlgHom V Q I)).toLinearMap
  exact ShortComplex.moduleCatMk
    ((Algebra.linearMap T (T ⊗[V] L)).prod (Algebra.linearMap T (T ⊗[V] Q)))
    (rL.comp (LinearMap.fst T _ _) - rQ.comp (LinearMap.snd T _ _)) (by
      apply LinearMap.ext
      intro t
      change (Algebra.TensorProduct.map (AlgHom.id T T) (Arc.localizationToInterval h))
        (t ⊗ₜ[V] (1 : L)) -
        (Algebra.TensorProduct.map (AlgHom.id T T) (IsScalarTower.toAlgHom V Q I))
          (t ⊗ₜ[V] (1 : Q)) = 0
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, sub_self])

end SerrePositivity.AlgebraicGeometry.ArcRouteB
