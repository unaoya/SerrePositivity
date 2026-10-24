module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitCylinder
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorTriangleSquare

/-!
概要：元の変換と余極限の指定辺を結ぶ、native 余錐の単位の全正方形。
方針：二時間の円柱を curry し、四辺を元の実円柱として回収する。
規約：四辺を選び直さない。使われ方：二つの合成三角形と native 比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の変換に沿う単位の自然性を表す、関手単体集合の実際の正方形。 -/
def coherentColimitUnitSquare : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u} :=
  curry ((α_ ((SSet.uliftFunctor.{u + 1, u}).obj B) Δ[1] Δ[1]).inv ≫
    (coherentColimitUnitCylinder B H).h)

/-- 横時間の始点では、元の始域の native 余錐の単位。 -/
lemma coherentColimitUnitSquare_bottom :
    SSet.ι₀ ≫ coherentColimitUnitSquare B H =
      curry (coconeTransformationHomotopy (coherentDiagramTotalCocone F)).h := by
  apply uncurry_injective
  rw [uncurry_natural_left, coherentColimitUnitSquare, uncurry_curry, uncurry_curry]
  have he : (_ ◁ SSet.ι₀) ≫
      (α_ ((SSet.uliftFunctor.{u + 1, u}).obj B) Δ[1] Δ[1]).inv = SSet.ι₀ := rfl
  rw [← Category.assoc, he]
  exact (coherentColimitUnitCylinder B H).h₀

/-- 横時間の終点では、元の標的の native 余錐の単位。 -/
lemma coherentColimitUnitSquare_top :
    SSet.ι₁ ≫ coherentColimitUnitSquare B H =
      curry (coconeTransformationHomotopy (coherentDiagramTotalCocone G)).h := by
  apply uncurry_injective
  rw [uncurry_natural_left, coherentColimitUnitSquare, uncurry_curry, uncurry_curry]
  have he : (_ ◁ SSet.ι₁) ≫
      (α_ ((SSet.uliftFunctor.{u + 1, u}).obj B) Δ[1] Δ[1]).inv = SSet.ι₁ := rfl
  rw [← Category.assoc, he]
  exact (coherentColimitUnitCylinder B H).h₁

/-- 図式側の辺は元の指定変換の関手辺そのもの。 -/
lemma coherentColimitUnitSquare_source :
    prismEndpoint 0 Δ[1] ≫ coherentColimitUnitSquare B H = curry H.h := by
  apply uncurry_injective
  rw [uncurry_natural_left, coherentColimitUnitSquare, uncurry_curry, uncurry_curry]
  have he : (_ ◁ prismEndpoint 0 Δ[1]) ≫
      (α_ ((SSet.uliftFunctor.{u + 1, u}).obj B) Δ[1] Δ[1]).inv =
        SSet.ι₀ ▷ Δ[1] := rfl
  rw [← Category.assoc, he, coherentColimitUnitCylinder_source]

/-- 頂点側の辺は、余極限関手の元の指定辺を定値図式として読んだ全円柱。 -/
lemma coherentColimitUnitSquare_target :
    prismEndpoint 1 Δ[1] ≫ coherentColimitUnitSquare B H =
      curry (snd ((SSet.uliftFunctor.{u + 1, u}).obj B) Δ[1] ≫
        SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B H).edge) := by
  apply uncurry_injective
  rw [uncurry_natural_left, coherentColimitUnitSquare, uncurry_curry, uncurry_curry]
  have he : (_ ◁ prismEndpoint 1 Δ[1]) ≫
      (α_ ((SSet.uliftFunctor.{u + 1, u}).obj B) Δ[1] Δ[1]).inv =
        SSet.ι₁ ▷ Δ[1] := rfl
  rw [← Category.assoc, he, coherentColimitUnitCylinder_target]

end SerrePositivity.InfinityCategories.F2
