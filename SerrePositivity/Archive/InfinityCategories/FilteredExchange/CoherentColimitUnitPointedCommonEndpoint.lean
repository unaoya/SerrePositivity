module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitPointedFixedFaceTerminal
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitZeroFaceEndpoint

/-!
概要：元の第零面と固定始点の二面の実終点を、同じ全三単体の最終頂点へ同定する。
方針：元の全 pointed 終点と底の射影の厳密な一致で引き戻しの二射影を比較する。
規約：全選択・元の実終点を保持。使われ方：三単体の三関係の共通終点の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J Q₀ Q₁ Q₂ R₁ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (j : Fin 4) (hj : j ≠ 0)
  {a : SSet.Homotopy F Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy F Q₂}
  (S : FunctorCompositionTriangle a b c)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ j
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)
  (H : SSet.Homotopy F Q₀)
  (he : (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫
    SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T k) = curry H.h)
  {x : SSet.Homotopy Q₀ R₁} {y : SSet.Homotopy R₁ Q₂} {z : SSet.Homotopy Q₀ Q₂}
  (U : FunctorCompositionTriangle x y z)
  (hU : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 0
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv U.diagram)

/-- 元の第零面と最終頂点を含む固定面の実終点は、全選択上で厳密に同じ射。 -/
lemma coherentColimitUnitPointedFixedFaceEndpoint_eq_zeroFace (hLast : j ≠ 3) :
    coherentColimitUnitPointedFixedFaceEndpoint B T k j hj S hS =
      coherentColimitUnitZeroFaceEndpoint B T k H he U hU :=
  coherentColimitUnitPointedFixedFaceEndpoint_eq_of_tetrahedron B T k j hj S hS hLast
    (coherentColimitUnitZeroFaceEndpoint B T k H he U hU)
    (coherentColimitUnitZeroFaceEndpoint_projection B T k H he U hU)
    (coherentColimitUnitZeroFaceEndpoint_pointed_tetrahedron B T k H he U hU)

end SerrePositivity.InfinityCategories.F2
