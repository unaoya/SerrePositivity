module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitPointedFixedFaceEndpoint

/-!
概要：固定始点を持つ元の二面と、元の指定三角形の実持ち上げを比較する。
方針：同じ全初期値の選択空間へ元の二頂点を入れ、長辺へ制限する。
規約：同じ全空間と同じ始点を保持。使われ方：共有面の指定比較を同じ空間で消去。
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
  {F G J Q₁ Q₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (j : Fin 4) (hj : j ≠ 0)
  {a : SSet.Homotopy F Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy F Q₂}
  (S : FunctorCompositionTriangle a b c)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ j
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)
local notation "P" => coherentColimitUnitPointedTetrahedronChoice B T k
local notation "h₀" => coherentColimitUnitPointedFace_initial B T k j hj S.diagram hS

/-- 最終頂点を含む三つの二面の終点は、元の全三単体の同じ最終頂点。 -/
lemma tetrahedronFace_terminal (A : SSet.{u + 1}) (i : Fin 4) (hi : i ≠ 3) :
    simplexPrismVertex 2 2 A ≫ (stdSimplex.δ i ▷ A) = simplexPrismVertex 3 3 A := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact (hi rfl).elim

/-- 元の固定面の実終点は、全選択を通じて全三単体の同じ最終頂点。 -/
lemma coherentColimitUnitPointedFixedFaceEndpoint_pointed_tetrahedron (hLast : j ≠ 3) :
    (simplexPrismVertex 3 3 (leftUnstraightening F) ▷ P) ≫
      coherentColimitUnitPointedTetrahedronUniversalLift B T k =
      coherentColimitUnitPointedFixedFaceEndpoint B T k j hj S hS ≫
        pullback.fst pointedSpaceProjection Q₂ := by
  rw [← tetrahedronFace_terminal (leftUnstraightening F) j hLast,
    comp_whiskerRight, Category.assoc]
  exact coherentColimitUnitPointedFixedFaceEndpoint_pointed B T k j hj S hS

/-- 同じ底と元の全三単体の最終頂点を持つ実終点は、元の固定面の終点に厳密に等しい。 -/
lemma coherentColimitUnitPointedFixedFaceEndpoint_eq_of_tetrahedron (hLast : j ≠ 3)
    (g : leftUnstraightening F ⊗ P ⟶ leftUnstraightening Q₂)
    (hg : g ≫ leftUnstraighteningProjection Q₂ =
      fst (leftUnstraightening F) P ≫ leftUnstraighteningProjection F)
    (hp : (simplexPrismVertex 3 3 (leftUnstraightening F) ▷ P) ≫
      coherentColimitUnitPointedTetrahedronUniversalLift B T k =
      g ≫ pullback.fst pointedSpaceProjection Q₂) :
    coherentColimitUnitPointedFixedFaceEndpoint B T k j hj S hS = g := by
  apply pullback.hom_ext
  · exact (coherentColimitUnitPointedFixedFaceEndpoint_pointed_tetrahedron
      B T k j hj S hS hLast).symm.trans hp
  · exact (coherentColimitUnitPointedFixedFaceEndpoint_projection B T k j hj S hS).trans hg.symm

end SerrePositivity.InfinityCategories.F2
