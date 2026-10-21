module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitZeroFaceOriginalTriangle

/-!
概要：第一辺で前合成した元の指定三角形を、同じ第零面の可変初期値の延長空間へ束ねる。
方針：元の底と射影の厳密な式で同じ全族の切断を作る。
規約：元の指定三角形の持ち上げを保持。使われ方：第零面の指定比較の同じ空間での照合。
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
  {F G J Q₀ Q₁ Q₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (H : SSet.Homotopy F Q₀)
  (he : (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫
    SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T k) = curry H.h)
  {a : SSet.Homotopy Q₀ Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy Q₀ Q₂}
  (S : FunctorCompositionTriangle a b c)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 0
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)

include hS in
/-- 元の指定三角形を実第一辺で前合成しても、元の第零面の同じ全底を被覆する。 -/
lemma coherentColimitUnitZeroFaceOriginalTriangleLift_projection :
    coherentColimitUnitZeroFaceOriginalTriangleLift B T k H he S ≫ pointedSpaceProjection =
      ((Δ[2] ◁ leftUnstraighteningProjection F) ▷
        coherentColimitUnitPointedTetrahedronChoice B T k) ≫
          (coherentColimitUnitPointedZeroFaceFamily B T k).diagram := by
  have hd : (coherentColimitUnitPointedZeroFaceFamily B T k).diagram =
      fst (Δ[2] ⊗ (SSet.uliftFunctor.{u + 1, u}).obj B)
        (coherentColimitUnitPointedTetrahedronChoice B T k) ≫
          functorSimplexDiagram S.diagram := by
    change _ ≫ functorSimplexDiagram _ = _
    rw [hS, Equiv.symm_apply_apply]
  rw [coherentColimitUnitZeroFaceOriginalTriangleLift, Category.assoc, Category.assoc,
    functorTrianglePointedLift_projection, hd]
  rw [← Category.assoc (Δ[2] ◁ coherentColimitUnitPointedFirstEdgeEndpoint B T k H he),
    ← whiskerLeft_comp, coherentColimitUnitPointedFirstEdgeEndpoint_projection]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 元の指定比較に使った全三角形も、元の第零面と同じ全延長空間の実際の切断となる。 -/
def coherentColimitUnitZeroFaceOriginalSection :=
  pointedPrismFamilySection (coherentColimitUnitPointedZeroFaceFamily B T k)
    (coherentColimitUnitZeroFaceOriginalTriangleLift B T k H he S)
    (coherentColimitUnitZeroFaceOriginalTriangleLift_boundary B T k H he S)
    (coherentColimitUnitZeroFaceOriginalTriangleLift_projection B T k H he S hS)

/-- 元の指定三角形の切断も、元の全三単体の全選択を厳密に保持する。 -/
lemma coherentColimitUnitZeroFaceOriginalSection_projection :
    coherentColimitUnitZeroFaceOriginalSection B T k H he S hS ≫
      (coherentColimitUnitPointedZeroFaceFamily B T k).liftSpaceProjection = 𝟙 _ :=
  pointedPrismFamilySection_projection _ _ _ _

end SerrePositivity.InfinityCategories.F2
