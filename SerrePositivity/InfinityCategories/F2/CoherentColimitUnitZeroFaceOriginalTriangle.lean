module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitPointedFirstEdgeWitness
public import SerrePositivity.InfinityCategories.F2.FunctorTrianglePointedLift

/-!
概要：元の指定三角形比較の全 pointed 持ち上げを、実第一辺の終点で前合成する。
方針：元の持ち上げを再利用し、全パラメータで同じ可変初期値を回収する。
規約：指定比較の元の全三角形を保持。使われ方：第零面の指定比較を元の値で照合。
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

/-- 元の指定三角形比較に用いた全持ち上げを、そのまま元の実第一辺で前合成する。 -/
def coherentColimitUnitZeroFaceOriginalTriangleLift :=
  (α_ (Δ[2] : SSet.{u + 1}) (leftUnstraightening F)
    (coherentColimitUnitPointedTetrahedronChoice B T k)).hom ≫
    (Δ[2] ◁ coherentColimitUnitPointedFirstEdgeEndpoint B T k H he) ≫
      functorTrianglePointedLift S

/-- 前合成した元の指定三角形の持ち上げは、第零面の同じ可変初期値を厳密に保持。 -/
lemma coherentColimitUnitZeroFaceOriginalTriangleLift_boundary :
    ((scaffoldFirstVertex 2 ▷ leftUnstraightening F) ▷
      coherentColimitUnitPointedTetrahedronChoice B T k) ≫
      coherentColimitUnitZeroFaceOriginalTriangleLift B T k H he S =
        (coherentColimitUnitPointedZeroFaceFamily B T k).boundary := by
  let K := coherentColimitUnitPointedTetrahedronChoice B T k
  let f := coherentColimitUnitPointedFirstEdgeEndpoint B T k H he
  have hv : (simplexPrismVertex 2 0 (leftUnstraightening F) ▷ K) ≫
      (α_ (Δ[2] : SSet.{u + 1}) (leftUnstraightening F) K).hom ≫ (Δ[2] ◁ f) =
        f ≫ simplexPrismVertex 2 0 (leftUnstraightening Q₀) := by
    apply SSet.hom_ext
    intro n
    rfl
  have hn : ((scaffoldFirstVertex 2 ▷ leftUnstraightening F) ▷ K) ≫
      (α_ (Δ[2] : SSet.{u + 1}) (leftUnstraightening F) K).hom ≫ (Δ[2] ◁ f) =
        (snd (Δ[0] : SSet.{u + 1}) (leftUnstraightening F) ▷ K) ≫
          f ≫ simplexPrismVertex 2 0 (leftUnstraightening Q₀) := by
    rw [scaffoldFirstVertex_whiskerRight, comp_whiskerRight, Category.assoc]
    exact congrArg (fun z =>
      (snd (Δ[0] : SSet.{u + 1}) (leftUnstraightening F) ▷ K) ≫ z) hv
  have h := congrArg (fun z => z ≫ functorTrianglePointedLift S) hn
  simp only [Category.assoc, functorTrianglePointedLift_initial] at h
  exact h.trans (coherentColimitUnitPointedZeroFace_boundary_endpoint B T k H he).symm

end SerrePositivity.InfinityCategories.F2
