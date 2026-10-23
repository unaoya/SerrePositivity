module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitPointedFaceOriginal
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitPointedUniversalLift
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionUniversalInitial
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedPrismFamilyComparison

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

/-- 固定始点を持つ元の二面を、全選択パラメータと同じ全初期値を持つ族にする。 -/
def coherentColimitUnitPointedFixedFaceFamily :
    PointedTransportPrismFamily (K := P) (scaffoldFirstVertex 2)
      (leftUnstraighteningProjection F) where
  diagram := fst (Δ[2] ⊗ (SSet.uliftFunctor.{u + 1, u}).obj B) P ≫
    functorSimplexDiagram S.diagram
  boundary := fst (Δ[0] ⊗ leftUnstraightening F) P ≫ leftUnstraighteningSimplexStart F
  projection := by
    rw [Category.assoc, leftUnstraighteningSimplexStart_projection F 2 _ h₀]
    apply SSet.hom_ext
    intro n
    rfl

/-- 元の全三単体の普遍持ち上げを、固定始点を持つ同じ二面へ実際に制限する。 -/
def coherentColimitUnitPointedFixedFaceLift :=
  ((stdSimplex.δ j ▷ leftUnstraightening F) ▷ P) ≫
    coherentColimitUnitPointedTetrahedronUniversalLift B T k

/-- 全選択を保持した実二面は、同じ元の全初期値を保つ。 -/
lemma coherentColimitUnitPointedFixedFaceLift_boundary :
    ((scaffoldFirstVertex 2 ▷ leftUnstraightening F) ▷ P) ≫
      coherentColimitUnitPointedFixedFaceLift B T k j =
        (coherentColimitUnitPointedFixedFaceFamily B T k j hj S hS).boundary := by
  rw [coherentColimitUnitPointedFixedFaceLift, ← Category.assoc, ← comp_whiskerRight,
    tetrahedronFace_initial_prism _ j hj, Category.id_comp]
  exact relativeExtensionUniversal_initial _ _ _ _ _

include hS in
/-- 全選択を保持した実二面は、元の指定三角形の同じ全底を被覆する。 -/
lemma coherentColimitUnitPointedFixedFaceLift_projection :
    coherentColimitUnitPointedFixedFaceLift B T k j ≫ pointedSpaceProjection =
      ((Δ[2] ◁ leftUnstraighteningProjection F) ▷ P) ≫
        (coherentColimitUnitPointedFixedFaceFamily B T k j hj S hS).diagram := by
  rw [coherentColimitUnitPointedFixedFaceLift, Category.assoc,
    coherentColimitUnitPointedTetrahedronUniversalLift_projection]
  change _ = _ ≫ fst _ _ ≫ functorSimplexDiagram S.diagram
  rw [← coherentColimitUnitPointedTetrahedronDiagram_face B T k j S.diagram hS]
  apply SSet.hom_ext
  intro n
  rfl

end SerrePositivity.InfinityCategories.F2
