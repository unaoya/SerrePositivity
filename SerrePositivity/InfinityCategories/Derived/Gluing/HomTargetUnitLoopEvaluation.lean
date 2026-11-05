module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitTriangleFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitSixTriangleDiagram
public import SerrePositivity.InfinityCategories.Derived.Gluing.FunctorEdgeHomotopyRecovery
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitCapUnitLoopDomains
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitCapCoefficientFace
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitSpanTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitSpanRelativeComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetDiagonalComparisonBoundary
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitTriangleDiagrams
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitCapIntervalTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitCollarIntervalTriangle
/-!
概要：六片の実単位閉路を元四面体の両射影面へ厳密に回収する。
方針：元の全入力・指定面・全区間族を保持する比較を合成する。
規約：追加の主経路仮定を置かない。使われ方：元 lax Hom 比較の逆の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetRightUnitLoop : SSet.Homotopy
    ((dgGluingHomTargetStandardFirstInputLift R C D E p q X Y ≫
      dgGluingHomTargetFirstInputDiagonal R C D E p q X Y))
    ((dgGluingHomTargetStandardFirstInputLift R C D E p q X Y ≫
      dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)) :=
  simplicialHomotopyOfFunctorEdge ((dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 0 0)

def dgGluingHomTargetLeftUnitLoop : SSet.Homotopy
    ((dgGluingHomTargetStandardLastInputLift R C D E p q X Y ≫
      dgGluingHomTargetLastInputDiagonal R C D E p q X Y))
    ((dgGluingHomTargetStandardLastInputLift R C D E p q X Y ≫
      dgGluingHomTargetLastInputDiagonal R C D E p q X Y)) :=
  simplicialHomotopyOfFunctorEdge ((dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 2 2)

lemma dgGluingHomTargetRightUnitLoop_edge :
    functorEdgeOfSimplicialHomotopy (dgGluingHomTargetRightUnitLoop R C D E p q X Y) =
      (dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 0 0 :=
  dgGluingFunctorEdge_homotopy_recovery _

lemma dgGluingHomTargetLeftUnitLoop_edge :
    functorEdgeOfSimplicialHomotopy (dgGluingHomTargetLeftUnitLoop R C D E p q X Y) =
      (dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 2 2 :=
  dgGluingFunctorEdge_homotopy_recovery _
lemma dgGluingHomTargetRightUnitLoop_h :
    (dgGluingHomTargetRightUnitLoop R C D E p q X Y).h =
      ((𝟙 P) ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
        (β_ P (Δ[1] : SSet.{max (u + 1) v})).hom ≫
          (stdSimplex.δ (0 : Fin 3) ▷ P) ≫
            dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 0 := by
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv
    (stdSimplex.δ (0 : Fin 3) ≫ dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 0))) = _
  rw [Equiv.symm_apply_apply, dgGluingHomTargetUnitCapTriangleDiagram,
    dgGluingTriangleDiagramTransport_face, uncurry_curry]

lemma dgGluingHomTargetLeftUnitLoop_h :
    (dgGluingHomTargetLeftUnitLoop R C D E p q X Y).h =
      ((𝟙 P) ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
        (β_ P (Δ[1] : SSet.{max (u + 1) v})).hom ≫
          (stdSimplex.δ (2 : Fin 3) ▷ P) ≫
            dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 2 := by
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv
    (stdSimplex.δ (2 : Fin 3) ≫ dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 2))) = _
  rw [Equiv.symm_apply_apply, dgGluingHomTargetUnitCapTriangleDiagram,
    dgGluingTriangleDiagramTransport_face, uncurry_curry]
lemma dgGluingHomTargetRightUnitLoop_evaluate :
    intervalMappingUncurry (dgGluingHomTargetRightUnitLoop R C D E p q X Y).h =
      ((Δ[1] : SSet.{max (u + 1) v}) ◁ ((𝟙 P) ▷ (Δ[1] : SSet.{max (u + 1) v}))) ≫
        ((Δ[1] : SSet.{max (u + 1) v}) ◁ (β_ P (Δ[1] : SSet.{max (u + 1) v})).hom) ≫ ((Δ[1] : SSet.{max (u + 1) v}) ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
          dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 0 := by
  rw [dgGluingHomTargetRightUnitLoop_h R C D E p q X Y]
  simp only [intervalMappingUncurry_precomp, dgGluingHomTargetUnitCapIntervalTriangle_evaluate]

lemma dgGluingHomTargetLeftUnitLoop_evaluate :
    intervalMappingUncurry (dgGluingHomTargetLeftUnitLoop R C D E p q X Y).h =
      ((Δ[1] : SSet.{max (u + 1) v}) ◁ ((𝟙 P) ▷ (Δ[1] : SSet.{max (u + 1) v}))) ≫
        ((Δ[1] : SSet.{max (u + 1) v}) ◁ (β_ P (Δ[1] : SSet.{max (u + 1) v})).hom) ≫ ((Δ[1] : SSet.{max (u + 1) v}) ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
          dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 2 := by
  rw [dgGluingHomTargetLeftUnitLoop_h R C D E p q X Y]
  simp only [intervalMappingUncurry_precomp, dgGluingHomTargetUnitCapIntervalTriangle_evaluate]

lemma dgGluingHomTargetRightUnitLoop_tetrahedron_face :
    intervalMappingUncurry (dgGluingHomTargetRightUnitLoop R C D E p q X Y).h =
      ((Δ[1] : SSet.{max (u + 1) v}) ◁ ((𝟙 P) ▷ (Δ[1] : SSet.{max (u + 1) v}))) ≫
        dgGluingTerminalUnitConeFamily P ≫ (stdSimplex.δ (1 : Fin 4) ▷ P) ≫
          prismEndpoint 1 (Δ[3] ⊗ P) ≫
            dgGluingHomTargetAugmentationTetrahedron R C D E p q X Y := by
  rw [dgGluingHomTargetRightUnitLoop_evaluate R C D E p q X Y,
    dgGluingHomTargetUnitCapPastingTriangleFamily,
    reassoc_of% dgGluingUnitCapPastingDomain_first_unit P]

lemma dgGluingHomTargetLeftUnitLoop_tetrahedron_face :
    intervalMappingUncurry (dgGluingHomTargetLeftUnitLoop R C D E p q X Y).h =
      ((Δ[1] : SSet.{max (u + 1) v}) ◁ ((𝟙 P) ▷ (Δ[1] : SSet.{max (u + 1) v}))) ≫
        dgGluingInitialUnitConeFamily P ≫ (stdSimplex.δ (2 : Fin 4) ▷ P) ≫
          prismEndpoint 0 (Δ[3] ⊗ P) ≫
            dgGluingHomTargetAugmentationTetrahedron R C D E p q X Y := by
  rw [dgGluingHomTargetLeftUnitLoop_evaluate R C D E p q X Y,
    dgGluingHomTargetUnitCapPastingTriangleFamily,
    reassoc_of% dgGluingUnitCapPastingDomain_last_unit P]

end SerrePositivity.InfinityCategories
