module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitTriangleFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitSixTriangleDiagram
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FunctorEdgeHomotopyRecovery
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitCapUnitLoopDomains
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitCapCoefficientFace
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitSpanTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitSpanRelativeComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetDiagonalComparisonBoundary
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitTriangleDiagrams
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitCapIntervalTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitCollarIntervalTriangle
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetRightUnitLoop : SSet.Homotopy
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetStandardFirstInputLift R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputDiagonal R C D E p q X Y))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetStandardFirstInputLift R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 0 0)

def dgGluingHomTargetLeftUnitLoop : SSet.Homotopy
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetStandardLastInputLift R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputDiagonal R C D E p q X Y))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetStandardLastInputLift R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputDiagonal R C D E p q X Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 2 2)

lemma dgGluingHomTargetRightUnitLoop_edge :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgGluingHomTargetRightUnitLoop R C D E p q X Y) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 0 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorEdge_homotopy_recovery _

lemma dgGluingHomTargetLeftUnitLoop_edge :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgGluingHomTargetLeftUnitLoop R C D E p q X Y) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitSixTriangleDiagram R C D E p q X Y).edge 2 2 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorEdge_homotopy_recovery _
lemma dgGluingHomTargetRightUnitLoop_h :
    (dgGluingHomTargetRightUnitLoop R C D E p q X Y).h =
      ((𝟙 P) ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
        (β_ P (Δ[1] : SSet.{max (u + 1) v})).hom ≫
          (stdSimplex.δ (0 : Fin 3) ▷ P) ≫
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 0 := by
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv
    (stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 0))) = _
  rw [Equiv.symm_apply_apply, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapTriangleDiagram,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleDiagramTransport_face, uncurry_curry]

lemma dgGluingHomTargetLeftUnitLoop_h :
    (dgGluingHomTargetLeftUnitLoop R C D E p q X Y).h =
      ((𝟙 P) ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
        (β_ P (Δ[1] : SSet.{max (u + 1) v})).hom ≫
          (stdSimplex.δ (2 : Fin 3) ▷ P) ≫
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 2 := by
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv
    (stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 2))) = _
  rw [Equiv.symm_apply_apply, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapTriangleDiagram,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleDiagramTransport_face, uncurry_curry]
lemma dgGluingHomTargetRightUnitLoop_evaluate :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgGluingHomTargetRightUnitLoop R C D E p q X Y).h =
      ((Δ[1] : SSet.{max (u + 1) v}) ◁ ((𝟙 P) ▷ (Δ[1] : SSet.{max (u + 1) v}))) ≫
        ((Δ[1] : SSet.{max (u + 1) v}) ◁ (β_ P (Δ[1] : SSet.{max (u + 1) v})).hom) ≫ ((Δ[1] : SSet.{max (u + 1) v}) ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 0 := by
  rw [dgGluingHomTargetRightUnitLoop_h R C D E p q X Y]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapIntervalTriangle_evaluate]

lemma dgGluingHomTargetLeftUnitLoop_evaluate :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgGluingHomTargetLeftUnitLoop R C D E p q X Y).h =
      ((Δ[1] : SSet.{max (u + 1) v}) ◁ ((𝟙 P) ▷ (Δ[1] : SSet.{max (u + 1) v}))) ≫
        ((Δ[1] : SSet.{max (u + 1) v}) ◁ (β_ P (Δ[1] : SSet.{max (u + 1) v})).hom) ≫ ((Δ[1] : SSet.{max (u + 1) v}) ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 2 := by
  rw [dgGluingHomTargetLeftUnitLoop_h R C D E p q X Y]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapIntervalTriangle_evaluate]

lemma dgGluingHomTargetRightUnitLoop_tetrahedron_face :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgGluingHomTargetRightUnitLoop R C D E p q X Y).h =
      ((Δ[1] : SSet.{max (u + 1) v}) ◁ ((𝟙 P) ▷ (Δ[1] : SSet.{max (u + 1) v}))) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTerminalUnitConeFamily P ≫ (stdSimplex.δ (1 : Fin 4) ▷ P) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[3] ⊗ P) ≫
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationTetrahedron R C D E p q X Y := by
  rw [dgGluingHomTargetRightUnitLoop_evaluate R C D E p q X Y,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily,
    reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain_first_unit P]

lemma dgGluingHomTargetLeftUnitLoop_tetrahedron_face :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgGluingHomTargetLeftUnitLoop R C D E p q X Y).h =
      ((Δ[1] : SSet.{max (u + 1) v}) ◁ ((𝟙 P) ▷ (Δ[1] : SSet.{max (u + 1) v}))) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitConeFamily P ≫ (stdSimplex.δ (2 : Fin 4) ▷ P) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[3] ⊗ P) ≫
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationTetrahedron R C D E p q X Y := by
  rw [dgGluingHomTargetLeftUnitLoop_evaluate R C D E p q X Y,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily,
    reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain_last_unit P]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
