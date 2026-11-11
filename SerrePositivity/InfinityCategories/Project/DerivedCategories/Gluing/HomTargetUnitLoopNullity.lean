module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitTriangleFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitLoopEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.TerminalUnitLoopEdgeRecovery
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.TerminalUnitLoopClass
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitTetrahedronLoopDiagonal
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NormalizationSourceTetrahedron
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
概要：元四面体の二単位退化から同じ実単位閉路の零性を得る。
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

lemma dgGluingHomTargetUnitProjectionTetrahedron_source_faces :
    (stdSimplex.δ (1 : Fin 4) ▷ P) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 0 =
    (stdSimplex.δ (0 : Fin 4) ▷ P) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationSourceTetrahedron_one_eq_zero.{u, max (u + 1) v}
    R E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaObject R C D E p q X)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaObject R C D E p q Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y)

lemma dgGluingHomTargetRightUnitLoop_projection_face :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightUnitLoop R C D E p q X Y).h =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTerminalUnitConeFamily P ≫ (stdSimplex.δ (1 : Fin 4) ▷ P) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 1 := by
  simpa only [id_whiskerRight, whiskerLeft_id, Category.id_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitProjectionTetrahedron, Category.assoc] using
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightUnitLoop_tetrahedron_face R C D E p q X Y

lemma dgGluingHomTargetLeftUnitLoop_projection_face :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftUnitLoop R C D E p q X Y).h =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitConeFamily P ≫ (stdSimplex.δ (2 : Fin 4) ▷ P) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 0 := by
  simpa only [id_whiskerRight, whiskerLeft_id, Category.id_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitProjectionTetrahedron, Category.assoc] using
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftUnitLoop_tetrahedron_face R C D E p q X Y

lemma dgGluingHomTargetUnitProjectionTetrahedron_target_standard_unit_face :
    (stdSimplex.δ (1 : Fin 4) ▷ P) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 1 =
      (stdSimplex.σ (1 : Fin 2) ▷ P) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetStandardFirstInputLift R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)) := by
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightUnitLoop R C D E p q X Y).h =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTerminalUnitConeFamily P ≫ (stdSimplex.σ (1 : Fin 2) ▷ P) ≫
        (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ (stdSimplex.δ (1 : Fin 4) ▷ P) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 1 := by
    rw [dgGluingHomTargetRightUnitLoop_projection_face R C D E p q X Y]
    exact congrArg (fun m => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTerminalUnitConeFamily P ≫ m)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitProjectionTetrahedron_target_unit_face R C D E p q X Y)
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTerminalUnitLoop_edge_recovery
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetStandardFirstInputLift R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputDiagonal R C D E p q X Y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightUnitLoop R C D E p q X Y)
    ((stdSimplex.δ (2 : Fin 3) ▷ P) ≫ (stdSimplex.δ (1 : Fin 4) ▷ P) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 1) hr
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitProjectionTetrahedron_target_unit_face R C D E p q X Y).trans
    (congrArg (fun m => (stdSimplex.σ (1 : Fin 2) ▷ P) ≫ m) he)

lemma dgGluingHomTargetRightUnitLoop_class_of_unit_face
    (hR : (stdSimplex.δ (1 : Fin 4) ▷ P) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 1 =
      (stdSimplex.σ (1 : Fin 2) ▷ P) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetStandardFirstInputLift R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputDiagonal R C D E p q X Y))) :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightUnitLoop R C D E p q X Y)) = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTerminalUnitLoop_homMk_id
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetStandardFirstInputLift R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputDiagonal R C D E p q X Y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightUnitLoop R C D E p q X Y)
  rw [dgGluingHomTargetRightUnitLoop_projection_face R C D E p q X Y, hR]

lemma dgGluingHomTargetLeftUnitLoop_class_of_unit_face
    (hL : (stdSimplex.δ (3 : Fin 4) ▷ P) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 0 =
      (stdSimplex.σ (0 : Fin 2) ▷ P) ≫ (stdSimplex.δ (2 : Fin 3) ▷ P) ≫
        (stdSimplex.δ (0 : Fin 4) ▷ P) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 0) :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftUnitLoop R C D E p q X Y)) = 𝟙 _ := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitTetrahedronLoop_homMk_id_of_three_faces
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetStandardLastInputLift R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputDiagonal R C D E p q X Y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftUnitLoop R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 0)
    ((stdSimplex.δ (0 : Fin 4) ▷ P) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 0)
    rfl (dgGluingHomTargetUnitProjectionTetrahedron_source_faces R C D E p q X Y) hL
    (dgGluingHomTargetLeftUnitLoop_projection_face R C D E p q X Y).symm

lemma dgGluingHomTargetRightUnitLoop_class :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightUnitLoop R C D E p q X Y)) = 𝟙 _ :=
  dgGluingHomTargetRightUnitLoop_class_of_unit_face R C D E p q X Y
    (dgGluingHomTargetUnitProjectionTetrahedron_target_standard_unit_face R C D E p q X Y)

lemma dgGluingHomTargetLeftUnitLoop_class :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftUnitLoop R C D E p q X Y)) = 𝟙 _ :=
  dgGluingHomTargetLeftUnitLoop_class_of_unit_face R C D E p q X Y
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitProjectionTetrahedron_source_unit_face R C D E p q X Y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
