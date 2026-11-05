module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitTriangleFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitLoopEvaluation
public import SerrePositivity.InfinityCategories.Derived.Gluing.TerminalUnitLoopEdgeRecovery
public import SerrePositivity.InfinityCategories.Derived.Gluing.TerminalUnitLoopClass
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitTetrahedronLoopDiagonal
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationSourceTetrahedron
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
概要：元四面体の二単位退化から同じ実単位閉路の零性を得る。
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

lemma dgGluingHomTargetUnitProjectionTetrahedron_source_faces :
    (stdSimplex.δ (1 : Fin 4) ▷ P) ≫
      dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 0 =
    (stdSimplex.δ (0 : Fin 4) ▷ P) ≫
      dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 0 :=
  dgGluingNormalizationSourceTetrahedron_one_eq_zero.{u, max (u + 1) v}
    R E (dgGluingHomTargetIdentityCommaObject R C D E p q X)
    (dgGluingHomTargetIdentityCommaObject R C D E p q Y)
    (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)

lemma dgGluingHomTargetRightUnitLoop_projection_face :
    intervalMappingUncurry (dgGluingHomTargetRightUnitLoop R C D E p q X Y).h =
    dgGluingTerminalUnitConeFamily P ≫ (stdSimplex.δ (1 : Fin 4) ▷ P) ≫
      dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 1 := by
  simpa only [id_whiskerRight, whiskerLeft_id, Category.id_comp,
    dgGluingHomTargetUnitProjectionTetrahedron, Category.assoc] using
      dgGluingHomTargetRightUnitLoop_tetrahedron_face R C D E p q X Y

lemma dgGluingHomTargetLeftUnitLoop_projection_face :
    intervalMappingUncurry (dgGluingHomTargetLeftUnitLoop R C D E p q X Y).h =
    dgGluingInitialUnitConeFamily P ≫ (stdSimplex.δ (2 : Fin 4) ▷ P) ≫
      dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 0 := by
  simpa only [id_whiskerRight, whiskerLeft_id, Category.id_comp,
    dgGluingHomTargetUnitProjectionTetrahedron, Category.assoc] using
      dgGluingHomTargetLeftUnitLoop_tetrahedron_face R C D E p q X Y

lemma dgGluingHomTargetUnitProjectionTetrahedron_target_standard_unit_face :
    (stdSimplex.δ (1 : Fin 4) ▷ P) ≫
      dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 1 =
      (stdSimplex.σ (1 : Fin 2) ▷ P) ≫
        intervalMappingUncurry ((dgGluingHomTargetStandardFirstInputLift R C D E p q X Y ≫
      dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)) := by
  have hr : intervalMappingUncurry (dgGluingHomTargetRightUnitLoop R C D E p q X Y).h =
      dgGluingTerminalUnitConeFamily P ≫ (stdSimplex.σ (1 : Fin 2) ▷ P) ≫
        (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ (stdSimplex.δ (1 : Fin 4) ▷ P) ≫
          dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 1 := by
    rw [dgGluingHomTargetRightUnitLoop_projection_face R C D E p q X Y]
    exact congrArg (fun m => dgGluingTerminalUnitConeFamily P ≫ m)
      (dgGluingHomTargetUnitProjectionTetrahedron_target_unit_face R C D E p q X Y)
  have he := dgGluingTerminalUnitLoop_edge_recovery
    ((dgGluingHomTargetStandardFirstInputLift R C D E p q X Y ≫
      dgGluingHomTargetFirstInputDiagonal R C D E p q X Y))
    (dgGluingHomTargetRightUnitLoop R C D E p q X Y)
    ((stdSimplex.δ (2 : Fin 3) ▷ P) ≫ (stdSimplex.δ (1 : Fin 4) ▷ P) ≫
      dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 1) hr
  exact (dgGluingHomTargetUnitProjectionTetrahedron_target_unit_face R C D E p q X Y).trans
    (congrArg (fun m => (stdSimplex.σ (1 : Fin 2) ▷ P) ≫ m) he)

lemma dgGluingHomTargetRightUnitLoop_class_of_unit_face
    (hR : (stdSimplex.δ (1 : Fin 4) ▷ P) ≫
      dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 1 =
      (stdSimplex.σ (1 : Fin 2) ▷ P) ≫
        intervalMappingUncurry ((dgGluingHomTargetStandardFirstInputLift R C D E p q X Y ≫
      dgGluingHomTargetFirstInputDiagonal R C D E p q X Y))) :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgGluingHomTargetRightUnitLoop R C D E p q X Y)) = 𝟙 _ := by
  apply dgGluingTerminalUnitLoop_homMk_id
    ((dgGluingHomTargetStandardFirstInputLift R C D E p q X Y ≫
      dgGluingHomTargetFirstInputDiagonal R C D E p q X Y))
    (dgGluingHomTargetRightUnitLoop R C D E p q X Y)
  rw [dgGluingHomTargetRightUnitLoop_projection_face R C D E p q X Y, hR]

lemma dgGluingHomTargetLeftUnitLoop_class_of_unit_face
    (hL : (stdSimplex.δ (3 : Fin 4) ▷ P) ≫
      dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 0 =
      (stdSimplex.σ (0 : Fin 2) ▷ P) ≫ (stdSimplex.δ (2 : Fin 3) ▷ P) ≫
        (stdSimplex.δ (0 : Fin 4) ▷ P) ≫
          dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 0) :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgGluingHomTargetLeftUnitLoop R C D E p q X Y)) = 𝟙 _ := by
  exact dgGluingUnitTetrahedronLoop_homMk_id_of_three_faces
    ((dgGluingHomTargetStandardLastInputLift R C D E p q X Y ≫
      dgGluingHomTargetLastInputDiagonal R C D E p q X Y))
    (dgGluingHomTargetLeftUnitLoop R C D E p q X Y)
    (dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 0)
    ((stdSimplex.δ (0 : Fin 4) ▷ P) ≫
      dgGluingHomTargetUnitProjectionTetrahedron R C D E p q X Y 0)
    rfl (dgGluingHomTargetUnitProjectionTetrahedron_source_faces R C D E p q X Y) hL
    (dgGluingHomTargetLeftUnitLoop_projection_face R C D E p q X Y).symm

lemma dgGluingHomTargetRightUnitLoop_class :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgGluingHomTargetRightUnitLoop R C D E p q X Y)) = 𝟙 _ :=
  dgGluingHomTargetRightUnitLoop_class_of_unit_face R C D E p q X Y
    (dgGluingHomTargetUnitProjectionTetrahedron_target_standard_unit_face R C D E p q X Y)

lemma dgGluingHomTargetLeftUnitLoop_class :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgGluingHomTargetLeftUnitLoop R C D E p q X Y)) = 𝟙 _ :=
  dgGluingHomTargetLeftUnitLoop_class_of_unit_face R C D E p q X Y
    (dgGluingHomTargetUnitProjectionTetrahedron_source_unit_face R C D E p q X Y)

end SerrePositivity.InfinityCategories
