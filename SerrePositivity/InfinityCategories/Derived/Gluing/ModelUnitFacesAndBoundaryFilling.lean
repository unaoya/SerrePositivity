module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModelSourceUnitNullity
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModelTargetUnitFace
public import SerrePositivity.InfinityCategories.Derived.Gluing.TerminalUnitLoopEdgeRecovery
/-!
概要：二つの実射影単位面を無条件に接続し、正本の指定対角境界を充填する。
方針：第二単位退化の基底辺は元実閉路の端点から回収し、第一単位は相対内角比較へ移す。
規約：全六片・元 Hom 入力・指定三辺を保持し、単位面の補助仮定を追加しない。
使われ方：G-1 d ③・④から正本比較の実ホモトピー逆の構成へ進む。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "K" => dgGluingModelUnitCollarParameter R C D M X Y

lemma dgGluingModelUnitProjectionTetrahedron_target_standard_unit_face :
    (stdSimplex.δ (1 : Fin 4) ▷ K) ≫
      dgGluingModelUnitProjectionTetrahedron R C D M X Y 1 =
      (stdSimplex.σ (1 : Fin 2) ▷ K) ≫
        intervalMappingUncurry (dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y) := by
  have hr : intervalMappingUncurry (dgGluingModelRightUnitLoop R C D M X Y).h =
      dgGluingTerminalUnitConeFamily K ≫ (stdSimplex.σ (1 : Fin 2) ▷ K) ≫
        (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ (stdSimplex.δ (1 : Fin 4) ▷ K) ≫
          dgGluingModelUnitProjectionTetrahedron R C D M X Y 1 := by
    rw [dgGluingModelRightUnitLoop_model_tetrahedron_face R C D M X Y]
    exact congrArg (fun m => dgGluingTerminalUnitConeFamily K ≫ m)
      (dgGluingModelUnitProjectionTetrahedron_target_unit_face R C D M X Y)
  have he := dgGluingTerminalUnitLoop_edge_recovery
    (dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y)
    (dgGluingModelRightUnitLoop R C D M X Y)
    ((stdSimplex.δ (2 : Fin 3) ▷ K) ≫ (stdSimplex.δ (1 : Fin 4) ▷ K) ≫
      dgGluingModelUnitProjectionTetrahedron R C D M X Y 1) hr
  exact (dgGluingModelUnitProjectionTetrahedron_target_unit_face R C D M X Y).trans
    (congrArg (fun m => (stdSimplex.σ (1 : Fin 2) ▷ K) ≫ m) he)

lemma dgGluingModelRightUnitLoop_class :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgGluingModelRightUnitLoop R C D M X Y)) = 𝟙 _ :=
  dgGluingModelRightUnitLoop_class_of_unit_face R C D M X Y
    (dgGluingModelUnitProjectionTetrahedron_target_standard_unit_face R C D M X Y)

lemma dgGluingLaxHomDiagonalComparisonBoundary_filling :
    ∃ V, (boundary 2).ι ≫ V = dgGluingLaxHomDiagonalComparisonBoundary R C D M X Y :=
  dgGluingLaxHomDiagonalComparisonBoundary_filling_of_target_unit_face R C D M X Y
    (dgGluingModelUnitProjectionTetrahedron_target_standard_unit_face R C D M X Y)
end SerrePositivity.InfinityCategories
