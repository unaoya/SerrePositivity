module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModelSourceTetrahedronFaceAgreement
public import SerrePositivity.InfinityCategories.Derived.Gluing.TerminalUnitLoopClass
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitTetrahedronLoopDiagonal
/-! # 二つの射影単位退化から正本の指定対角境界を充填する

概要：元四面体の二射影面の単位退化だけから、実二閉路の零性と指定境界充填を得る。
方針：右閉路には厳密退化、左閉路には同じ内角を固定した相対四面体比較を適用する。
規約：D に依頼中の二面だけを補助入力に残し、元四面体・全入力・主比較の公開型を保持する。
使われ方：D の二つの厳密単位則を接続すれば③・④を無仮定で閉じる。
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

lemma dgGluingModelRightUnitLoop_class_of_unit_face
    (hR : (stdSimplex.δ (1 : Fin 4) ▷ K) ≫
      dgGluingModelUnitProjectionTetrahedron R C D M X Y 1 =
      (stdSimplex.σ (1 : Fin 2) ▷ K) ≫
        intervalMappingUncurry (dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y)) :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgGluingModelRightUnitLoop R C D M X Y)) = 𝟙 _ := by
  apply dgGluingTerminalUnitLoop_homMk_id
    (dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y)
    (dgGluingModelRightUnitLoop R C D M X Y)
  rw [dgGluingModelRightUnitLoop_model_tetrahedron_face R C D M X Y, hR]
  rfl

lemma dgGluingModelLeftUnitLoop_class_of_unit_face
    (hL : (stdSimplex.δ (3 : Fin 4) ▷ K) ≫
      dgGluingModelUnitProjectionTetrahedron R C D M X Y 0 =
      (stdSimplex.σ (0 : Fin 2) ▷ K) ≫ (stdSimplex.δ (2 : Fin 3) ▷ K) ≫
        (stdSimplex.δ (0 : Fin 4) ▷ K) ≫
          dgGluingModelUnitProjectionTetrahedron R C D M X Y 0) :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgGluingModelLeftUnitLoop R C D M X Y)) = 𝟙 _ := by
  exact dgGluingUnitTetrahedronLoop_homMk_id_of_three_faces
    (dgGluingHomDerivedLastCompositionDiagonal R C D M X Y)
    (dgGluingModelLeftUnitLoop R C D M X Y)
    (dgGluingModelUnitProjectionTetrahedron R C D M X Y 0)
    ((stdSimplex.δ (0 : Fin 4) ▷ K) ≫
      dgGluingModelUnitProjectionTetrahedron R C D M X Y 0)
    rfl (dgGluingModelUnitProjectionTetrahedron_source_faces R C D M X Y) hL
    (dgGluingModelLeftUnitLoop_model_tetrahedron_face R C D M X Y).symm

lemma dgGluingLaxHomDiagonalComparisonBoundary_filling_of_projection_unit_faces
    (hR : (stdSimplex.δ (1 : Fin 4) ▷ K) ≫
      dgGluingModelUnitProjectionTetrahedron R C D M X Y 1 =
      (stdSimplex.σ (1 : Fin 2) ▷ K) ≫
        intervalMappingUncurry (dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y))
    (hL : (stdSimplex.δ (3 : Fin 4) ▷ K) ≫
      dgGluingModelUnitProjectionTetrahedron R C D M X Y 0 =
      (stdSimplex.σ (0 : Fin 2) ▷ K) ≫ (stdSimplex.δ (2 : Fin 3) ▷ K) ≫
        (stdSimplex.δ (0 : Fin 4) ▷ K) ≫
          dgGluingModelUnitProjectionTetrahedron R C D M X Y 0) :
    ∃ V, (boundary 2).ι ≫ V = dgGluingLaxHomDiagonalComparisonBoundary R C D M X Y := by
  apply dgGluingLaxHomDiagonalComparisonBoundary_filling_of_model_unit_classes R C D M X Y
  · rw [← dgGluingModelRightUnitLoop_edge R C D M X Y]
    exact dgGluingModelRightUnitLoop_class_of_unit_face R C D M X Y hR
  · rw [← dgGluingModelLeftUnitLoop_edge R C D M X Y]
    exact dgGluingModelLeftUnitLoop_class_of_unit_face R C D M X Y hL
end SerrePositivity.InfinityCategories
