module
public import SerrePositivity.KST.SConstruction.RawBoundaryVertices
public import SerrePositivity.KST.SConstruction.AssemblyEdgeFaces
public import SerrePositivity.KST.SConstruction.KZeroObjectPresentation

/-! # 元の対角の辺の類と object S₁ の辺の類
概要：内部 core の辺の対角像の基本亜群の類を、同じ始点の object S₁ の辺へ帰着する。
方針：元の組み立ての三角形の右辺を零列全体の零化で消す。
規約：元の境界商内での等式。使われ方：全ての辺から対象 K 類の生成を導く。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra
open scoped Simplicial

/-- 元の境界商の任意の辺を、基本亜群の基点の自己射として扱う。 -/
def rawBoundaryPath (X : StableModel.{u})
    (e : (boundaryReducedRealization 0 X).right _⦋1⦌) :
    boundaryFundamentalBasepoint X ⟶ boundaryFundamentalBasepoint X :=
  FreeGroupoid.homMk (SSet.Truncated.HomotopyCategory.homMk
    (fundamentalLoopEdge (rawBoundaryLoopSimplex X e)))

/-- 元の object S₁ の辺は同じ core 頂点での元の組み立てで表示される。 -/
lemma objectRawBoundaryEdge_assembly (X : StableModel.{u})
    (d : (coreSConstruction 1 X.carrier) _⦋0⦌) :
    (objectRawBoundaryEdge X d.val).map =
      lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const d) ≫
        diagonalAssembly 1 (iteratedSRealizationDiagram 0 X) ≫
          (iteratedSRealizationCoordinateIso 0 X).hom ≫ boundaryReductionQuotient 0 X := by
  have he : (SSet.yonedaEquiv (X := objectSConstruction X.carrier) (n := ⦋1⦌)).symm d.val ≫
      objectToCoreSRealization X.carrier =
      lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const d) ≫
        diagonalAssembly 1 (iteratedSRealizationDiagram 0 X) :=
    objectToCoreSRealization_simplex X.carrier 1 d.val
  have h := congrArg (fun f => f ≫ (iteratedSRealizationCoordinateIso 0 X).hom ≫
    boundaryReductionQuotient 0 X) he
  simpa only [objectRawBoundaryEdge, objectRawBoundaryComparison, Category.assoc] using h

/-- 元の内部 core の辺の対角像と始点の object の辺を結ぶ、境界商内の乗法三角形。 -/
def rawBoundaryDiagonalTriangle (X : StableModel.{u})
    (e : (coreSConstruction 1 X.carrier) _⦋1⦌) :
    PtSimplex.MulStruct
      (objectRawBoundaryEdge X ((coreSConstruction 1 X.carrier).δ 1 e).val) .const
      (rawBoundaryLoopSimplex X
        (((iteratedSRealizationCoordinateIso 0 X).hom ≫ boundaryReductionQuotient 0 X).app
          (Opposite.op ⦋1⦌) e)) (0 : Fin 1) where
  map := assemblyEdgeTriangle (iteratedSRealizationDiagram 0 X) e ≫
    (iteratedSRealizationCoordinateIso 0 X).hom ≫ boundaryReductionQuotient 0 X
  δ_castSucc_castSucc_map := by
    have hq := (iteratedZeroColumn_boundary_zero 0 X).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const (boundaryReducedRealization 0 X)
        ((iteratedSRealizationDiagram 0 X).obj (Opposite.op ⦋0⦌)))
    exact assemblyEdgeTriangle_face_zero (iteratedSRealizationDiagram 0 X)
      ((iteratedSRealizationCoordinateIso 0 X).hom ≫ boundaryReductionQuotient 0 X)
      (boundaryReducedRealization 0 X).basepoint hq e
  δ_succ_castSucc_map := by
    have h := congrArg (fun f => f ≫ (iteratedSRealizationCoordinateIso 0 X).hom ≫
      boundaryReductionQuotient 0 X) (assemblyEdgeTriangle_face_one
        (iteratedSRealizationDiagram 0 X) e)
    have hy := SSet.yonedaEquiv_symm_comp
      (X := iteratedSRealization 0 X) e
      ((iteratedSRealizationCoordinateIso 0 X).hom ≫ boundaryReductionQuotient 0 X)
    exact (Category.assoc _ _ _).symm.trans (h.trans hy)
  δ_succ_succ_map := by
    have h := congrArg (fun f => f ≫ (iteratedSRealizationCoordinateIso 0 X).hom ≫
      boundaryReductionQuotient 0 X) (assemblyEdgeTriangle_face_two
        (iteratedSRealizationDiagram 0 X) e)
    exact (Category.assoc _ _ _).symm.trans
      (h.trans (objectRawBoundaryEdge_assembly X ((coreSConstruction 1 X.carrier).δ 1 e)).symm)
  δ_map_of_lt j hj := by simp at hj
  δ_map_of_gt j hj := by
    have h : (2 : Fin 3) < j := hj
    omega

/-- 元の対角の辺の基本亜群の類は、同じ内部始点の object S₁ の辺の類と等しい。 -/
lemma rawBoundaryPath_diagonal (X : StableModel.{u})
    (e : (coreSConstruction 1 X.carrier) _⦋1⦌) :
    rawBoundaryPath X
      (((iteratedSRealizationCoordinateIso 0 X).hom ≫ boundaryReductionQuotient 0 X).app
        (Opposite.op ⦋1⦌) e) =
      objectBoundaryPath X ((coreSConstruction 1 X.carrier).δ 1 e).val := by
  have h := SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (fundamentalLoopMulToComp (rawBoundaryDiagonalTriangle X e))
  rw [fundamentalLoopEdge_const, SSet.Truncated.HomotopyCategory.homMk_id,
    Category.comp_id] at h
  exact congrArg (FreeGroupoid.of
    (hoFunctor.obj (boundaryReducedRealization 0 X).right)).map h.symm

end SerrePositivity.KST.SConstruction
