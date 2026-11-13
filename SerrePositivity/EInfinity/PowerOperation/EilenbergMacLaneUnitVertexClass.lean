module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneZeroCohomologyMap
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaUnitClass
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneUnitLoopVertex

/-!
# 指定 AW 単位の零次ホモトピー類と随伴構造射の代表

DAG XIII §2.2 の零次数の Ω 比較への前段。元の頂点を同じ PtSimplex 同値で
零次ホモトピー類にし、構造射による像も同じ頂点で計算する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open scoped Simplicial
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open SerrePositivity.KST.Spectra (pointedHomotopyMap)
variable (A : Type u) [CommRing A]

/-- AW 単位の元の頂点を、指定基点で零次ホモトピー類として読む。 -/
def gammaUnitVertexClass :
    KanHomotopy ((gammaPointedFunctor A).obj (𝟙_ (Complex A))).right 0
      ((gammaPointedFunctor A).obj (𝟙_ (Complex A))).basepoint :=
  KanHomotopy.mk 0 ((SSet.PtSimplex.equiv₀
    ((gammaPointedFunctor A).obj (𝟙_ (Complex A))).basepoint).symm
      (gammaUnitSimplex A ⦋0⦌))

lemma gammaBasedPiZeroCohomologyEquiv_unit :
    gammaBasedPiZeroCohomologyEquiv A (𝟙_ (Complex A)) (gammaUnitVertexClass A) =
      HomologyZero.unitClass (𝟙_ (Complex A)) (𝟙 _) := by
  change gammaPiZeroCohomologyEquiv A (𝟙_ (Complex A))
    (KanHomotopyZero.equivPiZero (KanHomotopyZero.mk _)) = _
  rw [KanHomotopyZero.equivPiZero_mk]
  have h := (SSet.PtSimplex.equiv₀
    ((gammaPointedFunctor A).obj (𝟙_ (Complex A))).basepoint).apply_symm_apply
      (gammaUnitSimplex A ⦋0⦌)
  exact (congrArg (fun x => gammaPiZeroCohomologyEquiv A (𝟙_ (Complex A))
    (SSet.π₀.mk x)) h).trans (gammaPiZeroCohomologyEquiv_unit A)

lemma gammaBasedPiZeroCohomologyEquiv_symm_unit :
    (gammaBasedPiZeroCohomologyEquiv A (𝟙_ (Complex A))).symm
      (HomologyZero.unitClass (𝟙_ (Complex A)) (𝟙 _)) = gammaUnitVertexClass A := by
  apply (gammaBasedPiZeroCohomologyEquiv A (𝟙_ (Complex A))).injective
  rw [Equiv.apply_symm_apply, gammaBasedPiZeroCohomologyEquiv_unit]

/-- 構造射の零次誘導写像の単位での値は、同じ実際の頂点の像の類。 -/
lemma gammaUnitVertexClass_map_adjoint :
    pointedHomotopyMap 0 ((gammaAdjointSuspension A).app (𝟙_ (Complex A)))
      (gammaUnitVertexClass A) =
      KanHomotopy.mk 0 ((SSet.PtSimplex.equiv₀
        ((gammaLoopFunctor A).obj (𝟙_ (Complex A))).basepoint).symm
        (((gammaAdjointSuspension A).app (𝟙_ (Complex A))).right.app (Opposite.op ⦋0⦌)
          (gammaUnitSimplex A ⦋0⦌))) := by
  change KanHomotopy.map 0 _ _ (KanHomotopy.mk 0 _) = _
  rw [KanHomotopy.map_mk]
  congr 1
  apply (SSet.PtSimplex.equiv₀
    ((gammaLoopFunctor A).obj (𝟙_ (Complex A))).basepoint).injective
  let es := SSet.PtSimplex.equiv₀
    ((gammaPointedFunctor A).obj (𝟙_ (Complex A))).basepoint
  let et := SSet.PtSimplex.equiv₀
    ((gammaLoopFunctor A).obj (𝟙_ (Complex A))).basepoint
  change ((gammaAdjointSuspension A).app (𝟙_ (Complex A))).right.app (Opposite.op ⦋0⦌)
    (es (es.symm (gammaUnitSimplex A ⦋0⦌))) =
    et (et.symm (((gammaAdjointSuspension A).app (𝟙_ (Complex A))).right.app
      (Opposite.op ⦋0⦌) (gammaUnitSimplex A ⦋0⦌)))
  exact (congrArg (((gammaAdjointSuspension A).app (𝟙_ (Complex A))).right.app
    (Opposite.op ⦋0⦌)) (es.apply_symm_apply _)).trans (et.apply_symm_apply _).symm

end SerrePositivity.EInfinity.PowerOperation
