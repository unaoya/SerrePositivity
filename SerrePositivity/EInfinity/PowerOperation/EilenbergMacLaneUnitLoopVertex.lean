module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneAdjointSuspension
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneLoopProperties
public import SerrePositivity.KST.Spectra.PointedCurryFamilyVertex
public import SerrePositivity.KST.Spectra.LoopZeroOrientation

/-!
# 指定構造射の単位の頂点と固定した基本円の loop の厳密な照合

DAG XIII §2.2 の零次数の Ω 比較への前段。基本円の選択を変えず、
同じ零 loop 比較の逆元の向きを保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory MonoidalClosed
open scoped Simplicial
open SerrePositivity.DifferentialGraded
open SerrePositivity.PointedSimplicialSet
open SerrePositivity.KST.Spectra.PointedMapping
  (familyVertex unitUnderlyingHom_curry'_vertex)
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
variable (A : Type u) [CommRing A]

/-- 指定零次球面の非基点側は元の AW 単位の頂点そのもの。 -/
lemma gammaUnitBasedPoint_vertex :
    unitVertexEquiv (gammaPointed A (𝟙_ (Complex A))) (gammaUnitBasedPoint A) =
      gammaUnitSimplex A ⦋0⦌ := by
  change SSet.unitHomEquiv _
    ((PointedObject.adjoinHomEquiv (𝟙_ SSet.{u}) (gammaPointed A (𝟙_ (Complex A))))
      ((PointedObject.adjoinHomEquiv (𝟙_ SSet.{u})
        (gammaPointed A (𝟙_ (Complex A)))).symm (gammaUnitPoint A))) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- 随伴構造射の単位での値は、指定基本円の同じ写像族の頂点である。 -/
lemma gammaAdjointSuspension_unit_vertex :
    ((gammaAdjointSuspension A).app (𝟙_ (Complex A))).right.app (Opposite.op ⦋0⦌)
      (gammaUnitSimplex A ⦋0⦌) =
    familyVertex (unitCircle A ≫
      (gammaPointedFunctor A).map (unitShiftAutomorphism A).hom) := by
  have h := gammaAdjointSuspension_on_unit A
  change gammaUnitBasedPoint A ≫ (gammaAdjointSuspension A).app (𝟙_ (Complex A)) =
    curry' (unitCircle A ≫ (gammaPointedFunctor A).map (unitShiftAutomorphism A).hom) at h
  have hv := congrArg (unitVertexEquiv
    ((gammaLoopFunctor A).obj (𝟙_ (Complex A)))) h
  rw [unitVertexEquiv_naturality, gammaUnitBasedPoint_vertex] at hv
  exact hv.trans (unitUnderlyingHom_curry'_vertex _)

/-- 既存の零 loop 比較は、この指定頂点を指定基本円の像の逆元へ送る。 -/
lemma gammaAdjointSuspension_unit_loop_class :
    KST.Spectra.loopZeroHomotopyEquiv (gammaPointed A ((𝟙_ (Complex A))⟦(1 : ℤ)⟧))
      (KanHomotopy.mk 0 ((SSet.PtSimplex.equiv₀
        ((gammaLoopFunctor A).obj (𝟙_ (Complex A))).basepoint).symm
        (((gammaAdjointSuspension A).app (𝟙_ (Complex A))).right.app (Opposite.op ⦋0⦌)
          (gammaUnitSimplex A ⦋0⦌)))) =
      (KanHomotopyGroup.mk (KST.Spectra.SphereSimplex.equiv
        (gammaPointed A ((𝟙_ (Complex A))⟦(1 : ℤ)⟧)) 1
        (unitCircle A ≫ (gammaPointedFunctor A).map (unitShiftAutomorphism A).hom)))⁻¹ := by
  rw [gammaAdjointSuspension_unit_vertex]
  exact KST.Spectra.loopZeroHomotopyEquiv_familyVertex _ _

end SerrePositivity.EInfinity.PowerOperation
