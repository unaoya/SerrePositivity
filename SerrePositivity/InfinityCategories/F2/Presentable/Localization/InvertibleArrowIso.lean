module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMinimum
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.HomotopyLimits.StronglySaturatedHom

/-!
概要：元の可逆な辺は、射圏内でその始点の恒等射と全自然同型で結ばれる。
方針：区間最小値の指定ホモトピーの二つの成分で、恒等辺と元の可逆辺を検査する。
規約：元の辺を同型な代表へ置き換えず、射圏内の実同型を返す。
使われ方：実 Ind 像の辺クラスが全ての可逆辺を含むことの検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization

/-- 元の可逆辺から、元の始点上の恒等射との射圏内の全同型を構成する。 -/
def invertibleArrow_sourceIdentityIso {C : SSet.{u}} [Quasicategory C]
    (F : (Δ[1] : SSet.{u}) ⟶ C)
    (hF : IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv F))) :
    FunctorIso (SSet.const (F.app _ (stdSimplex.obj₀Equiv.symm 0))) F := by
  let H : SSet.Homotopy (SSet.const (F.app _ (stdSimplex.obj₀Equiv.symm 0))) F := {
    h := intervalMinimum ≫ F
    h₀ := by
      change SSet.ι₀ ≫ (intervalMinimum ≫ F) =
        SSet.const (F.app _ (stdSimplex.obj₀Equiv.symm 0))
      rw [← Category.assoc, intervalMinimum_second_zero, SSet.const_comp]
    h₁ := by
      change SSet.ι₁ ≫ (intervalMinimum ≫ F) = F
      rw [← Category.assoc, intervalMinimum_second_one, Category.id_comp]
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact False.elim s.1.property }
  have heval (j : Fin 2) :
      (simplicialHomotopyVertexEdge H (stdSimplex.obj₀Equiv.symm j)).edge =
        SSet.yonedaEquiv (prismEndpoint j Δ[1] ≫ H.h) := by
    rw [SSet.yonedaEquiv_comp]
    change H.h.app (Opposite.op ⦋1⦌)
      ((Truncated.Edge.id (X := (truncation 2).obj (Δ[1] : SSet.{u}))
        (stdSimplex.obj₀Equiv.symm j)).edge, homotopyIntervalEdge.edge) =
      H.h.app (Opposite.op ⦋1⦌)
        (PinchedHom.constant (stdSimplex.obj₀Equiv.symm j) 1,
          SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
    apply congrArg (H.h.app (Opposite.op ⦋1⦌))
    apply Prod.ext
    · exact (pinchedConstant_one _).symm
    · change homotopyIntervalEdge.{u}.edge = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))
      apply SSet.stdSimplex.ext
      intro i
      fin_cases i <;> rfl
  apply functorIsoOfPointwiseInvertibleHomotopy H
  intro k
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective k
  fin_cases j
  · have he : (simplicialHomotopyVertexEdge H (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).edge =
        (Truncated.Edge.id (X := (truncation 2).obj C)
          (F.app _ (stdSimplex.obj₀Equiv.symm 0))).edge := by
      rw [heval 0]
      change SSet.yonedaEquiv (prismEndpoint 0 Δ[1] ≫ (intervalMinimum ≫ F)) = _
      rw [← Category.assoc, intervalMinimum_first_zero, SSet.const_comp]
      exact pinchedConstant_one _
    apply (isInvertibleEdge_congr he).mpr
    change IsIso (Truncated.HomotopyCategory.homMk (Truncated.Edge.id _))
    rw [Truncated.HomotopyCategory.homMk_id]
    infer_instance
  · have he : (simplicialHomotopyVertexEdge H (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).edge =
        SSet.yonedaEquiv F := by
      rw [heval 1]
      change SSet.yonedaEquiv (prismEndpoint 1 Δ[1] ≫ (intervalMinimum ≫ F)) = _
      rw [← Category.assoc, intervalMinimum_first_one, Category.id_comp]
    exact (isInvertibleEdge_congr he).mpr hF

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
