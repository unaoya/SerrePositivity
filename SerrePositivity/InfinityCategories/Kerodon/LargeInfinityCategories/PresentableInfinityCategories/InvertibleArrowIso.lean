module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMinimum
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.StronglySaturatedHom

/-!
概要：元の可逆な辺は、射圏内でその始点の恒等射と全自然同型で結ばれる。
方針：区間最小値の指定ホモトピーの二つの成分で、恒等辺と元の可逆辺を検査する。
規約：元の辺を同型な代表へ置き換えず、射圏内の実同型を返す。
使われ方：実 Ind 像の辺クラスが全ての可逆辺を含むことの検証。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 元の可逆辺から、元の始点上の恒等射との射圏内の全同型を構成する。 -/
def invertibleArrow_sourceIdentityIso {C : SSet.{u}} [Quasicategory C]
    (F : (Δ[1] : SSet.{u}) ⟶ C)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv F))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.const (F.app _ (stdSimplex.obj₀Equiv.symm 0))) F := by
  let H : SSet.Homotopy (SSet.const (F.app _ (stdSimplex.obj₀Equiv.symm 0))) F := {
    h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMinimum ≫ F
    h₀ := by
      change SSet.ι₀ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMinimum ≫ F) =
        SSet.const (F.app _ (stdSimplex.obj₀Equiv.symm 0))
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMinimum_second_zero, SSet.const_comp]
    h₁ := by
      change SSet.ι₁ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMinimum ≫ F) = F
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMinimum_second_one, Category.id_comp]
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact False.elim s.1.property }
  have heval (j : Fin 2) :
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (stdSimplex.obj₀Equiv.symm j)).edge =
        SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint j Δ[1] ≫ H.h) := by
    rw [SSet.yonedaEquiv_comp]
    change H.h.app (Opposite.op ⦋1⦌)
      ((Truncated.Edge.id (X := (truncation 2).obj (Δ[1] : SSet.{u}))
        (stdSimplex.obj₀Equiv.symm j)).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
      H.h.app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm j) 1,
          SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
    apply congrArg (H.h.app (Opposite.op ⦋1⦌))
    apply Prod.ext
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _).symm
    · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.{u}.edge = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))
      apply SSet.stdSimplex.ext
      intro i
      fin_cases i <;> rfl
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy H
  intro k
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective k
  fin_cases j
  · have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).edge =
        (Truncated.Edge.id (X := (truncation 2).obj C)
          (F.app _ (stdSimplex.obj₀Equiv.symm 0))).edge := by
      rw [heval 0]
      change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMinimum ≫ F)) = _
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMinimum_first_zero, SSet.const_comp]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr
    change IsIso (Truncated.HomotopyCategory.homMk (Truncated.Edge.id _))
    rw [Truncated.HomotopyCategory.homMk_id]
    infer_instance
  · have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).edge =
        SSet.yonedaEquiv F := by
      rw [heval 1]
      change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMinimum ≫ F)) = _
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMinimum_first_one, Category.id_comp]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr hF

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
