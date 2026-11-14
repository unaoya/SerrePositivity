module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeRootedHomFamily
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CommaComparisons.NativeSpanUniversalPathFamily

/-!
概要：始対象を前置した四面体の共通脚と終点を、元の native な共通脚そのものに同定する。
方針：四面体の辺 03 と右退化の有限順序写像を計算し、元の三角形の長辺の面を使う。
規約：指定余錐の頂点の等号を含め、元の共通脚の一単体を保つ。
使われ方：四面体上の全 Hom の族の共通脚への制限と、実際の脚の前合成との比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 四面体の最初と最後の頂点を結ぶ実際の辺 03。 -/
def tetrahedronRootEdge : (Δ[1] : SSet.{u}) ⟶ Δ[3] :=
  stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4)

/-- 辺 03 を右退化で三角形へ戻すと、元の長辺 02。 -/
lemma tetrahedronRootEdge_degeneracy :
    tetrahedronRootEdge.{u} ≫ stdSimplex.σ (2 : Fin 3) = stdSimplex.δ (1 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 辺 03 の始点は、前置した比較辺の始点。 -/
lemma tetrahedronRootEdge_source :
    stdSimplex.δ (1 : Fin 2) ≫ tetrahedronRootEdge.{u} =
      stdSimplex.δ (1 : Fin 2) ≫
        (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 辺 03 の終点は、終端面の最後の頂点。 -/
lemma tetrahedronRootEdge_target_terminalFace :
    stdSimplex.δ (0 : Fin 2) ≫ tetrahedronRootEdge.{u} =
      (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) ≫ stdSimplex.δ (0 : Fin 4) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 三角形の最後の頂点は、長辺の終点。 -/
lemma triangleTip_longEdge :
    (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) : (Δ[0] : SSet.{u}) ⟶ Δ[2]) =
      stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))

/-- 元の native な span の共通脚を、その一単体のまま点図式の辺として表示する。 -/
def specifiedCoconeNativeRootEdge : (Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC).edge

/-- 四面体の底の辺 03 は、元の native な span の共通脚そのもの。 -/
lemma specifiedCoconeRootedTetrahedron_rootEdge :
    tetrahedronRootEdge ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron hp p c hc dB dC ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))) =
      specifiedCoconeNativeRootEdge hp p c hc dB dC := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron_base, ← Category.assoc,
    tetrahedronRootEdge_degeneracy, stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
      g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC).d₁

omit [Mono g] in
/-- 元の共通脚の始点は、共通部分の余錐の頂点図式。 -/
lemma specifiedCoconeNativeRootEdge_source :
    stdSimplex.δ (1 : Fin 2) ≫ specifiedCoconeNativeRootEdge hp p c hc dB dC =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram c := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC).δ_one_yonedaEquiv_symm.trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram_eq c).symm

/-- 元の共通脚の終点は、同じ指定余錐の頂点図式。 -/
lemma specifiedCoconeNativeRootEdge_target :
    stdSimplex.δ (0 : Fin 2) ≫ specifiedCoconeNativeRootEdge hp p c hc dB dC =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC).δ_zero_yonedaEquiv_symm
  exact h.trans ((congrArg SSet.yonedaEquiv.symm
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedPathCocone_vertex_eq_strictSpan hp p c hc dB dC).symm).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexDiagram_eq _).symm)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
