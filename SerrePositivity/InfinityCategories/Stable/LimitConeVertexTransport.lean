module
public import SerrePositivity.InfinityCategories.Stable.RightFibrationEdgeTarget
public import SerrePositivity.InfinityCategories.Derived.RightFibrationReflection
public import SerrePositivity.InfinityCategories.Core.TerminalTransport

/-!
概要：全パラメーターに整合する実錐比較を、矢印圏の四角形へ移す。
方針：元の全単体・同じ比較辺・指定頂点への錐の移送を保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma exists_limitCone_vertex_of_invertible {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : JoinCone p) (hc : IsLimitCone c) {y : X _⦋0⦌}
    (e : X.Edge y c.vertex) (he : IsInvertibleEdge e) :
    ∃ d : JoinCone p, IsLimitCone d ∧ d.vertex = y := by
  let q := sliceOverProjection p
  obtain ⟨F, hF₁, hFq⟩ := rightFibration_liftEdge_target q c e.toTruncated
  let s := SSet.yonedaEquiv F
  let d : JoinCone p := (sliceOver p).δ 1 s
  have hs : (sliceOver p).δ 0 s = c := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₁, Equiv.apply_symm_apply]
  let a : Truncated.Edge (X := (truncation 2).obj (sliceOver p)) d c := ⟨s, rfl, hs⟩
  have hm : (a.map ((truncation 2).map q)).edge = e.edge := by
    change q.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv F) = e.edge
    rw [← SSet.yonedaEquiv_comp, hFq]
    exact Equiv.apply_symm_apply _ e.edge
  have ha := derived_rightFibration_reflects_invertibleEdge q a
    ((isInvertibleEdge_congr hm).2 he)
  have : IsIso (Truncated.HomotopyCategory.homMk a) := ha
  refine ⟨d, hc.of_vertexIso (asIso (Truncated.HomotopyCategory.homMk a)).symm, ?_⟩
  have ht := congrArg (fun z ↦ X.δ 1 z) hm
  change X.δ 1 (q.app (Opposite.op ⦋1⦌) s) = X.δ 1 e.edge at ht
  have hn := ConcreteCategory.congr_hom (q.naturality (SimplexCategory.δ (1 : Fin 2)).op) s
  exact hn.trans (ht.trans e.src_eq)

end SerrePositivity.InfinityCategories
