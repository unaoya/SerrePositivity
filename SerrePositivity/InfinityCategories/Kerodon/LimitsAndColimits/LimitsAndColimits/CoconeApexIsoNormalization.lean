module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-!
概要：全前段を固定したまま、余錐頂点を指定した同型の始点に厳密に揃える。
方針：coslice 射影の left fibration で指定可逆辺を持ち上げ、全余錐の同型へ戻す。
規約：全前段の固定と全余錐の FunctorIso を保持し、頂点だけの比較で代用しない。
使われ方：c5 の全図式持ち上げで商の像に属する余錐頂点へ正規化する。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 前段全体を固定し、頂点を指定点に厳密に揃えた同型な実余錐を構成する。 -/
lemma exists_cocone_apexIsoNormalization {K X : SSet.{u}} [Quasicategory X]
    {F : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) {z : X _⦋0⦌} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso z c.vertex) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F, d.vertex = z ∧ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso d.val c.val) := by
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective z c.vertex e.hom
  have hai : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge, ha]
    infer_instance
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F
  obtain ⟨L, hL₁, hLp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftInvertibleEdge_target p c a hai
  let v := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).δ 1 (SSet.yonedaEquiv L)
  let d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F := v
  let l : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F)) v c := {
    edge := SSet.yonedaEquiv L
    src_eq := rfl
    tgt_eq := by
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).δ 0 (SSet.yonedaEquiv L) = c
      rw [← stdSimplex.yonedaEquiv_δ_comp, hL₁, Equiv.apply_symm_apply] }
  have hmap : (l.map ((truncation 2).map p)).edge = a.edge := by
    change p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv L) = a.edge
    rw [← SSet.yonedaEquiv_comp, hLp]
    exact Equiv.apply_symm_apply _ _
  have hz : d.vertex = z := by
    change p.app (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).δ 1 (SSet.yonedaEquiv L)) = z
    calc
      _ = X.δ 1 (p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv L)) :=
        ConcreteCategory.congr_hom (C := Type u)
          (p.naturality (SimplexCategory.δ (1 : Fin 2)).op) (SSet.yonedaEquiv L)
      _ = z := by
        change X.δ 1 (l.map ((truncation 2).map p)).edge = z
        rw [hmap]
        exact a.src_eq
  have hli : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge l :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_reflects_invertibleEdge p l ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hmap).mpr hai)
  exact ⟨d, hz, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFunctorIsoOfVertexIso d c
    (asIso (Truncated.HomotopyCategory.homMk l))⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_cocone_apexIsoNormalization := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_cocone_apexIsoNormalization
