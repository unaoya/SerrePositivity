module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BinaryCoconeTriangleFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-! # 二点図式の余錐間の辺の持ち上げ

概要：二つの脚と可換な頂点の辺を、余錐間の辺へ持ち上げる。
方針：脚の合成二単体の族を貼り合わせ、coslice へ curry する。
規約：射影の一次単体を厳密に保持。使われ方：二項余積の一意性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：二つの脚の合成二単体から頂点の辺を余錐間の辺へ持ち上げられる。
方針：二つの脚の族を貼り合わせて curry し、両端と射影を計算する。
規約：quasicategory 性は不要。使われ方：余錐間の射の存在。 -/
lemma exists_binaryCoconeEdgeLift {X : SSet.{u}}
    {p : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) c.vertex d.vertex)
    (L : (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft).CompStruct e (d.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft))
    (R : (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight).CompStruct e (d.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight)) :
    ∃ E : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)) c d,
      (E.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p))).edge = e.edge := by
  obtain ⟨U, hfixed, hzero, hone, hright⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_binaryCoconeTriangleFamily L R
  let a : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry U hfixed
  have ha₀ : stdSimplex.δ (1 : Fin 2) ≫ a = SSet.yonedaEquiv.symm c := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective p
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda]
    exact hzero
  have ha₁ : stdSimplex.δ (0 : Fin 2) ≫ a = SSet.yonedaEquiv.symm d := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective p
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda]
    exact hone
  let E : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)) c d :=
    { edge := SSet.yonedaEquiv a
      src_eq := by
        change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p).δ 1 (SSet.yonedaEquiv a) = c
        rw [← stdSimplex.yonedaEquiv_δ_comp, ha₀]
        exact (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) (n := ⦋0⦌)).apply_symm_apply c
      tgt_eq := by
        change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p).δ 0 (SSet.yonedaEquiv a) = d
        rw [← stdSimplex.yonedaEquiv_δ_comp, ha₁]
        exact (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) (n := ⦋0⦌)).apply_symm_apply d }
  have hproj : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p = SSet.yonedaEquiv.symm e.edge := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry]
    exact hright
  refine ⟨E, ?_⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv a) = e.edge
  rw [← SSet.yonedaEquiv_comp, hproj]
  exact (SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).apply_symm_apply e.edge

/-- 概要：ホモトピー圏で両脚と可換な辺は余錐間の辺へ持ち上がる。
方針：可換式を合成二単体に持ち上げて前補題を使う。
規約：値域は quasicategory。使われ方：余極限頂点からの射の一意性。 -/
lemma exists_binaryCoconeEdgeLift_of_comm {X : SSet.{u}} [Quasicategory X]
    {p : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) c.vertex d.vertex)
    (hL : SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft) ≫
      SSet.Truncated.HomotopyCategory.homMk e =
        SSet.Truncated.HomotopyCategory.homMk (d.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft))
    (hR : SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight) ≫
      SSet.Truncated.HomotopyCategory.homMk e =
        SSet.Truncated.HomotopyCategory.homMk (d.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight)) :
    ∃ E : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)) c d,
      (E.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p))).edge = e.edge := by
  obtain ⟨L⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac hL
  obtain ⟨R⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac hR
  exact exists_binaryCoconeEdgeLift e L R

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
