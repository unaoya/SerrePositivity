module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CoconeEndpointTransport
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CoslicePushoutGluing

/-! # 整合する二枝の終点輸送の貼り合わせ

概要：pushout の二枝で整合する終点輸送の区間族は全図式の終点輸送へ貼り合わさる。
方針：可変終点の coslice 族を貼り、先頭を二枝の一意性、終端を fiber の普遍性で戻す。
規約：二枝の区間族の共通部分での一致を仮定する。使われ方：対称 span の輸送をループ表示へ送る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：二枝の輸送の区間族が共通部分で整合すれば、全図式の輸送を両枝と可換に構成できる。
方針：join の pushout による区間族の貼り合わせ、先頭の一意性、終端の fiber lift を使う。
規約：図式の余極限性や値域の quasicategory 性は不要。整合条件そのものは入力とする。
使われ方：同じ枝の同時輸送から対称 span 全体の終点輸送を構成する。 -/
lemma exists_coconeEndpointTransport_glue {A B C D X : SSet.{u}}
    {i : A ⟶ B} {j : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    (hP : IsPushout i j r s) (p : D ⟶ X) {x y : X _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (Tb : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (r ≫ p)) a)
    (Tc : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (s ≫ p)) a)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p x ⊗ (Δ[1] : SSet.{u}))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p r x ▷ (Δ[1] : SSet.{u})) ≫ Tb.h) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap j (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p x ⊗ (Δ[1] : SSet.{u}))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p s x ▷ (Δ[1] : SSet.{u})) ≫ Tc.h)) :
    ∃ T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) a,
      T.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p r =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p r x ▷ (Δ[1] : SSet.{u})) ≫ Tb.h ∧
      T.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p s =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p s x ▷ (Δ[1] : SSet.{u})) ≫ Tc.h ∧
      T.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p r y = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p r x ≫ Tb.map ∧
      T.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p s y = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p s x ≫ Tc.map := by
  let br := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p r x
  let cr := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p s x
  obtain ⟨H, hHb, hHc, hHp⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_coslice_glue_of_pushout hP p
    ((br ▷ (Δ[1] : SSet.{u})) ≫ Tb.h) ((cr ▷ (Δ[1] : SSet.{u})) ≫ Tc.h) h
  have hH₀ : SSet.ι₀ ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) x := by
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coslice_hom_ext_of_pushout hP p
    · rw [Category.assoc, hHb, ← Category.assoc, SSet.ι₀_comp, Category.assoc, Tb.h₀]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_restrict_ι p r x
    · rw [Category.assoc, hHc, ← Category.assoc, SSet.ι₀_comp, Category.assoc, Tc.h₀]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_restrict_ι p s x
  have hHover : H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p =
      snd (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p x) (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm a.edge := by
    rw [hHp, Category.assoc, Tb.over, ← Category.assoc, whiskerRight_snd]
    rfl
  have hHy : (SSet.ι₁ ≫ H) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p = SSet.const y := by
    rw [Category.assoc, hHover]
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stablePrism_edge_one a
  let T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) a :=
    { map := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) y (SSet.ι₁ ≫ H) hHy
      h := H
      h₀ := hH₀
      h₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _).symm
      over := hHover }
  refine ⟨T, hHb, hHc, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (r ≫ p)) y
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_restrict_ι, ← Category.assoc, ← T.h₁,
      Category.assoc, hHb, ← Category.assoc, SSet.ι₁_comp, Category.assoc, Tb.h₁, Category.assoc]
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (s ≫ p)) y
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_restrict_ι, ← Category.assoc, ← T.h₁,
      Category.assoc, hHc, ← Category.assoc, SSet.ι₁_comp, Category.assoc, Tc.h₁, Category.assoc]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
