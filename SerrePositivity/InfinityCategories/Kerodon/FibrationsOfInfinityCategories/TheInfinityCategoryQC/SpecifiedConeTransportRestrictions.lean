module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpecifiedLimitConeTransport

/-!
概要：指定された極限錐の輸送の二つの制限を明示する。
方針：境界の等式を左右の包含へ制限して prism の貼り合わせを計算する。
規約：頂点側は定値、図式側は元の指定 prism。
使われ方：Cat_∞ の引き戻し錐の二射影の比較。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：輸送の全錐のホモトピーは頂点側で定値。
方針：二因子の和への制限を左包含へ制限する。
規約：全時刻の厳密な等式。
使われ方：錐の二脚の比較で頂点の自己同値を導入しない。 -/
lemma SpecifiedLimitConeTransport.apex {K X : SSet.{u}} {p q : K ⟶ X}
    {H : (Δ[1] : SSet.{u}) ⊗ K ⟶ X} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q}
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpecifiedLimitConeTransport (p := p) H d) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K ▷ (Δ[1] : SSet.{u})) ≫ t.homotopy.h =
      fst Δ[0] Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K ≫ d.val := by
  have h := congrArg
    (fun z ↦ ((coprod.inl : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ K) ▷ (Δ[1] : SSet.{u})) ≫ z)
    t.boundary
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, coprod.inl_desc] at h
  calc
    _ = _ := h
    _ = (β_ (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
        ((Δ[1] ◁ (coprod.inl : Δ[0] ⟶ Δ[0] ⨿ K)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneBoundaryPrism d H) := rfl
    _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneBoundaryPrism, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coprodPrism_inl]; rfl
/-- 概要：輸送の全錐のホモトピーは図式側で指定 prism と一致する。
方針：二因子の和への制限を右包含へ制限する。
規約：指定した自然変換の円柱自体を保持する。
使われ方：二脚の自然性の正方形の成分を計算する。 -/
lemma SpecifiedLimitConeTransport.diagram {K X : SSet.{u}} {p q : K ⟶ X}
    {H : (Δ[1] : SSet.{u}) ⊗ K ⟶ X} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q}
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpecifiedLimitConeTransport (p := p) H d) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K ▷ (Δ[1] : SSet.{u})) ≫ t.homotopy.h =
      (β_ K (Δ[1] : SSet.{u})).hom ≫ H := by
  have h := congrArg
    (fun z ↦ ((coprod.inr : K ⟶ (Δ[0] : SSet.{u}) ⨿ K) ▷ (Δ[1] : SSet.{u})) ≫ z)
    t.boundary
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, coprod.inr_desc] at h
  calc
    _ = _ := h
    _ = (β_ K (Δ[1] : SSet.{u})).hom ≫
        ((Δ[1] ◁ (coprod.inr : K ⟶ Δ[0] ⨿ K)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneBoundaryPrism d H) := rfl
    _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneBoundaryPrism, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coprodPrism_inr]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
