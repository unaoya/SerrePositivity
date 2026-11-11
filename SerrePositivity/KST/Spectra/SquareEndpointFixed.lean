module

public import SerrePositivity.KST.Spectra.IntervalEndpointFamilies
public import SerrePositivity.KST.Spectra.SquareBoundaryFamilies

/-!
概要：左右辺全体が一定な正方形は、二端点の境界全体を元の始辺の値で固定する。
方針：時刻零で定数辺の値を照合し、二端点の余積の各成分で検査する。
規約：異なる左右の定数を許す。使われ方：比較正方形の自由区間境界上の垂直性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.SquareAdjustment
variable {E : SSet.{u}} {a b : (Δ[1] : SSet.{u}) ⟶ E} (H : SSet.Homotopy a b)

private lemma endpoint_fixed (c : 𝟙_ SSet.{u} ⟶ (Δ[1] : SSet.{u})) (v : E _⦋0⦌)
    (hc : c ▷ (Δ[1] : SSet.{u}) ≫ H.h = SSet.const v) :
    c ▷ (Δ[1] : SSet.{u}) ≫ H.h = fst (𝟙_ SSet.{u}) (Δ[1] : SSet.{u}) ≫ c ≫ a := by
  have hn : (SSet.ι₀ : (𝟙_ SSet.{u}) ⟶ _) ≫ c ▷ (Δ[1] : SSet.{u}) =
      c ≫ SSet.ι₀ := rfl
  have hv : c ≫ a = SSet.const v := by
    rw [← H.h₀, ← Category.assoc, ← hn, Category.assoc, hc, SSet.comp_const]
  rw [hc, hv, SSet.comp_const]

/-- 二つの終点の定数性は、二端点境界全体を固定する実相対ホモトピーを与える。 -/
lemma fixed_endpoints (x y : E _⦋0⦌)
    (hx : leftSide ≫ H.h = SSet.const x) (hy : rightSide ≫ H.h = SSet.const y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right ▷ (Δ[1] : SSet.{u}) ≫ H.h =
      fst ((𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) (Δ[1] : SSet.{u}) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.right ≫ a := by
  have h₀ := (intervalFamily_endpoint_unit_iff H.h x (1 : Fin 2)).1
    (by rw [face_left, Category.assoc, hx, SSet.comp_const])
  have h₁ := (intervalFamily_endpoint_unit_iff H.h y (0 : Fin 2)).1
    (by rw [face_right, Category.assoc, hy, SSet.comp_const])
  apply PointedObject.tensorRightCoprod_hom_ext
  · rw [← comp_whiskerRight_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inl, whiskerRight_fst_assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inl_assoc]
    exact endpoint_fixed H _ y h₁
  · rw [← comp_whiskerRight_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inr, whiskerRight_fst_assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inr_assoc]
    exact endpoint_fixed H _ x h₀

end SerrePositivity.KST.Spectra.SquareAdjustment
