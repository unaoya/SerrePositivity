module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroCornerPasting

/-! # 任意の二頂点を持つ零始点の押し出し四角形

概要：安定 ∞ 圏の任意の二頂点は、零始点を持つ押し出し span の二つの終点となる。
方針：一方の頂点の loop 四角形の右に、もう一方への零射を付加して長方形を構成する。
規約：二つの入力頂点を厳密に指定する。使われ方：有限直和と前加法構造の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：任意の二頂点 x・y に対し、零始点からこの二頂点へ向かう押し出し四角形が存在する。
方針：y の loop 四角形を懸垂の左四角形とし、右下の零頂点から x への辺との合成二単体を貼る。
規約：通常のホモトピー圏の coproduct の instance は別途必要。
使われ方：二項直和の実際の ∞ 圏の普遍四角形。 -/
lemma exists_zeroSourcePushoutSquare {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (x y : X _⦋0⦌) :
    ∃ R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X,
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 0 0) ∧ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 1 0 = x ∧
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 0 1 = y ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R := by
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenLoopSquare y
  let f := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow s.square
  let g := Classical.choice (s.other_zero.1.nonempty_edge x)
  let c := f.compStruct g
  let τ : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm c.simplex
  have hτ₂ : stdSimplex.δ (2 : Fin 3) ≫ τ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ s.square := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (fun a => X.δ 2 a) (SSet.yonedaEquiv.apply_symm_apply c.simplex)).trans
      (c.d₂.trans (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow_edge s.square))
  have hτ₀ : stdSimplex.δ (0 : Fin 3) ≫ τ = SSet.yonedaEquiv.symm g.edge := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (fun a => X.δ 0 a) (SSet.yonedaEquiv.apply_symm_apply c.simplex)).trans
      (c.d₀.trans (SSet.yonedaEquiv.apply_symm_apply g.edge).symm)
  obtain ⟨F, hleft, hbottom, hright, _⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_pushoutRectangle_of_zeroTriangle
    s.toZeroTriangle (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback s.toZeroTriangle s.isPullback) τ hτ₂.symm
  let R := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0
  have hsource : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 0 0 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) 1 0 := by
    change F.app (Opposite.op ⦋0⦌) _ = F.app (Opposite.op ⦋0⦌) _
    congr 1
  have htop : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 0 1 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) 1 1 := by
    change F.app (Opposite.op ⦋0⦌) _ = F.app (Opposite.op ⦋0⦌) _
    congr 1
  have hbottomR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ R = SSet.yonedaEquiv.symm g.edge := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_bottomEdge, hbottom, hτ₀]
  have hx : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 1 0 = x := by
    rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_target]
    have h := congrArg (fun a : (Δ[1] : SSet.{u}) ⟶ X => X.δ 0 (SSet.yonedaEquiv a)) hbottomR
    exact h.trans ((congrArg (X.δ 0) (SSet.yonedaEquiv.apply_symm_apply g.edge)).trans g.tgt_eq)
  refine ⟨R, ?_, hx, ?_, hright⟩
  · rw [hsource, hleft]
    exact s.other_zero
  · rw [htop, hleft]
    exact s.target_eq

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
