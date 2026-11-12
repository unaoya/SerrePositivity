module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.FullCosliceRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.CoconeLegPostcomposition

/-!
概要：周囲で得た因子化の比較辺を、元の余錐脚を保持して実引き戻しへ回収する。
方針：二つの実際の辺を引き戻しへ持ち上げ、終点を両射影で確認する。
規約：辺の類ではなく元の辺と元の脚の厳密な等式を保持する。
使われ方：全部分圏での compact 全余錐の相対因子化。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：周囲の因子化辺と指定された底の余錐脚を同じ実引き戻しへ貼り合わせる。
方針：二つの区間射を持ち上げ、終点と第一射影を厳密に回収する。
規約：元の終点と元の余錐脚を固定する。
使われ方：前層内の全余錐因子化の元の圏への降下。 -/
lemma exists_factorizationEdge_of_isPullback
    {X E Y B : SSet.{u}} (a : X ⟶ E) (b : X ⟶ Y) (j : E ⟶ B) (p : Y ⟶ B)
    (hsq : IsPullback a b j p) {K : SSet.{u}} (D : K ⟶ E) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D)
    (i : K _⦋0⦌) (t : X _⦋0⦌) (ht : a.app _ t = c.vertex)
    {w : Y _⦋0⦌} (k : Y.Edge w (b.app _ t))
    (hk : (k.map p).edge = ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c i).map j).edge) :
    ∃ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber a (D.app _ i)) _⦋0⦌,
      ∃ e : X.Edge v.val t, (e.map a).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c i).edge := by
  let l := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c i
  let F : (Δ[1] : SSet.{u}) ⟶ X := hsq.lift
    (SSet.yonedaEquiv.symm l.edge) (SSet.yonedaEquiv.symm k.edge) (by
      rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp]
      exact congrArg SSet.yonedaEquiv.symm hk.symm)
  have hFa : F ≫ a = SSet.yonedaEquiv.symm l.edge := hsq.lift_fst _ _ _
  have hFb : F ≫ b = SSet.yonedaEquiv.symm k.edge := hsq.lift_snd _ _ _
  have htarget : stdSimplex.δ 0 ≫ F = SSet.yonedaEquiv.symm t := by
    apply hsq.hom_ext
    · rw [Category.assoc, hFa, l.δ_zero_yonedaEquiv_symm, SSet.yonedaEquiv_symm_comp, ht]
    · rw [Category.assoc, hFb, k.δ_zero_yonedaEquiv_symm, SSet.yonedaEquiv_symm_comp]
  let v := SSet.yonedaEquiv (stdSimplex.δ 1 ≫ F)
  have hv : a.app (Opposite.op ⦋0⦌) v = D.app _ i := by
    change a.app _ (SSet.yonedaEquiv (stdSimplex.δ 1 ≫ F)) = _
    rw [← SSet.yonedaEquiv_comp, Category.assoc, hFa, l.δ_one_yonedaEquiv_symm,
      Equiv.apply_symm_apply]
  let e : X.Edge v t :=
    ⟨SSet.yonedaEquiv F, by
      change X.δ 1 (SSet.yonedaEquiv F) = v
      rw [← stdSimplex.yonedaEquiv_δ_comp],
      by
        change X.δ 0 (SSet.yonedaEquiv F) = t
        rw [← stdSimplex.yonedaEquiv_δ_comp, htarget, Equiv.apply_symm_apply]⟩
  refine ⟨⟨v, hv.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _).symm⟩, e, ?_⟩
  change a.app _ (SSet.yonedaEquiv F) = l.edge
  rw [← SSet.yonedaEquiv_comp, hFa, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
