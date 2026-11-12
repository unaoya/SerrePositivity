module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FinalHornPullbackExtension

/-!
概要：cocartesian 辺の可逆化を、その底の辺の逆像への制限で判定する。
方針：指定辺を pullback の普遍性で持ち上げ、cocartesian 性の底変換を使う。
規約：図式の全ての辺を可逆にする条件へ強めない。
使われ方：特殊辺の図式の可逆化条件から外ホーンの延長を得る。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：底の一辺の逆像で cocartesian 辺を可逆化する図式は、その辺上の元の辺も可逆化する。
方針：元の辺と区間の恒等射を組み合わせ、pullback 上の cocartesian 辺を作る。
規約：指定辺以外の底の辺に関する条件は不要。
使われ方：外ホーンの終端辺の族の可逆性。 -/
lemma diagram_inverts_cocartesian_of_edgeRestriction {P Q A D : SSet.{u}}
    {i : Q ⟶ P} {q : Q ⟶ (Δ[1] : SSet.{u})} {p : P ⟶ A}
    {j : (Δ[1] : SSet.{u}) ⟶ A} (hs : IsPullback i q p j) (H : P ⟶ D)
    (hH : ∀ t : Q _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q t →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((i ≫ H).app (Opposite.op ⦋1⦌) t)))
    (s : P _⦋1⦌) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p s)
    (hb : p.app (Opposite.op ⦋1⦌) s = SSet.yonedaEquiv j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app (Opposite.op ⦋1⦌) s)) := by
  let r : (Δ[1] : SSet.{u}) ⟶ P := SSet.yonedaEquiv.symm s
  have hr : r ≫ p = 𝟙 _ ≫ j := by
    rw [Category.id_comp]
    apply SSet.yonedaEquiv.injective
    simpa only [r, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hb
  let t := SSet.yonedaEquiv (hs.lift r (𝟙 _) hr)
  have ht : i.app (Opposite.op ⦋1⦌) t = s := by
    rw [← SSet.yonedaEquiv_comp, hs.lift_fst]
    exact SSet.yonedaEquiv.apply_symm_apply s
  have htc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q t :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_isPullback hs t (by rw [ht]; exact hc)
  have h := hH t htc
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app _ (i.app _ t))) at h
  rw [ht] at h
  exact h

/-- 概要：最後の辺の逆像で cocartesian 辺を可逆化すれば外ホーン上の図式を延長できる。
方針：元の cocartesian 辺をホーンの逆像へ持ち上げ、さらに終端辺へ制限して可逆化を確認する。
規約：最後の辺の逆像は任意の pullback 表示でよい。
使われ方：相対指数の特殊な辺の cartesian 性の幾何学的な充填。 -/
lemma exists_kanFinalHorn_extension_of_edgeRestriction (n : ℕ) {P Q E D : SSet.{u}}
    [Quasicategory D] (p : E ⟶ (Δ[n + 2] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (i : P ⟶ E) (a : P ⟶ (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}))
    (hs : IsPullback i a p (horn (n + 2) (Fin.last (n + 2))).ι)
    (k : Q ⟶ P) (q : Q ⟶ (Δ[1] : SSet.{u}))
    (ht : IsPullback k q a (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n))) (H : P ⟶ D)
    (hH : ∀ t : Q _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q t →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((k ≫ H).app (Opposite.op ⦋1⦌) t))) :
    ∃ G : E ⟶ D, i ≫ G = H := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanFinalHornPullback_extension n p i a hs H
  intro s hc hb
  apply diagram_inverts_cocartesian_of_edgeRestriction ht H hH s
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_isPullback hs s hc)
  apply Subtype.ext
  have hw := congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) s) hs.w
  exact hw.symm.trans hb

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
