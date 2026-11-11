module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianComparison

/-!
概要：終点指定の cartesian な持ち上げの保存からすべての cartesian 辺の保存を導く。
方針：任意の辺を保存される持ち上げと三角形で比較し、垂直な可逆辺を使う。
規約：始域・標的・二つの底は quasicategory、両射影は inner fibration。
使われ方：相対 join の図式の制限と任意の cartesian 輸送との両立。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：同じ終点と底の辺を持つ保存される輸送との比較により cartesian 性を保存できる。
方針：比較三角形の最初の辺を可逆にし、その像と後半の cartesian 辺を合成する。
規約：二つの射影の底は異なってよく、u は任意の単体集合の射。
使われ方：構成した特殊な輸送の保存を一般の辺へ拡張する。 -/
lemma cartesianEdge_map_of_comparison {E F B C : SSet.{u}}
    [Quasicategory E] [Quasicategory F] [Quasicategory B] [Quasicategory C]
    (p : E ⟶ B) (q : F ⟶ C) [InnerFibration p] [InnerFibration q]
    (u : E ⟶ F) (e f : (Δ[1] : SSet.{u}) ⟶ E)
    (hb : e ≫ p = f ≫ p)
    (ht : stdSimplex.δ (0 : Fin 2) ≫ e = stdSimplex.δ (0 : Fin 2) ≫ f)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv e))
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv f))
    (hfu : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge q (SSet.yonedaEquiv (f ≫ u))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge q (SSet.yonedaEquiv (e ≫ u)) := by
  obtain ⟨t, hte, htf, htp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanCartesianComparisonTriangle p e f hb ht hf
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianComparison_first_isInvertible p t (by rw [hte]; exact he)
    (by rw [htf]; exact hf) e htp
  have him := hi.map u
  have hfirst : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge q
      (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ (t ≫ u))) := by
    have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_of_isInvertibleEdge q _ him
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge q
      (u.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ t))) at hc
    simpa only [← Category.assoc, SSet.yonedaEquiv_comp] using hc
  have hsecond : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge q
      (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ (t ≫ u))) := by
    rw [← Category.assoc, htf]
    exact hfu
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_longEdge (t ≫ u) q hfirst hsecond
  rw [← Category.assoc, hte] at h
  exact h

/-- 概要：終点指定の保存される cartesian な持ち上げがあればすべての cartesian 辺を保存する。
方針：任意の辺の終点に対する指定持ち上げを選び、比較による保存を適用する。
規約：持ち上げの存在を仮定し、選択した cleavage 自体はデータに持たない。
使われ方：相対指数の特殊な図式の延長から cartesian 関手の性質を得る。 -/
lemma cartesianEdges_preserved_of_target_lifts {E F B C : SSet.{u}}
    [Quasicategory E] [Quasicategory F] [Quasicategory B] [Quasicategory C]
    (p : E ⟶ B) (q : F ⟶ C) [InnerFibration p] [InnerFibration q]
    (u : E ⟶ F)
    (hlift : ∀ (x : E _⦋0⦌) (b : (Δ[1] : SSet.{u}) ⟶ B),
      stdSimplex.δ (0 : Fin 2) ≫ b = SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) x) →
      ∃ f : (Δ[1] : SSet.{u}) ⟶ E,
        stdSimplex.δ (0 : Fin 2) ≫ f = SSet.yonedaEquiv.symm x ∧ f ≫ p = b ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv f) ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge q (SSet.yonedaEquiv (f ≫ u)))
    (e : E _⦋1⦌) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge q (u.app (Opposite.op ⦋1⦌) e) := by
  let a : (Δ[1] : SSet.{u}) ⟶ E := SSet.yonedaEquiv.symm e
  let x := E.δ 0 e
  have hx : stdSimplex.δ (0 : Fin 2) ≫ a = SSet.yonedaEquiv.symm x := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
  obtain ⟨f, hfx, hfp, hfc, hfu⟩ := hlift x (a ≫ p) (by
    rw [← Category.assoc, hx, SSet.yonedaEquiv_symm_comp])
  have h := cartesianEdge_map_of_comparison p q u a f hfp.symm (hx.trans hfx.symm)
    (by simpa only [a, Equiv.apply_symm_apply] using he) hfc hfu
  simpa only [SSet.yonedaEquiv_comp, a, Equiv.apply_symm_apply] using h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
