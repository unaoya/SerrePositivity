module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianCancellation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianProductProjection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleCartesian
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：同じ底の辺と終点を持つ cartesian な持ち上げを垂直な可逆辺で比較する。
方針：二つの辺を最後の外ホーンとして貼り、退化した底の三角形の上で充填する。
規約：比較の向きは長辺の始点から後半の辺の始点へ。
使われ方：特殊な cartesian 輸送の保存から任意の輸送の保存を導く。

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

/-- 概要：同じ終点と底を持つ二辺は、後半の辺が cartesian なら退化した底の三角形で比較できる。
方針：最後の二次元外ホーンに二辺を貼って持ち上げる。
規約：長辺を e、後半の辺を f とする。
使われ方：cartesian な輸送の比較三角形。 -/
lemma exists_kanCartesianComparisonTriangle {E B : SSet.{u}} (p : E ⟶ B)
    (e f : (Δ[1] : SSet.{u}) ⟶ E) (hb : e ≫ p = f ≫ p)
    (ht : stdSimplex.δ (0 : Fin 2) ≫ e = stdSimplex.δ (0 : Fin 2) ≫ f)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv f)) :
    ∃ t : (Δ[2] : SSet.{u}) ⟶ E,
      stdSimplex.δ (1 : Fin 3) ≫ t = e ∧ stdSimplex.δ (0 : Fin 3) ≫ t = f ∧
      t ≫ p = stdSimplex.σ (0 : Fin 2) ≫ e ≫ p := by
  obtain ⟨a, hae, haf⟩ := horn₂₂.isPushout.exists_desc e f ht
  have h₀ : (stdSimplex.δ (0 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
      stdSimplex.σ (0 : Fin 2) = 𝟙 _ := by
    apply SSet.yonedaEquiv.injective
    decide
  have h₁ : (stdSimplex.δ (1 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
      stdSimplex.σ (0 : Fin 2) = 𝟙 _ := by
    apply SSet.yonedaEquiv.injective
    decide
  let sq : CommSq a (horn 2 2).ι p (stdSimplex.σ (0 : Fin 2) ≫ e ≫ p) := ⟨by
    apply horn₂₂.isPushout.hom_ext
    · simp only [← Category.assoc, hae, horn.ι_ι, h₁, Category.id_comp]
    · simp only [← Category.assoc, haf, horn.ι_ι, h₀, Category.id_comp]
      exact hb.symm⟩
  have hfixed : a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge 0) = SSet.yonedaEquiv f := by
    rw [← haf, SSet.yonedaEquiv_comp]
    have h : SSet.yonedaEquiv horn₂₂.ι₁₂.{u} = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge.{u} 0 := by
      apply Subtype.ext
      decide
    rw [h]
  have := hf 0 a _ hfixed sq
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · rw [← horn.ι_ι_assoc 2 1 (by decide), sq.fac_left, hae]
  · rw [← horn.ι_ι_assoc 2 0 (by decide), sq.fac_left, haf]

/-- 概要：同じ底と終点を持つ cartesian な二辺を結ぶ三角形の最初の辺は可逆。
方針：cartesian な消去則で最初の辺の cartesian 性を得て、底の定値辺で可逆性を検出する。
規約：底は quasicategory、射は inner fibration。
使われ方：特殊な cartesian 辺との比較の同値性。 -/
lemma cartesianComparison_first_isInvertible {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [InnerFibration p] (t : (Δ[2] : SSet.{u}) ⟶ E)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ t)))
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ t)))
    (e : (Δ[1] : SSet.{u}) ⟶ E)
    (hp : t ≫ p = stdSimplex.σ (0 : Fin 2) ≫ e ≫ p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ t))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isInvertibleEdge_of_isCartesianEdge p _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_first_of_second_long t p hf he)
  have h₂ : (stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
      stdSimplex.σ (0 : Fin 2) = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    apply SSet.yonedaEquiv.injective
    decide
  have hbase : (stdSimplex.δ (2 : Fin 3) ≫ t) ≫ p =
      SSet.const ((e ≫ p).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
    rw [Category.assoc, hp, ← Category.assoc, h₂, SSet.const_comp]
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      (SSet.yonedaEquiv ((stdSimplex.δ (2 : Fin 3) ≫ t) ≫ p))) := by
    rw [hbase]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.constantEdge_isInvertible _
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ t))).map
      ((truncation 2).map p)) (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
        (SSet.yonedaEquiv ((stdSimplex.δ (2 : Fin 3) ≫ t) ≫ p))) (by
      rw [SSet.yonedaEquiv_comp]
      rfl)).2 hi

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.4.1.9" (partial := component) "仮定：同じ底の辺・終点を持つ二つの Cartesian lifts と準圏の底（Lean が強い）。結論：同じ退化底三角形の比較を作り、その残る辺が invertible であると示すので「二つの lifts は equivalent」という明記された assertion に一致。全ての lifts の相対 slice での terminality は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianComparison_first_isInvertible
attribute [cite HTT "2.4.1.9" (partial := component) "仮定：同じ底の辺・終点を持つ二つの Cartesian lifts と準圏の底（Lean が強い）。結論：同じ退化底三角形の比較を作り、その残る辺が invertible であると示すので「二つの lifts は equivalent」という明記された assertion に一致。全ての lifts の相対 slice での terminality は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanCartesianComparisonTriangle
