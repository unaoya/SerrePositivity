module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CrossingComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCocartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinExtensionFibers

/-!
概要：相対 join の標準 prism を使う区間上の延長の同値判定。
方針：零 fiber の各頂点で標準垂直辺を選び、両端の比較と保存される lift の判定を使う。
規約：両因子と標的は quasicategory。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、相対 join を介した写像円柱の比較。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiber_quasicategory_of_innerFibration

/-- 概要：標準 prism の像の垂直辺が cocartesian なら、零 fiber の各頂点で保存される lift が得られる。
方針：零 fiber を左因子で表示し、指定頂点を固定した標準垂直辺を使う。
規約：係数 Y は quasicategory、像側の射影 p の充填性は要求しない。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、区間上の同値判定の選択 lift の条件。 -/
lemma relativeJoin_extension_preserved_lift {X Y E : SSet.{u}} [Quasicategory Y]
    (f : X ⟶ Y) (p : E ⟶ (Δ[1] : SSet.{u})) (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 Y) ⟶ E)
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f ≫ G = H)
    (hc : ∀ x : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismVerticalSimplex H x))
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 Y)) _⦋0⦌)
    (hx : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 Y)).app (Opposite.op ⦋0⦌) x =
      stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :
    ∃ e : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 Y),
      stdSimplex.δ 1 ≫ e = SSet.yonedaEquiv.symm x ∧
      e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 Y) = 𝟙 Δ[1] ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 Y)) (SSet.yonedaEquiv e) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (SSet.yonedaEquiv (e ≫ G)) := by
  obtain ⟨y, hy⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_vertex_inl_of_projection_zero f (𝟙 Y) x hx
  let k : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ X := lift (𝟙 Δ[1]) (SSet.const y)
  let e := k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f
  have hk : stdSimplex.δ (1 : Fin 2) ≫ k = SSet.yonedaEquiv.symm y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 X := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [k, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, Category.assoc, lift_fst, Category.comp_id,
        SSet.comp_const, stdSimplex.δ_one_eq_const]
    · simp only [k, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, Category.assoc, lift_snd, Category.comp_id,
        SSet.comp_const, SSet.yonedaEquiv_symm_zero]
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · change (stdSimplex.δ 1 ≫ k) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f = SSet.yonedaEquiv.symm x
    rw [hk, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_zero, SSet.yonedaEquiv_symm_comp, hy]
  · change k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 Y) = 𝟙 Δ[1]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_projection]
    exact lift_fst _ _
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismVerticalSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f) y)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_vertical_isCocartesian f y
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (SSet.yonedaEquiv (k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f ≫ G))
    rw [hH]
    exact hc y

/-- 概要：両端で同値かつ標準垂直辺を cocartesian に送る相対 join の延長は同値。
方針：両端の比較を誘導された fiber の同値に移し、保存される標準 lift の判定を適用する。
規約：因子 X・Y と標的 E は quasicategory。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、全空間の比較の相対 join の段階。 -/
lemma relativeJoin_extension_isQCatEquivalence {X Y E : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory E] (f : X ⟶ Y)
    (p : E ⟶ (Δ[1] : SSet.{u}))
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 Y) ⟶ E) (hG : G ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 Y))
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f ≫ G = H)
    (g : Y ⟶ E) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr f (𝟙 Y) ≫ G = g)
    (z0 : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hz0 : z0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 X ≫ H)
    (z1 : Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hz1 : z1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g)
    (he0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence z0) (he1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence z1)
    (hc : ∀ x : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismVerticalSimplex H x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence G := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isQCatEquivalence_over_interval_of_endpoint_fibers_of_cocartesian_lifts
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 Y)) p G hG
  · exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_extension_zeroFiber_isPrecompositionEquivalence_iff
      f p G hG H hH z0 hz0).mpr he0).isQCatEquivalence
  · exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_extension_oneFiber_isPrecompositionEquivalence_iff
      f p G hG g hg z1 hz1).mpr he1).isQCatEquivalence
  · exact relativeJoin_extension_preserved_lift f p G H hH hc

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
