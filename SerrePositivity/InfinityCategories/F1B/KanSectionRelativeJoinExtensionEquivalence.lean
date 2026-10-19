module

public import SerrePositivity.InfinityCategories.F1B.KanSectionCocartesianCrossingComparison
public import SerrePositivity.InfinityCategories.F1B.KanSectionRelativeJoinCocartesianFibration
public import SerrePositivity.InfinityCategories.F1.RelativeJoinExtensionFibers

/-!
概要：相対 join の標準 prism を使う区間上の延長の同値判定。
方針：零 fiber の各頂点で標準垂直辺を選び、両端の比較と保存される lift の判定を使う。
規約：両因子と標的は quasicategory。
使われ方：Kerodon Theorem 5.2.4.1、相対 join を介した写像円柱の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.KanSection

attribute [local instance] vertexFiber_quasicategory_of_innerFibration

/-- 概要：標準 prism の像の垂直辺が cocartesian なら、零 fiber の各頂点で保存される lift が得られる。
方針：零 fiber を左因子で表示し、指定頂点を固定した標準垂直辺を使う。
規約：係数 Y は quasicategory、像側の射影 p の充填性は要求しない。
使われ方：Kerodon Theorem 5.2.4.1、区間上の同値判定の選択 lift の条件。 -/
lemma relativeJoin_extension_preserved_lift {X Y E : SSet.{u}} [Quasicategory Y]
    (f : X ⟶ Y) (p : E ⟶ (Δ[1] : SSet.{u})) (G : relativeJoin f (𝟙 Y) ⟶ E)
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (hH : relativeJoinPrism f ≫ G = H)
    (hc : ∀ x : X _⦋0⦌, IsCocartesianEdge p (prismVerticalSimplex H x))
    (x : (relativeJoin f (𝟙 Y)) _⦋0⦌)
    (hx : (relativeJoinProjection f (𝟙 Y)).app (Opposite.op ⦋0⦌) x =
      stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :
    ∃ e : (Δ[1] : SSet.{u}) ⟶ relativeJoin f (𝟙 Y),
      stdSimplex.δ 1 ≫ e = SSet.yonedaEquiv.symm x ∧
      e ≫ relativeJoinProjection f (𝟙 Y) = 𝟙 Δ[1] ∧
      IsCocartesianEdge (relativeJoinProjection f (𝟙 Y)) (SSet.yonedaEquiv e) ∧
      IsCocartesianEdge p (SSet.yonedaEquiv (e ≫ G)) := by
  obtain ⟨y, hy⟩ := relativeJoin_vertex_inl_of_projection_zero f (𝟙 Y) x hx
  let k : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ X := lift (𝟙 Δ[1]) (SSet.const y)
  let e := k ≫ relativeJoinPrism f
  have hk : stdSimplex.δ (1 : Fin 2) ≫ k = SSet.yonedaEquiv.symm y ≫ prismEndpoint 0 X := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [k, prismEndpoint, Category.assoc, lift_fst, Category.comp_id,
        SSet.comp_const, stdSimplex.δ_one_eq_const]
    · simp only [k, prismEndpoint, Category.assoc, lift_snd, Category.comp_id,
        SSet.comp_const, SSet.yonedaEquiv_symm_zero]
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · change (stdSimplex.δ 1 ≫ k) ≫ relativeJoinPrism f = SSet.yonedaEquiv.symm x
    rw [hk, Category.assoc, relativeJoinPrism_zero, SSet.yonedaEquiv_symm_comp, hy]
  · change k ≫ relativeJoinPrism f ≫ relativeJoinProjection f (𝟙 Y) = 𝟙 Δ[1]
    rw [relativeJoinPrism_projection]
    exact lift_fst _ _
  · change IsCocartesianEdge (relativeJoinProjection f (𝟙 Y))
      (prismVerticalSimplex (relativeJoinPrism f) y)
    exact relativeJoinPrism_vertical_isCocartesian f y
  · change IsCocartesianEdge p (SSet.yonedaEquiv (k ≫ relativeJoinPrism f ≫ G))
    rw [hH]
    exact hc y

/-- 概要：両端で同値かつ標準垂直辺を cocartesian に送る相対 join の延長は同値。
方針：両端の比較を誘導された fiber の同値に移し、保存される標準 lift の判定を適用する。
規約：因子 X・Y と標的 E は quasicategory。
使われ方：Kerodon Theorem 5.2.4.1、全空間の比較の相対 join の段階。 -/
lemma relativeJoin_extension_isQCatEquivalence {X Y E : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory E] (f : X ⟶ Y)
    (p : E ⟶ (Δ[1] : SSet.{u}))
    (G : relativeJoin f (𝟙 Y) ⟶ E) (hG : G ≫ p = relativeJoinProjection f (𝟙 Y))
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (hH : relativeJoinPrism f ≫ G = H)
    (g : Y ⟶ E) (hg : relativeJoinInr f (𝟙 Y) ≫ G = g)
    (z0 : X ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hz0 : z0 ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = prismEndpoint 0 X ≫ H)
    (z1 : Y ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hz1 : z1 ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g)
    (he0 : IsPrecompositionEquivalence z0) (he1 : IsPrecompositionEquivalence z1)
    (hc : ∀ x : X _⦋0⦌, IsCocartesianEdge p (prismVerticalSimplex H x)) :
    IsQCatEquivalence G := by
  apply isQCatEquivalence_over_interval_of_endpoint_fibers_of_cocartesian_lifts
    (relativeJoinProjection f (𝟙 Y)) p G hG
  · exact ((relativeJoin_extension_zeroFiber_isPrecompositionEquivalence_iff
      f p G hG H hH z0 hz0).mpr he0).isQCatEquivalence
  · exact ((relativeJoin_extension_oneFiber_isPrecompositionEquivalence_iff
      f p G hG g hg z1 hz1).mpr he1).isQCatEquivalence
  · exact relativeJoin_extension_preserved_lift f p G H hH hc

end SerrePositivity.InfinityCategories.KanSection
