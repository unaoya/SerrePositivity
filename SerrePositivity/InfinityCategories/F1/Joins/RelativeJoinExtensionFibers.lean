module

public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinEndpointFibers
public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinCylinderIntervalExtension
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor

/-!
概要：区間上の relative join の比較射が両端 fiber に誘導する射の同定。
方針：元の因子との同型を通して包含後に比較し、同型の前合成を同値条件から消去する。
規約：延長 G の存在と底の可換性は明示的なデータとして受け取る。
使われ方：Kerodon Theorem 5.2.4.1、fiber ごとの同値判定への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：延長の零 fiber の射は、指定した prism の始点の比較に一致する。
方針：零 fiber 同型の包含後の式と prism の始点の式を使う。
規約：z は始点の射の指定した fiber への持ち上げ。
使われ方：Kerodon Theorem 5.2.4.1、第一条件を延長の零 fiber に移す。 -/
lemma relativeJoin_extension_zeroFiber_eq {X Y E : SSet.{u}} (f : X ⟶ Y)
    (p : E ⟶ (Δ[1] : SSet.{u})) (G : relativeJoin f (𝟙 Y) ⟶ E)
    (hG : G ≫ p = relativeJoinProjection f (𝟙 Y))
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (hH : relativeJoinPrism f ≫ G = H)
    (z : X ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hz : z ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = prismEndpoint 0 X ≫ H) :
    (relativeJoinZeroFiberIso f (𝟙 Y)).hom ≫
      vertexFiberMap (relativeJoinProjection f (𝟙 Y)) p G hG (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        z := by
  apply vertexFiber_hom_ext
  rw [Category.assoc, relativeJoinZeroFiberIso_vertexFiberMap_ι, hz,
    ← relativeJoinPrism_zero, Category.assoc, hH]

/-- 概要：延長の一 fiber の射は、指定した終域部分の比較に一致する。
方針：一 fiber 同型の包含後の式と右包含の制限の等式を使う。
規約：z は終域部分の射の指定した fiber への持ち上げ。
使われ方：Kerodon Theorem 5.2.4.1、第二条件を延長の一 fiber に移す。 -/
lemma relativeJoin_extension_oneFiber_eq {X Y E : SSet.{u}} (f : X ⟶ Y)
    (p : E ⟶ (Δ[1] : SSet.{u})) (G : relativeJoin f (𝟙 Y) ⟶ E)
    (hG : G ≫ p = relativeJoinProjection f (𝟙 Y))
    (g : Y ⟶ E) (hg : relativeJoinInr f (𝟙 Y) ≫ G = g)
    (z : Y ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hz : z ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g) :
    (relativeJoinOneFiberIso f (𝟙 Y)).hom ≫
      vertexFiberMap (relativeJoinProjection f (𝟙 Y)) p G hG (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        z := by
  apply vertexFiber_hom_ext
  rw [Category.assoc, relativeJoinOneFiberIso_vertexFiberMap_ι, hz, hg]

/-- 概要：延長の零 fiber の前合成の同値条件は prism の始点の比較の条件と同値。
方針：零 fiber 同型を前合成から消去し、始点の比較との等式を使う。
規約：両端の単体集合の quasicategory 性は要求しない。
使われ方：Kerodon Theorem 5.2.4.1、第一条件による零 fiber の判定。 -/
lemma relativeJoin_extension_zeroFiber_isPrecompositionEquivalence_iff
    {X Y E : SSet.{u}} (f : X ⟶ Y) (p : E ⟶ (Δ[1] : SSet.{u}))
    (G : relativeJoin f (𝟙 Y) ⟶ E) (hG : G ≫ p = relativeJoinProjection f (𝟙 Y))
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (hH : relativeJoinPrism f ≫ G = H)
    (z : X ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hz : z ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = prismEndpoint 0 X ≫ H) :
    IsPrecompositionEquivalence
      (vertexFiberMap (relativeJoinProjection f (𝟙 Y)) p G hG (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ↔
        IsPrecompositionEquivalence z := by
  have hi := isPrecompositionEquivalence_of_iso (relativeJoinZeroFiberIso f (𝟙 Y))
  have he := relativeJoin_extension_zeroFiber_eq f p G hG H hH z hz
  constructor
  · intro hm
    have hc := hi.comp hm
    rwa [he] at hc
  · intro hm
    apply hi.cancel_left
    rwa [he]

/-- 概要：延長の一 fiber の前合成の同値条件は終域部分の比較の条件と同値。
方針：一 fiber 同型を前合成から消去し、終域部分の比較との等式を使う。
規約：両端の単体集合の quasicategory 性は要求しない。
使われ方：Kerodon Theorem 5.2.4.1、第二条件による一 fiber の判定。 -/
lemma relativeJoin_extension_oneFiber_isPrecompositionEquivalence_iff
    {X Y E : SSet.{u}} (f : X ⟶ Y) (p : E ⟶ (Δ[1] : SSet.{u}))
    (G : relativeJoin f (𝟙 Y) ⟶ E) (hG : G ≫ p = relativeJoinProjection f (𝟙 Y))
    (g : Y ⟶ E) (hg : relativeJoinInr f (𝟙 Y) ≫ G = g)
    (z : Y ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hz : z ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g) :
    IsPrecompositionEquivalence
      (vertexFiberMap (relativeJoinProjection f (𝟙 Y)) p G hG (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ↔
        IsPrecompositionEquivalence z := by
  have hi := isPrecompositionEquivalence_of_iso (relativeJoinOneFiberIso f (𝟙 Y))
  have he := relativeJoin_extension_oneFiber_eq f p G hG g hg z hz
  constructor
  · intro hm
    have hc := hi.comp hm
    rwa [he] at hc
  · intro hm
    apply hi.cancel_left
    rwa [he]

end SerrePositivity.InfinityCategories
