module

public import SerrePositivity.InfinityCategories.F1.Joins.JoinDiagramRelativeRetraction

/-!
概要：部分族が既に通常の join 図式である fat join 図式の相対的な回収。
方針：部分族と両端を保つ関手単体集合のレトラクションを図式の頂点で評価する。
規約：回収した図式は部分族と両端に厳密に一致し、元の全図式との等式は要求しない。
使われ方：Kerodon §4.6.6、区間模型から pinched 模型への厳密な左逆。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：部分族上の通常の join 図式は、全 fat join 図式の両端を保って延長できる。
方針：相対レトラクションを全図式で評価し、部分族の厳密な左逆の式を使う。
規約：i は単射、K は任意で非空性は不要。
使われ方：Kerodon §4.6.6、pinched 写像空間上で恒等となる逆の構成。 -/
lemma exists_joinDiagram_relative_extension {A B K X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) [Mono i] (F : fatJoin B K ⟶ X) (G : join A K ⟶ X)
    (hFG : fatJoinMap i (𝟙 K) ≫ F = fatJoinComparison A K ≫ G) :
    ∃ H : join B K ⟶ X,
      joinMap i (𝟙 K) ≫ H = G ∧
      joinInl B K ≫ H = fatJoinInl B K ≫ F ∧
      joinInr B K ≫ H = fatJoinInr B K ≫ F := by
  obtain ⟨rA, rB, hrA, _, hi, hl, hr⟩ :=
    exists_pre_fatJoinComparison_relative_retraction i K X
  obtain ⟨H, hH⟩ := (functorVertexEquiv (join B K) X).surjective
    (rB.app (Opposite.op ⦋0⦌) (functorVertex F))
  refine ⟨H, ?_, ?_, ?_⟩
  · have hi' := ConcreteCategory.congr_hom (NatTrans.congr_app hi (Opposite.op ⦋0⦌))
      (functorVertex F)
    change ((pre (joinMap i (𝟙 K))).app X).app (Opposite.op ⦋0⦌)
        (rB.app (Opposite.op ⦋0⦌) (functorVertex F)) =
      rA.app (Opposite.op ⦋0⦌) (functorVertex (fatJoinMap i (𝟙 K) ≫ F)) at hi'
    rw [← hH, hFG] at hi'
    have hrA' := ConcreteCategory.congr_hom
      (NatTrans.congr_app hrA (Opposite.op ⦋0⦌)) (functorVertex G)
    change rA.app (Opposite.op ⦋0⦌) (functorVertex (fatJoinComparison A K ≫ G)) =
      functorVertex G at hrA'
    exact (functorVertexEquiv (join A K) X).injective (hi'.trans hrA')
  · have hl' := ConcreteCategory.congr_hom (NatTrans.congr_app hl (Opposite.op ⦋0⦌))
      (functorVertex F)
    change ((pre (joinInl B K)).app X).app (Opposite.op ⦋0⦌)
        (rB.app (Opposite.op ⦋0⦌) (functorVertex F)) =
      functorVertex (fatJoinInl B K ≫ F) at hl'
    rw [← hH] at hl'
    exact (functorVertexEquiv B X).injective hl'
  · have hr' := ConcreteCategory.congr_hom (NatTrans.congr_app hr (Opposite.op ⦋0⦌))
      (functorVertex F)
    change ((pre (joinInr B K)).app X).app (Opposite.op ⦋0⦌)
        (rB.app (Opposite.op ⦋0⦌) (functorVertex F)) =
      functorVertex (fatJoinInr B K ≫ F) at hr'
    rw [← hH] at hr'
    exact (functorVertexEquiv K X).injective hr'

end SerrePositivity.InfinityCategories
