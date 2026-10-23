module

public import SerrePositivity.InfinityCategories.F1.JoinDiagramRightRelativeRetraction

/-!
概要：部分族が既に通常の join 図式である fat join 図式の相対的な回収。
方針：右側の部分族と両端を保つ関手単体集合のレトラクションを図式の頂点で評価する。
規約：回収した図式は部分族と両端に厳密に一致し、元の全図式との等式は要求しない。
使われ方：Kerodon §4.6.6、区間模型から pinched 模型への厳密な左逆。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：部分族上の通常の join 図式は、全 fat join 図式の両端を保って延長できる。
方針：相対レトラクションを全図式で評価し、部分族の厳密な左逆の式を使う。
規約：i は単射、K は任意で非空性は不要。
使われ方：Kerodon §4.6.6、pinched 写像空間上で恒等となる逆の構成。 -/
lemma exists_joinDiagram_right_relative_extension {A B K X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) [Mono i] (F : fatJoin K B ⟶ X) (G : join K A ⟶ X)
    (hFG : fatJoinMap (𝟙 K) i ≫ F = fatJoinComparison K A ≫ G) :
    ∃ H : join K B ⟶ X,
      joinMap (𝟙 K) i ≫ H = G ∧
      joinInl K B ≫ H = fatJoinInl K B ≫ F ∧
      joinInr K B ≫ H = fatJoinInr K B ≫ F := by
  obtain ⟨rA, rB, hrA, _, hi, hr, hl⟩ :=
    exists_pre_fatJoinComparison_right_relative_retraction i K X
  obtain ⟨H, hH⟩ := (functorVertexEquiv (join K B) X).surjective
    (rB.app (Opposite.op ⦋0⦌) (functorVertex F))
  refine ⟨H, ?_, ?_, ?_⟩
  · have hi' := ConcreteCategory.congr_hom (NatTrans.congr_app hi (Opposite.op ⦋0⦌))
      (functorVertex F)
    change ((pre (joinMap (𝟙 K) i)).app X).app (Opposite.op ⦋0⦌)
        (rB.app (Opposite.op ⦋0⦌) (functorVertex F)) =
      rA.app (Opposite.op ⦋0⦌) (functorVertex (fatJoinMap (𝟙 K) i ≫ F)) at hi'
    rw [← hH, hFG] at hi'
    have hrA' := ConcreteCategory.congr_hom
      (NatTrans.congr_app hrA (Opposite.op ⦋0⦌)) (functorVertex G)
    change rA.app (Opposite.op ⦋0⦌) (functorVertex (fatJoinComparison K A ≫ G)) =
      functorVertex G at hrA'
    exact (functorVertexEquiv (join K A) X).injective (hi'.trans hrA')
  · have hl' := ConcreteCategory.congr_hom (NatTrans.congr_app hl (Opposite.op ⦋0⦌))
      (functorVertex F)
    change ((pre (joinInl K B)).app X).app (Opposite.op ⦋0⦌)
        (rB.app (Opposite.op ⦋0⦌) (functorVertex F)) =
      functorVertex (fatJoinInl K B ≫ F) at hl'
    rw [← hH] at hl'
    exact (functorVertexEquiv K X).injective hl'
  · have hr' := ConcreteCategory.congr_hom (NatTrans.congr_app hr (Opposite.op ⦋0⦌))
      (functorVertex F)
    change ((pre (joinInr K B)).app X).app (Opposite.op ⦋0⦌)
        (rB.app (Opposite.op ⦋0⦌) (functorVertex F)) =
      functorVertex (fatJoinInr K B ≫ F) at hr'
    rw [← hH] at hr'
    exact (functorVertexEquiv B X).injective hr'

end SerrePositivity.InfinityCategories.F2
