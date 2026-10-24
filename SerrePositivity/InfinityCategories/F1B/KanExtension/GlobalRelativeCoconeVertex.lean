module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinFiberCocone
public import SerrePositivity.InfinityCategories.F1B.Fibrations.FiberwiseHomFiberPostcomposition

/-!
概要：局所相対余錐の頂点の二つの像を指定された大域図式の族と同定する。
方針：fiber の同型の制限・後合成との自然性を頂点で計算する。
規約：元の図式と標的の全余錐の像を厳密に保つ。
使われ方：相対 Kan の局所余錐から相対始対象の頂点を選ぶ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：局所の相対余錐の頂点は元の図式と標的の全図式の指定頂点へ写る。
方針：fiber の同型の制限・後合成との自然性と大域図式の fiber 頂点の式を合わせる。
規約：p、U と図式に充填性を仮定しない。
使われ方：指定された相対比較の標的の頂点上で局所余錐を選ぶ。 -/
lemma kanGlobalRelativeCocone_vertex_images {K C D E : SSet.{u}}
    (p : K ⟶ C) (U : D ⟶ E) (F : K ⟶ D)
    (H₀ : relativeJoin p (𝟙 C) ⟶ E) (c : C _⦋0⦌)
    (z : JoinCocone (vertexFiberι p c ≫ F))
    (hU : z.val ≫ U = (kanRelativeJoinFiberCocone p c H₀).val) :
    let x := ((kanRelativeJoinCoconeFiberIso p c D).hom.app (Opposite.op ⦋0⦌)
      (functorVertex z.val)).val
    (SerrePositivity.InfinityCategories.fiberwiseHomPre (D := D) (kanRelativeJoinInlOver p)).app (Opposite.op ⦋0⦌) x =
        (kanGlobalDiagramFamily p F).app (Opposite.op ⦋0⦌) c ∧
      (SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp (relativeJoinBaseProjection p (𝟙 C)) U).app
        (Opposite.op ⦋0⦌) x =
          (kanGlobalDiagramFamily (relativeJoinBaseProjection p (𝟙 C)) H₀).app
            (Opposite.op ⦋0⦌) c := by
  let x := (kanRelativeJoinCoconeFiberIso p c D).hom.app (Opposite.op ⦋0⦌)
    (functorVertex z.val)
  constructor
  · have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (kanRelativeJoinCoconeFiberIso_restriction (D := D) p c)
        (Opposite.op ⦋0⦌)) (functorVertex z.val)
    have hzv : (coconeRestriction (vertexFiber p c) D).app (Opposite.op ⦋0⦌)
        (functorVertex z.val) = functorVertex (vertexFiberι p c ≫ F) := by
      change functorVertex (joinInl (vertexFiber p c) Δ[0] ≫ z.val) = _
      rw [z.property]
    change (SerrePositivity.InfinityCategories.fiberwiseHomPreFiber (D := D) (kanRelativeJoinInlOver p) c).app
      (Opposite.op ⦋0⦌) x = (SerrePositivity.InfinityCategories.fiberwiseHomFiberIso p c D).hom.app
        (Opposite.op ⦋0⦌) ((coconeRestriction (vertexFiber p c) D).app
          (Opposite.op ⦋0⦌) (functorVertex z.val)) at h
    rw [hzv] at h
    exact (congrArg Subtype.val h).trans (kanGlobalDiagramFamily_fiber_vertex p F c)
  · have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (SerrePositivity.InfinityCategories.F1B.relativeJoinCoconeFiberIso_postcomp p c U)
        (Opposite.op ⦋0⦌)) (functorVertex z.val)
    change (SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcompFiber (relativeJoinBaseProjection p (𝟙 C)) U c).app
      (Opposite.op ⦋0⦌) x = (kanRelativeJoinCoconeFiberIso p c E).hom.app
        (Opposite.op ⦋0⦌) (functorVertex (z.val ≫ U)) at h
    rw [hU] at h
    exact (congrArg Subtype.val h).trans (kanRelativeJoinFiberCocone_family_vertex p c H₀)

end SerrePositivity.InfinityCategories.F1B
