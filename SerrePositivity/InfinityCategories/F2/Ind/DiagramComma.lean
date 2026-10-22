module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramYoneda
public import SerrePositivity.InfinityCategories.F2.Ind.CommaFamily

/-!
概要：指定された元の Ind 図式への、全 coherent Yoneda 表示の comma。
方針：全図式版 Yoneda と指定頂点の slice を厳密に引き戻す。
規約：これは大きい添字。小ささ・filtered 性・普遍性は未主張。
使われ方：有限図式全体の filtered 表示の小さい模型への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C)

/-- 元の図式への全 coherent 変換を持つ、元の C の全図式の添字。 -/
abbrev diagramComma : SSet.{u + 1} :=
  leftKanShape (diagramYoneda κ K C) (functorVertex D)

/-- 元の C の全図式への、同じ comma の第一射影。 -/
abbrev diagramCommaProjection : diagramComma κ D ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj ((ihom K).obj C) :=
  leftKanProjection (diagramYoneda κ K C) (functorVertex D)

instance diagramCommaProjection_rightFibration : RightFibration (diagramCommaProjection κ D) :=
  ⟨rightFibrations.pullback_fst _ _ (RightFibration.mem (p :=
    sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex D))))⟩

instance diagramComma_quasicategory : Quasicategory (diagramComma κ D) :=
  quasicategory_of_innerFibration (diagramCommaProjection κ D)

/-- 表示族から、指定された同じ全 Ind 図式への元の全余錐。 -/
def diagramCommaCocone :
    JoinCocone (diagramCommaProjection κ D ≫ diagramYoneda κ K C) :=
  ⟨sliceOverUncurry (pullback.snd (diagramYoneda κ K C)
    (sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex D)))), by
      rw [sliceOverUncurry_projection, ← pullback.condition]⟩

/-- 標準の全余錐の頂点は、元の指定全図式そのもの。 -/
lemma diagramCommaCocone_vertex : (diagramCommaCocone κ D).vertex = functorVertex D := by
  rw [JoinCocone.vertex_eq]
  change SSet.yonedaEquiv (joinInr _ _ ≫ sliceOverUncurry _) = _
  rw [sliceOverUncurry_fixed, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.F2.Ind
