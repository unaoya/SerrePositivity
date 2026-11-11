module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-! # ホモトピーの前合成と関手辺

概要：図式の形状に沿うホモトピーの制限は関手辺の前合成と一致する。
方針：curry と uncurry の前合成の式で一次単体を照合する。
規約：端点つきの辺の等号として述べる。
使われ方：S4 の普遍余錐と四角形の比較を照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：図式の形状の射に沿ってホモトピーを制限する。
方針：区間との積で前合成する。
規約：端点は制限した二つの図式。使われ方：余錐を基底の図式へ制限する。 -/
def stableHomotopyPrecomp {A B X : SSet.{u}} (i : A ⟶ B) {F G : B ⟶ X}
    (H : SSet.Homotopy F G) : SSet.Homotopy (i ≫ F) (i ≫ G) where
  h := (i ▷ (Δ[1] : SSet.{u})) ≫ H.h
  h₀ := by
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, H.h₀]
    rfl
  h₁ := by
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, H.h₁]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 概要：ホモトピーを制限して得た関手辺は、元の関手辺の前合成による像である。
方針：uncurry の前合成則で辺の一次単体を照合する。
規約：quasicategory 性は不要。使われ方：制限した h の類の計算。 -/
lemma functorEdgeOfSimplicialHomotopy_precomp {A B X : SSet.{u}} (i : A ⟶ B)
    {F G : B ⟶ X} (H : SSet.Homotopy F G) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).map ((truncation 2).map ((pre i).app X)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (stableHomotopyPrecomp i H) := by
  have hc : curry H.h ≫ (pre i).app X = curry ((i ▷ (Δ[1] : SSet.{u})) ≫ H.h) := by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
  apply SSet.Truncated.Edge.ext
  change ((pre i).app X).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry H.h)) =
    SSet.yonedaEquiv (curry ((i ▷ (Δ[1] : SSet.{u})) ≫ H.h))
  rw [← SSet.yonedaEquiv_comp, hc]

/-- 概要：制限したホモトピーの h の類は前合成関手による元の類の像である。
方針：端点つき辺の前合成の等号に homMk を適用する。
規約：quasicategory 性は不要。使われ方：余錐比較の制限。 -/
lemma homMk_functorEdge_precomp {A B X : SSet.{u}} (i : A ⟶ B)
    {F G : B ⟶ X} (H : SSet.Homotopy F G) :
    (hoFunctor.map ((pre i).app X)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) =
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (stableHomotopyPrecomp i H)) := by
  exact congrArg SSet.Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy_precomp i H)

/-- 概要：形状の同型とその逆による二度の制限は元の関手辺を与える。
方針：区間との積の合成をまとめ、同型の逆合成を消す。
規約：始めに同型の順方向で制限する。使われ方：余錐表示から四角形に戻す。 -/
lemma homMk_functorEdge_precomp_inv_hom_arrow {A B X : SSet.{u}} (e : A ≅ B)
    {F G : B ⟶ X} (H : SSet.Homotopy F G) :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (stableHomotopyPrecomp e.inv
        (stableHomotopyPrecomp e.hom H)))) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) := by
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  change SSet.yonedaEquiv (curry ((e.inv ▷ (Δ[1] : SSet.{u})) ≫
    ((e.hom ▷ (Δ[1] : SSet.{u})) ≫ H.h))) = SSet.yonedaEquiv (curry H.h)
  rw [← Category.assoc, ← comp_whiskerRight, e.inv_hom_id, id_whiskerRight, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
