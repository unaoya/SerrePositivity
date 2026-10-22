module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationSmallDiagram

/-!
概要：小さい C 図式の Yoneda 像への全余錐を、元の指定図式 D のまま回収する。
方針：標準区間の宇宙同型で全余錐を後合成し、頂点の逆比較を消去する。
規約：元の全図式と指定頂点を厳密に保持。使われ方：元の図式 comma への帰還。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
  (V : IndArrowInterpolationData κ D q)

/-- 同じ小さい区間の持ち上げで表示した、補間の全余錐の射。 -/
def indArrowInterpolationLiftedCoconeMap :
    join ((SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}))) Δ[0] ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}))).obj (IndInfinity κ C) :=
  indArrowInterpolationCoherentCoconeMap V ≫
    (pre (HomotopyLimits.uliftStdSimplexIso.{u, u + 1} 1).hom).app (IndInfinity κ C)

/-- 同じ余錐の元の図式側は、小さい C 図式の元の Yoneda 像そのもの。 -/
lemma indArrowInterpolationLiftedCoconeMap_old :
    joinInl ((SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}))) Δ[0] ≫
      indArrowInterpolationLiftedCoconeMap V =
        (SSet.uliftFunctor.{u + 1, u}).map (indArrowInterpolationSmallDiagram V) ≫
          diagramYoneda κ (Δ[1] : SSet.{u}) C := by
  rw [indArrowInterpolationLiftedCoconeMap, ← Category.assoc,
    indArrowInterpolationCoherentCoconeMap_old,
    indArrowInterpolationSmallDiagram_yoneda, Category.assoc]

/-- 同じ余錐の全頂点写像は、元の指定全図式 D の頂点写像そのもの。 -/
lemma indArrowInterpolationLiftedCoconeMap_tip :
    joinInr ((SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}))) Δ[0] ≫
      indArrowInterpolationLiftedCoconeMap V = SSet.yonedaEquiv.symm (functorVertex D) := by
  rw [indArrowInterpolationLiftedCoconeMap, ← Category.assoc,
    indArrowInterpolationCoherentCoconeMap_tip, SSet.yonedaEquiv_symm_comp]
  congr 1

/-- 小さい元の C 図式の Yoneda 像への、実際の全 coherent 余錐。 -/
def indArrowInterpolationLiftedCocone :
    JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map (indArrowInterpolationSmallDiagram V) ≫
      diagramYoneda κ (Δ[1] : SSet.{u}) C) :=
  ⟨indArrowInterpolationLiftedCoconeMap V, indArrowInterpolationLiftedCoconeMap_old V⟩

/-- 頂点は元の指定図式そのもの。 -/
lemma indArrowInterpolationLiftedCocone_vertex :
    (indArrowInterpolationLiftedCocone V).vertex = functorVertex D := by
  rw [JoinCocone.vertex_eq]
  change SSet.yonedaEquiv (joinInr _ _ ≫ indArrowInterpolationLiftedCoconeMap V) = _
  rw [indArrowInterpolationLiftedCoconeMap_tip, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.F2.Ind
