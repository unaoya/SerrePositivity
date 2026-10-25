module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorVertexConeReindex
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ColimitCoconeCompletion
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeConeFamilies

/-!
概要：実余錐族の頂点と下方図式を、全関手圏での評価・制限と厳密に同定する。
方針：全関手の頂点表示を往復し、Yoneda の合成式を使う。
規約：同型な代表を選ばず、元の指定図式と頂点を保持する。
使われ方：Ind 像の余極限閉性の、全余錐族による組み立て。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization

/-- 関手頂点を読み戻した実余錐の頂点は、元の頂点評価そのもの。 -/
lemma functorVertexCocone_apex {K Y : SSet.{u}}
    (v : ((ihom (join K (Δ[0] : SSet.{u}))).obj Y) _⦋0⦌) :
    (F2.functorVertexCocone v).vertex =
      (evaluateFunctorAt (SSet.yonedaEquiv (joinInr K (Δ[0] : SSet.{u})))).app _ v := by
  let F := (functorVertexEquiv _ Y).symm v
  have hv : functorVertex F = v := (functorVertexEquiv _ Y).apply_symm_apply v
  rw [← hv, evaluateFunctorAt_functorVertex]
  change SSet.yonedaEquiv (joinInr K Δ[0] ≫ F) = _
  exact SSet.yonedaEquiv_comp _ _

/-- 実余錐族の各頂点は、同じ族の頂点評価で計算できる。 -/
lemma kanCoconeFamilyAt_apex {A K Y : SSet.{u}}
    (p : A ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj Y) (a : A _⦋0⦌) :
    (kanCoconeFamilyAt p a).vertex =
      (p ≫ evaluateFunctorAt (SSet.yonedaEquiv (joinInr K (Δ[0] : SSet.{u})))).app _ a :=
  functorVertexCocone_apex (p.app _ a)

/-- 実余錐族の下方制限は、指定した元の全図式族の同じ頂点である。 -/
lemma kanCoconeFamilyAt_diagram {A K Y : SSet.{u}}
    (p : A ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj Y)
    (R : A ⟶ (ihom K).obj Y) (hp : p ≫ coconeRestriction K Y = R)
    (a : A _⦋0⦌) :
    joinInl K Δ[0] ≫ (kanCoconeFamilyAt p a).val =
      (functorVertexEquiv K Y).symm (R.app _ a) := by
  change joinInl K Δ[0] ≫ (functorVertexEquiv _ Y).symm (p.app _ a) = _
  rw [← F2.functorVertexMap_precomp]
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app hp (Opposite.op ⦋0⦌)) a
  exact congrArg (functorVertexEquiv K Y).symm h

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
