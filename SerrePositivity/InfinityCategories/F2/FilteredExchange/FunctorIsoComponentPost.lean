module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoComponentTransport
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeFunctorCurryIsoPresentation
public import SerrePositivity.InfinityCategories.F2.CatInfinity.VertexIsoTerminalEquality
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallUnstraighteningPointFiberEvaluation

/-!
概要：元の関手同型の各点成分と後合成は、指定同型の値まで整合する。
方針：各点成分を元の評価写像の像へ戻し、評価の自然性を使う。
規約：端点の表示変更のみ許す。使われ方：全 prism 比較の始点射影の成分。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 指定関手同型の後合成の各点成分は、同じ元の各点成分の像。 -/
lemma functorIso_app_postcomp_heq {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z] {f g : X ⟶ Y}
    (e : FunctorIso f g) (q : Y ⟶ Z) (x : X _⦋0⦌) :
    HEq ((e.postcomp q).app x) (VertexIso.map (e.app x) q) := by
  have h₀ := functorIso_app_heq_evaluate (e.postcomp q) x
  rw [functorIso_postcomp_eq_mapIso] at h₀
  have h₁ := vertexIso_map_heq_of_heq (e.app x) (VertexIso.map e (evaluateFunctorAt x))
    (evaluateFunctorAt_functorVertex x f).symm (evaluateFunctorAt_functorVertex x g).symm
    (functorIso_app_heq_evaluate e x) q
  rw [functorIso_postcomp_eq_mapIso]
  exact h₀.trans ((heq_of_eq (vertexIso_map_comp e ((ihom X).map q) (evaluateFunctorAt x))).trans
    ((vertexIso_map_heq e (evaluateFunctorAt_post q x)).trans
      ((heq_of_eq (vertexIso_map_comp e (evaluateFunctorAt x) q).symm).trans h₁.symm)))

/-- 等式から来る元の関手同型の成分は、同じ頂点等式の同型となる。 -/
lemma functorIso_app_eqToIso_heq {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : X ⟶ Y} (h : f = g) (x : X _⦋0⦌) :
    HEq (FunctorIso.app (eqToIso
      (congrArg (fun k => SSet.HomotopyCategory.mk (functorVertex k)) h) :
      FunctorIso f g) x)
      (eqToIso (congrArg SSet.HomotopyCategory.mk
        (congrArg (fun k : X ⟶ Y => k.app (Opposite.op ⦋0⦌) x) h))) := by
  subst g
  have he := functorIso_app_heq_evaluate (show FunctorIso f f from Iso.refl _) x
  simp only [VertexIso.map, Functor.mapIso_refl] at he
  have hr {a b : hoFunctor.obj Y} (h : a = b) : HEq (Iso.refl a) (Iso.refl b) := by
    cases h
    rfl
  exact he.trans (hr (congrArg SSet.HomotopyCategory.mk (evaluateFunctorAt_functorVertex x f)))

end SerrePositivity.InfinityCategories.F2
