module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoPrecompEndpointTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation

/-!
概要：実端点を正規化した前合成の比較は、二段の任意の再制限でも値を保つ。
方針：表示変更を外し、変数のまま前合成の合成則を使って再び端点を揃える。
規約：大きい比較の定義を展開しない。使われ方：元の三角形境界比較の全初期値での自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定比較の二段の前合成は、実端点をそれぞれ正規化しても同じ指定値を保持する。 -/
lemma functorIsoOfEq_precomp_reindex_heq {A B X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : FunctorIso f g) (p : A ⟶ X) (r : B ⟶ A)
    {fA gA : A ⟶ Y} {fB gB : B ⟶ Y}
    (hfA : p ≫ f = fA) (hgA : p ≫ g = gA)
    (hfB : (r ≫ p) ≫ f = fB) (hgB : (r ≫ p) ≫ g = gB) :
    HEq ((functorIsoOfEq (e.precomp p) hfA hgA).precomp r)
      (functorIsoOfEq (e.precomp (r ≫ p)) hfB hgB) :=
  (functorIsoOfEq_precomp_heq (e.precomp p) hfA hgA r).trans
    ((heq_of_eq (functorIso_precomp_precomp e p r)).trans (functorIsoOfEq_heq _ _ _).symm)

end SerrePositivity.InfinityCategories.F2
