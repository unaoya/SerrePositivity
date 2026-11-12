module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoCompositionTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport
/-!
概要：同じ辺値の逆と実対角値の比を、元の普遍比較の値による比へ移す。
方針：元の辺値の端点表示と、指定対角値の実終点の等式を保持して合成する。
規約：元の値因子・全初期値・指定対角比較を変更しない。
使われ方：Ncomp の raw 比を元の作用比較へ戻す。
-/

@[expose] public section
open CategoryTheory SSet
open scoped Simplicial
noncomputable section
namespace SerrePositivity.InfinityCategories.F2
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
/-- 概要：対角値の終点表示を頂点で揃えて同じ比を移す。
方針：逆と合成の表示変更を使う。規約：指定値を保持。使われ方：raw 比の照合。 -/
lemma functorIso_value_ratio_heq_vertices {A B Y Z K : SSet.{u}} (a : A ⟶ B)
    (v₁ : A ⟶ Y) (v₂ : B ⟶ Z) (g : Y ⟶ Z)
    (e : FunctorIso (a ≫ v₂) (v₁ ≫ g)) (q : K ⟶ A)
    {t t' : ((ihom K).obj Z) _⦋0⦌}
    (D : VertexIso (functorVertex ((q ≫ a) ≫ v₂)) t)
    (D' : VertexIso (functorVertex (q ≫ (a ≫ v₂))) t')
    (ht : t = t') (hD : HEq D D') :
    HEq ((functorIsoOfEq (e.precomp q) (Category.assoc q a v₂).symm rfl).symm ≪≫ D)
      ((e.precomp q).symm ≪≫ D') := by
  have hfirst := vertexIso_symm_heq_of_heq
    (functorIsoOfEq (e.precomp q) (Category.assoc q a v₂).symm rfl) (e.precomp q)
    (congrArg functorVertex (Category.assoc q a v₂)) rfl
    (functorIsoOfEq_heq (e.precomp q) (Category.assoc q a v₂).symm rfl)
  exact vertexIso_trans_heq_of_heq _ _ _ _ rfl
    (congrArg functorVertex (Category.assoc q a v₂)) ht hfirst hD
end SerrePositivity.InfinityCategories.F2
