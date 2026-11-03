module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalMapNativeValueDown

/-!
概要：元の native 余極限値の射を元の全空間 Kan 射と、頂点表示を保って比較する。
方針：元の値比較同型へ頂点表示を後合成し、厳密な自然性の式で終端を揃える。
規約：元の指定同型を保持。使われ方：native cospan の同じ Kan cospan への厳密化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の native 値の射と元の Kan 射の間の、同じ頂点表示による指定可換同型。 -/
def coherentTotalNativeKanIso {B D : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ SpaceInfinity.{u})
    (a : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G) :
    FunctorIso
      (coherentTotalMapNativeValueDown F G a ≫ eqToHom (coherentDiagramTotalVertex_object G))
      (eqToHom (coherentDiagramTotalVertex_object F) ≫ continuousKanReplacement.map a) :=
  functorIsoOfEq ((coherentTotalMapNativeValueDownIso F G a).postcomp
    (eqToHom (coherentDiagramTotalVertex_object G))) rfl (coherentTotalVertexMap_factor F G a)

end SerrePositivity.InfinityCategories.F2
