module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTotalNativeKanIso

/-!
概要：元の Kan 値比較を頂点表示へ戻す際の始域・終域の射を明示する。
方針：同じ頂点表示の往復を元の射の式で相殺する。
規約：HEq から端点等式を抽出しない。使われ方：指定像の後合成と元の四射の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B D : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ SpaceInfinity.{u})
  (a : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G)

/-- 頂点表示の逆との可換性も、元の Kan 射と元の値の射の厳密な式である。 -/
lemma coherentTotalVertexMap_inverse_factor :
    continuousKanReplacement.map a ≫ eqToHom (coherentDiagramTotalVertex_object G).symm =
      eqToHom (coherentDiagramTotalVertex_object F).symm ≫ coherentTotalVertexMap F G a := by
  let e := eqToIso (coherentDiagramTotalVertex_object F)
  change _ = e.inv ≫ (e.hom ≫ _)
  rw [← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- Kan 値比較の始域射を元の頂点表示へ戻すと元の native 値の射である。 -/
lemma coherentTotalNativeKanIso_valueSourceMap :
    (coherentTotalMapNativeValueDown F G a ≫ eqToHom (coherentDiagramTotalVertex_object G)) ≫
        eqToHom (coherentDiagramTotalVertex_object G).symm =
      coherentTotalMapNativeValueDown F G a := by
  let e := eqToIso (coherentDiagramTotalVertex_object G)
  change (_ ≫ e.hom) ≫ e.inv = _
  rw [Category.assoc, e.hom_inv_id, Category.comp_id]

/-- Kan 値比較の終域射を元の頂点表示へ戻すと元の具体的な値の射である。 -/
lemma coherentTotalNativeKanIso_valueTargetMap :
    (eqToHom (coherentDiagramTotalVertex_object F) ≫ continuousKanReplacement.map a) ≫
      eqToHom (coherentDiagramTotalVertex_object G).symm = coherentTotalVertexMap F G a :=
  Category.assoc _ _ _

end SerrePositivity.InfinityCategories.F2
