module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentNativeKanValueImage
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentNativeKanValueMaps

/-!
概要：元の Kan 値比較の後合成像を、元の小宇宙の値比較の後合成として表示する。
方針：頂点表示の逆との自然性で合成順を揃え、明示した端点等式で指定像を戻す。
規約：指定同型と端点の式を保持。使われ方：共通の右脚・左脚の底の像の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- Kan 二射目で後合成し元の頂点表示へ戻した指定像は、元の値比較の後合成である。 -/
lemma coherentTotalNativeKanIso_postValueImage {B D E : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ SpaceInfinity.{u})
    (H : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ SpaceInfinity.{u})
    (a : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G)
    (b : smallLeftUnstraightening G ⟶ smallLeftUnstraightening H) :
    HEq (((coherentTotalNativeKanIso F G a).postcomp (continuousKanReplacement.map b)).postcomp
      (eqToHom (coherentDiagramTotalVertex_object H).symm))
      ((coherentTotalMapNativeValueDownIso F G a).postcomp (coherentTotalVertexMap G H b)) := by
  let e := coherentTotalNativeKanIso F G a
  let wG := eqToHom (coherentDiagramTotalVertex_object G).symm
  let wH := eqToHom (coherentDiagramTotalVertex_object H).symm
  let r := coherentTotalVertexMap G H b
  have hp := functorIso_postcomp_heq_of_heq (coherentTotalMapNativeValueDownIso F G a)
    (e.postcomp wG) (coherentTotalNativeKanIso_valueSourceMap F G a).symm
    (coherentTotalNativeKanIso_valueTargetMap F G a).symm
    (coherentTotalNativeKanIso_valueImage F G a) r
  have h₀ := functorIso_postcomp_postcomp e (continuousKanReplacement.map b) wH
  have hm : continuousKanReplacement.map b ≫ wH = wG ≫ r :=
    coherentTotalVertexMap_inverse_factor G H b
  have h₁ := functorIso_postcomp_heq_of_map_eq e hm.symm
  have h₂ := functorIso_postcomp_postcomp e wG r
  exact (heq_of_eq h₀).trans (h₁.trans ((heq_of_eq h₂.symm).trans hp))

end SerrePositivity.InfinityCategories.F2
