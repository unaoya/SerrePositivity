module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoChainTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransportAlgebra

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalNativeKanIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoChainTransport

/-!
概要：元の Kan 射への指定値比較を元の頂点表示へ戻すと、元の小さい値比較を回収する。
方針：指定同型の端点補正を保持して後合成し、同じ頂点表示の往復を相殺する。
規約：元の指定値を保持。使われ方：左右比較の底の像を小宇宙の四射の可換式へ揃える。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- Kan 頂点表示の指定比較の像を元の値へ戻すと、同じ元の値比較の指定類になる。 -/
lemma coherentTotalNativeKanIso_valueImage {B D : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ SpaceInfinity.{u})
    (a : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G) :
    HEq ((coherentTotalNativeKanIso F G a).postcomp
      (eqToHom (coherentDiagramTotalVertex_object G).symm))
      (coherentTotalMapNativeValueDownIso F G a) := by
  let v := eqToHom (coherentDiagramTotalVertex_object G)
  let w := eqToHom (coherentDiagramTotalVertex_object G).symm
  let e := coherentTotalMapNativeValueDownIso F G a
  have hc : HEq (coherentTotalNativeKanIso F G a) (e.postcomp v) :=
    functorIsoOfEq_heq _ _ _
  have hp := functorIso_postcomp_heq_of_heq (e.postcomp v)
    (coherentTotalNativeKanIso F G a) rfl (coherentTotalVertexMap_factor F G a) hc w
  have he : HEq ((e.postcomp v).postcomp w) e := by
    have ht := functorIso_postcomp_postcomp e v w
    have hv : v ≫ w = 𝟙 _ := (eqToIso (coherentDiagramTotalVertex_object G)).hom_inv_id
    have hh := functorIso_postcomp_heq_of_map_eq e hv.symm
    exact (heq_of_eq ht).trans (hh.trans (heq_of_eq (functorIso_postcomp_id e)))
  exact hp.trans he

end SerrePositivity.InfinityCategories.F2
