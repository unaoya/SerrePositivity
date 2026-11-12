module
public import SerrePositivity.DifferentialGraded.Module.FreeSphere

/-! # dg 加群延長と Yoneda の全次数自然性

概要：表現可能加群の延長の同型は全 Hom 複体上で自然である。
方針：tensor の右単位の自然性と主 Hom end の評価を使う。
規約：対象ごとの同型に留めない。使われ方：β3 の関手の完全性の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 表現可能入力での延長の Hom 写像は、対角 bimodule との tensor の左作用。 -/
lemma dgModuleExtension_yoneda_map (d d' : D) :
    yonedaHom A D d d' ≫
      (dgModuleExtension A D E F).map (representable A d) (representable A d') =
    (BimoduleTensor.compose A E D D (functorGraph A D E F)
      (Bimodule.diagonal A D)).toFunctor.map d d' := by
  apply moduleHom_ext A E
  intro e
  have h := BimoduleTensor.compose_leftMap_π A E D (RightModule A D)
    (functorGraph A D E F) (DGFunctor.id (RightModule A D))
    (representable A d) (representable A d') e
  change (dgModuleExtension A D E F).map (representable A d) (representable A d') ≫
    moduleHomπ A E _ _ e = 𝟙 _ ≫ BalancedTensor.rightHomMap A D _ _ _ at h
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => yonedaHom A D d d' ≫ k)
      (h.trans (Category.id_comp _))).trans
        (BimoduleTensor.compose_leftMap_π A E D D (functorGraph A D E F)
          (Bimodule.diagonal A D) d d' e).symm)

/-- 表現可能加群の延長同型は、全次数の主 Hom 複体上で自然。 -/
lemma dgModuleExtensionRepresentableIso_naturality (d d' : D) :
    yonedaHom A D d d' ≫
        (dgModuleExtension A D E F).map (representable A d) (representable A d') ≫
        moduleHomPostcompose A E _ _ _ (dgModuleExtensionRepresentableIso A D E F d').hom =
      (F.comp (dgYoneda A E)).map d d' ≫
        moduleHomPrecompose A E _ _ _ (dgModuleExtensionRepresentableIso A D E F d).hom := by
  rw [← Category.assoc, dgModuleExtension_yoneda_map]
  exact BimoduleTensor.rightUnitIso_naturality A E D (functorGraph A D E F) d d'

end SerrePositivity.InfinityCategories.Project.DerivedCategories
