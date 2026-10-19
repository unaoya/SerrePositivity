module
public import SerrePositivity.InfinityCategories.Derived.DGModuleStrictNatTransIso
public import SerrePositivity.InfinityCategories.Derived.DGModuleExtensionYonedaStrict

/-! # 延長と Yoneda の native nerve の実関手同型

概要：加群延長後の Yoneda と対象像の Yoneda は実関手圏で同型。
方針：共通宇宙の始域で全 Hom 自然な実加群同型族を使う。
規約：辺や対象ごとの比較だけで済ませない。使われ方：dg 関手の完全性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D E : Type v)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
variable (F : DGFunctor A D E)

/-- 共通宇宙の始域における延長・Yoneda 比較の実関手同型。 -/
def dgModuleExtensionYonedaNerveIso :
    FunctorIso
      (dgNerve.map ((dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp
        ((dgYoneda A D).comp (dgModuleExtension A D E F))))
      (dgNerve.map ((dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp
        (F.comp (dgYoneda A E)))) :=
  dgModuleFunctorIsoOfStrictNatTrans A E (dgModuleExtensionYonedaLiftedStrict A D E F)
    (fun x => (dgModuleExtensionRepresentableIso A D E F x.label.down).hom)
    (fun _ => rfl) (fun _ => inferInstance)

/-- 始域を持ち上げた Yoneda の後で、実際の加群延長を適用する表示。 -/
def dgModuleExtensionYonedaCompositeIso :
    FunctorIso
      (dgNerve.map ((dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp
        (dgYoneda A D)) ≫ dgNerve.map (dgModuleExtension A D E F))
      (dgNerve.map ((dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp
        (F.comp (dgYoneda A E)))) := by
  have he : ((dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp (dgYoneda A D)).comp
      (dgModuleExtension A D E F) =
    (dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp
      ((dgYoneda A D).comp (dgModuleExtension A D E F)) := by
    apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
    intro x y
    simp only [EnrichedFunctor.comp_map, Category.assoc, eqToHom_refl, Category.comp_id]
  rw [← dgNerve.map_comp, he]
  exact dgModuleExtensionYonedaNerveIso A D E F

end SerrePositivity.InfinityCategories
