module
public import SerrePositivity.InfinityCategories.Derived.DGModuleStrictNatTrans
public import SerrePositivity.InfinityCategories.Derived.DGModuleExtensionYoneda
public import SerrePositivity.InfinityCategories.Derived.DGUniverseLift

/-! # 延長と Yoneda の厳密 dg 自然変換

概要：代表加群の延長同型を全次数で自然な閉零成分へ束ねる。
方針：全 Hom 複体上の単位比較を使い、始域の宇宙持ち上げとも合成する。
規約：dg nerve の実ホモトピーへの入力。使われ方：前三角 dg 関手の完全性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve

/-- 厳密 dg 自然変換を任意の dg 関手で前合成する。 -/
def dgStrictNatTransPrecomp {A : Type u} [CommRing A]
    {B : Type z} {D : Type v} {E : Type w}
    [DGCategory A B] [DGCategory A D] [DGCategory A E]
    (L : DGFunctor A B D) {F G : DGFunctor A D E} (η : StrictNatTrans F G) :
    StrictNatTrans (L.comp F) (L.comp G) where
  app x := η.app (L.obj x)
  naturality f := η.naturality ((L.map _ _).f _ f)

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 延長と Yoneda の比較は、各対象で実加群同型の閉零 cycle を持つ厳密自然変換。 -/
def dgModuleExtensionYonedaStrict :
    StrictNatTrans ((dgYoneda A D).comp (dgModuleExtension A D E F))
      (F.comp (dgYoneda A E)) :=
  dgModuleStrictNatTransOfHomNaturality A E
    (fun x => (dgModuleExtensionRepresentableIso A D E F x).hom)
    (dgModuleExtensionRepresentableIso_naturality A D E F)

/-- 始域を共通宇宙へ上げた延長・Yoneda 比較の厳密 dg 自然変換。 -/
def dgModuleExtensionYonedaLiftedStrict :
    StrictNatTrans
      ((dgUniverseLiftDown.{u, v, max (u + 1) w} A D).comp
        ((dgYoneda A D).comp (dgModuleExtension A D E F)))
      ((dgUniverseLiftDown.{u, v, max (u + 1) w} A D).comp
        (F.comp (dgYoneda A E))) :=
  dgStrictNatTransPrecomp _ (dgModuleExtensionYonedaStrict A D E F)

end SerrePositivity.InfinityCategories
