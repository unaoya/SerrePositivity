module
public import SerrePositivity.InfinityCategories.Derived.DGNerveCommonMap
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransClosedIso
/-!
概要：独立の対象宇宙から共通 nerve へ移した厳密 dg 自然同型を構成する。
方針：全 Hom 成分と閉同型を共通の対象持ち上げに移し、native 比較同型で共役する。
規約：対象ごとの同型だけではなく、実関手同型を返す。Small 仮定は不要。
使われ方：混在宇宙の tensor・Yoneda 比較と完全性の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {D : Type v} {E : Type w}
  [DGCategory R D] [DGCategory R E] {F G : DGFunctor R D E}

def dgStrictNatTransCommonFunctorIso (η : StrictNatTrans F G)
    (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ≅
      ForgetEnrichment.of (Complex R) (G.obj x))
    (ha : ∀ x, η.app x = closedHomEquiv R E _ _ (a x).hom) :
    FunctorIso (dgNerveCommonMap.{u, v, w, t} F) (dgNerveCommonMap.{u, v, w, t} G) := by
  let η' : StrictNatTrans
      (dgUniverseLiftFunctor.{u, v, w, max u v w t, max u v w t} F)
      (dgUniverseLiftFunctor.{u, v, w, max u v w t, max u v w t} G) := {
    app x := η.app x.label.down
    naturality f := η.naturality f }
  let a' (x : DGUniverseLift.{v, max u v w t} D) :
      ForgetEnrichment.of (Complex R)
        ((dgUniverseLiftFunctor.{u, v, w, max u v w t, max u v w t} F).obj x) ≅
      ForgetEnrichment.of (Complex R)
        ((dgUniverseLiftFunctor.{u, v, w, max u v w t, max u v w t} G).obj x) := {
    hom := (a x.label.down).hom
    inv := (a x.label.down).inv
    hom_inv_id := (a x.label.down).hom_inv_id
    inv_hom_id := (a x.label.down).inv_hom_id }
  have h := dgStrictNatTransFunctorIsoOfClosedIso η' a' (fun x => ha x.label.down)
  rw [dgNerveCommonMap_lifted, dgNerveCommonMap_lifted]
  exact (h.precomp (dgNerveUniverseLiftIso.{u, v, max u v w t} R D).hom).postcomp
    (dgNerveUniverseLiftIso.{u, w, max u v w t} R E).inv

end SerrePositivity.InfinityCategories
