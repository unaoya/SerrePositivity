module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCommonMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransClosedIso
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} {E : Type w}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] {F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E}

def dgStrictNatTransCommonFunctorIso (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
    (a : ∀ x, ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x) ≅
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj x))
    (ha : ∀ x, η.app x = _root_.SerrePositivity.DifferentialGraded.closedHomEquiv R E _ _ (a x).hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, v, w, t} F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, v, w, t} G) := by
  let η' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, w, max u v w t, max u v w t} F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, w, max u v w t, max u v w t} G) := {
    app x := η.app x.label.down
    naturality f := η.naturality f }
  let a' (x : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, max u v w t} D) :
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, w, max u v w t, max u v w t} F).obj x) ≅
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, w, max u v w t, max u v w t} G).obj x) := {
    hom := (a x.label.down).hom
    inv := (a x.label.down).inv
    hom_inv_id := (a x.label.down).hom_inv_id
    inv_hom_id := (a x.label.down).inv_hom_id }
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransFunctorIsoOfClosedIso η' a' (fun x => ha x.label.down)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap_lifted, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap_lifted]
  exact (h.precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, v, max u v w t} R D).hom).postcomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, w, max u v w t} R E).inv

end SerrePositivity.InfinityCategories.Project.DerivedCategories
