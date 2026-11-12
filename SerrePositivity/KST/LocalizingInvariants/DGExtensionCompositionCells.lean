module

public import SerrePositivity.KST.LocalizingInvariants.DGExtensionCompositionStrict
public import SerrePositivity.KST.LocalizingInvariants.DGStrictAdjointComparisonComponent

/-!
概要：元の graph 延長の厳密合成比較で使う単位と余単位の閉零成分を同定する。
方針：実単位・制限の逆同型・実余単位を、元の閉射の合成として計算する。
規約：関手と成分を置き換えない。使われ方：通常随伴一意性との成分照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (D E T : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R T] [Small.{u} T] (F : DGFunctor R D E) (G : DGFunctor R E T)

lemma dgExtensionCompositionUnit_app (M : RightModule R D) :
    (dgExtensionCompositionUnit R D E T F G).app M = closedHomEquiv R (RightModule R D) _ _
      (functorExtensionUnit R D T (F.comp G) M ≫
        (graphRestrictionCompositionIso R D E T F G).inv.app
          (ForgetEnrichment.of (Complex R) ((dgModuleExtension R D T (F.comp G)).obj M))) := by
  apply Subtype.ext
  exact dgClosedCycle_comp R (RightModule R D) _ _

lemma dgExtensionCompositionCounit_app (M : RightModule R T) :
    (dgExtensionCompositionCounit R D E T F G).app M = closedHomEquiv R (RightModule R T) _ _
      ((dgModuleExtension R E T G).onClosed.map
        (functorExtensionCounit R D E F (restrictModule R E T G.op M)) ≫
          functorExtensionCounit R E T G M) := by
  apply Subtype.ext
  let a := functorExtensionCounit R D E F (restrictModule R E T G.op M)
  let b := functorExtensionCounit R E T G M
  change compose R (closedHomEquiv R (RightModule R T) _ _ b).val
    (((dgModuleExtension R E T G).map _ _).f 0
      (closedHomEquiv R (RightModule R E) _ _ a).val) (zero_add 0) = _
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_mapClosedCycle (dgModuleExtension R E T G) a
  exact (congrArg (fun t => compose R (closedHomEquiv R (RightModule R T) _ _ b).val
    t (zero_add 0)) he).trans (dgClosedCycle_comp R (RightModule R T) _ _)

end SerrePositivity.KST.LocalizingInvariants
