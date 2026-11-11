module

public import SerrePositivity.KST.LocalizingInvariants.DGRestrictionIdentityStrict
public import SerrePositivity.KST.LocalizingInvariants.DGExtensionCounitHomNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGExtensionCompositionIsoComponent

/-!
概要：D の元の恒等 graph 延長を恒等関手へ比較し、閉零成分を実同型へ同定する。
方針：恒等制限の逆と元の延長余単位を、厳密左随伴比較に代入する。
規約：元の tensor 延長を保持。使われ方：Perf の恒等比較と実値の関手。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 元の恒等 graph 延長から恒等関手への、全斉次射に自然な比較。 -/
def dgExtensionIdentityStrict : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (dgModuleExtension R D D (DGFunctor.id D))
    (DGFunctor.id (RightModule R D)) :=
  dgStrictAdjointComparison _ _ _ (dgRestrictionIdentityUnitStrict R D)
    (dgExtensionCounitStrict R D D (DGFunctor.id D))

/-- 通常の随伴一意性から得る、元の恒等延長の実自然同型。 -/
def dgExtensionIdentityIso : (dgModuleExtension R D D (DGFunctor.id D)).onClosed ≅ 𝟭 _ :=
  Adjunction.leftAdjointUniq (dgModuleExtensionRestrictionAdjunction R D D (DGFunctor.id D))
    (Adjunction.id.ofNatIsoRight (moduleRestrictionIdIso R D).symm)

lemma dgExtensionIdentityStrict_app_eq (M : RightModule R D) :
    (dgExtensionIdentityStrict R D).app M = closedHomEquiv R (RightModule R D) _ _
      ((dgExtensionIdentityIso R D).hom.app (ForgetEnrichment.of (Complex R) M)) := by
  let A := dgModuleExtensionRestrictionAdjunction R D D (DGFunctor.id D)
  let B := Adjunction.id.ofNatIsoRight (moduleRestrictionIdIso R D).symm
  have hu : (dgRestrictionIdentityUnitStrict R D).app M =
      closedHomEquiv R (RightModule R D) _ _
        (B.unit.app (ForgetEnrichment.of (Complex R) M)) := by
    change _ = closedHomEquiv R (RightModule R D) _ _
      (𝟙 _ ≫ (moduleRestrictionIdObjIso R D (ForgetEnrichment.of (Complex R) M)).inv)
    rw [Category.id_comp]
    rfl
  have hc : (dgExtensionCounitStrict R D D (DGFunctor.id D)).app M =
      closedHomEquiv R (RightModule R D) _ _
        (A.counit.app (ForgetEnrichment.of (Complex R) M)) := rfl
  have h := dgStrictAdjointComparison_app_eq (dgModuleExtension R D D (DGFunctor.id D))
    (DGFunctor.id (RightModule R D)) (dgModuleRestriction R D D (DGFunctor.id D).op)
    (dgRestrictionIdentityUnitStrict R D) (dgExtensionCounitStrict R D D (DGFunctor.id D)) M
    (B.unit.app (ForgetEnrichment.of (Complex R) M))
    (A.counit.app (ForgetEnrichment.of (Complex R) M)) hu hc
  exact h.trans (congrArg (closedHomEquiv R (RightModule R D) _ _)
    (adjointComparison_hom_app A B (ForgetEnrichment.of (Complex R) M)).symm)

end SerrePositivity.KST.LocalizingInvariants
