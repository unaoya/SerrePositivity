module

public import SerrePositivity.KST.LocalizingInvariants.DGExtensionCompositionCells

/-!
概要：元の厳密 graph 延長比較の成分を、通常の随伴一意性同型の成分へ同定する。
方針：輸送単位・合成余単位の閉零計算を、実左随伴比較の成分公式へ代入する。
規約：同じ実延長・実同型を保持。使われ方：比較の可逆性と実 Perf 合成同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants

lemma adjointComparison_hom_app {C E : Type*} [Category* C] [Category* E]
    {L L' : C ⥤ E} {Q : E ⥤ C} (a : L ⊣ Q) (b : L' ⊣ Q) (x : C) :
    (Adjunction.leftAdjointUniq a b).hom.app x =
      L.map (b.unit.app x) ≫ a.counit.app (L'.obj x) := by
  have h := (a.homEquiv x (L'.obj x)).symm_apply_apply
    ((Adjunction.leftAdjointUniq a b).hom.app x)
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_counit] at h
  exact h.symm

variable {R : Type u} [CommRing R] {D E T : Type v}
  [DGCategory R D] [DGCategory R E] [DGCategory R T]

lemma dgFunctorOnClosed_comp_map (F : DGFunctor R D E) (G : DGFunctor R E T)
    {x y : ClosedCategory R D} (f : x ⟶ y) :
    (F.comp G).onClosed.map f = G.onClosed.map (F.onClosed.map f) := by
  change ForgetEnrichment.homTo (Complex R) f ≫ (F.map _ _ ≫ G.map _ _) =
    (ForgetEnrichment.homTo (Complex R) f ≫ F.map _ _) ≫ G.map _ _
  exact (Category.assoc _ _ _).symm

variable (R) (D E T) [Small.{u} D] [Small.{u} E] [Small.{u} T]
  (F : DGFunctor R D E) (G : DGFunctor R E T)

lemma dgExtensionCompositionStrict_app_eq (M : RightModule R D) :
    (dgExtensionCompositionStrict R D E T F G).app M =
      closedHomEquiv R (RightModule R T) _ _
        ((dgExtensionCompositionIso R D E T F G).hom.app
          (ForgetEnrichment.of (Complex R) M)) := by
  let A := (dgModuleExtensionRestrictionAdjunction R D E F).comp
    (dgModuleExtensionRestrictionAdjunction R E T G)
  let B := (dgModuleExtensionRestrictionAdjunction R D T (F.comp G)).ofNatIsoRight
    (graphRestrictionCompositionIso R D E T F G).symm
  have hu : (dgExtensionCompositionUnit R D E T F G).app M =
      closedHomEquiv R (RightModule R D) _ _
        (B.unit.app (ForgetEnrichment.of (Complex R) M)) := by
    exact dgExtensionCompositionUnit_app R D E T F G M
  let M' := (dgModuleExtension R D T (F.comp G)).obj M
  have hc : (dgExtensionCompositionCounit R D E T F G).app M' =
      closedHomEquiv R (RightModule R T) _ _
        (A.counit.app (ForgetEnrichment.of (Complex R) M')) := by
    exact (dgExtensionCompositionCounit_app R D E T F G M').trans
      (congrArg (closedHomEquiv R (RightModule R T) _ _)
        (Adjunction.comp_counit_app (dgModuleExtensionRestrictionAdjunction R D E F)
          (dgModuleExtensionRestrictionAdjunction R E T G)
          (ForgetEnrichment.of (Complex R) M')).symm)
  have h := dgStrictAdjointComparison_app_eq
    ((dgModuleExtension R D E F).comp (dgModuleExtension R E T G))
    (dgModuleExtension R D T (F.comp G))
    ((dgModuleRestriction R E T G.op).comp (dgModuleRestriction R D E F.op))
    (dgExtensionCompositionUnit R D E T F G) (dgExtensionCompositionCounit R D E T F G) M
    (B.unit.app (ForgetEnrichment.of (Complex R) M))
    (A.counit.app (ForgetEnrichment.of (Complex R) M')) hu hc
  have he : (dgExtensionCompositionIso R D E T F G).hom.app
      (ForgetEnrichment.of (Complex R) M) =
      ((dgModuleExtension R D E F).comp (dgModuleExtension R E T G)).onClosed.map
        (B.unit.app (ForgetEnrichment.of (Complex R) M)) ≫
          A.counit.app (ForgetEnrichment.of (Complex R) M') := by
    rw [dgFunctorOnClosed_comp_map]
    exact adjointComparison_hom_app A B (ForgetEnrichment.of (Complex R) M)
  exact h.trans (congrArg (closedHomEquiv R (RightModule R T) _ _) he.symm)

end SerrePositivity.KST.LocalizingInvariants
