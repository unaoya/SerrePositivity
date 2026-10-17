module
public import SerrePositivity.DifferentialGraded.Derived.Restriction
public import SerrePositivity.DifferentialGraded.Module.RestrictionCoherence

/-! # 導来制限の恒等・合成比較と局所化前での計算 -/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance moduleDerivedRestriction_lifting (E : Type w) [DGCategory A E] [Small.{u} E]
    (F : DGFunctor A Dᵒᵖ Eᵒᵖ) :
    Localization.Lifting (moduleToDerived A E) (moduleQuasiIso A E)
      (moduleRestriction A D E F ⋙ moduleToDerived A D) (moduleDerivedRestriction A D E F) :=
  ⟨eqToIso (moduleDerivedRestriction_fac A D E F)⟩

def moduleDerivedRestrictionIdIso :
    moduleDerivedRestriction A D D (DGFunctor.id Dᵒᵖ) ≅ 𝟭 (DerivedModuleCategory A D) :=
  Localization.liftNatIso (moduleToDerived A D) (moduleQuasiIso A D)
    (moduleRestriction A D D (DGFunctor.id Dᵒᵖ) ⋙ moduleToDerived A D) (moduleToDerived A D)
    (moduleDerivedRestriction A D D (DGFunctor.id Dᵒᵖ)) (𝟭 _)
    (Functor.isoWhiskerRight (moduleRestrictionIdIso A D) (moduleToDerived A D))

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : Type z) [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A Dᵒᵖ Eᵒᵖ) (G : DGFunctor A Eᵒᵖ Tᵒᵖ)

lemma moduleDerivedRestrictionComp_fac :
    moduleToDerived A T ⋙ (moduleDerivedRestriction A E T G ⋙ moduleDerivedRestriction A D E F) =
      (moduleRestriction A E T G ⋙ moduleRestriction A D E F) ⋙ moduleToDerived A D := by
  rw [← Functor.assoc, moduleDerivedRestriction_fac, Functor.assoc,
    moduleDerivedRestriction_fac, ← Functor.assoc]

instance moduleDerivedRestrictionComp_lifting :
    Localization.Lifting (moduleToDerived A T) (moduleQuasiIso A T)
      ((moduleRestriction A E T G ⋙ moduleRestriction A D E F) ⋙ moduleToDerived A D)
      (moduleDerivedRestriction A E T G ⋙ moduleDerivedRestriction A D E F) :=
  ⟨eqToIso (moduleDerivedRestrictionComp_fac A D E T F G)⟩

def moduleDerivedRestrictionCompIso :
    moduleDerivedRestriction A E T G ⋙ moduleDerivedRestriction A D E F ≅
      moduleDerivedRestriction A D T (F.comp G) :=
  Localization.liftNatIso (moduleToDerived A T) (moduleQuasiIso A T)
    ((moduleRestriction A E T G ⋙ moduleRestriction A D E F) ⋙ moduleToDerived A D)
    (moduleRestriction A D T (F.comp G) ⋙ moduleToDerived A D)
    (moduleDerivedRestriction A E T G ⋙ moduleDerivedRestriction A D E F)
    (moduleDerivedRestriction A D T (F.comp G))
    (Functor.isoWhiskerRight (moduleRestrictionCompIso A D E T F G) (moduleToDerived A D))

lemma moduleDerivedRestrictionCompIso_hom_app (M : ModuleCategory A T) :
    (moduleDerivedRestrictionCompIso A D E T F G).hom.app ((moduleToDerived A T).obj M) =
      (Localization.Lifting.iso (moduleToDerived A T) (moduleQuasiIso A T)
        ((moduleRestriction A E T G ⋙ moduleRestriction A D E F) ⋙ moduleToDerived A D)
        (moduleDerivedRestriction A E T G ⋙ moduleDerivedRestriction A D E F)).hom.app M ≫
      (moduleToDerived A D).map (moduleRestrictionCompObjIso A D E T F G M).hom ≫
      (Localization.Lifting.iso (moduleToDerived A T) (moduleQuasiIso A T)
        (moduleRestriction A D T (F.comp G) ⋙ moduleToDerived A D)
        (moduleDerivedRestriction A D T (F.comp G))).inv.app M :=
  Localization.liftNatTrans_app _ _ _ _ _ _ _ _

end SerrePositivity.DifferentialGraded
