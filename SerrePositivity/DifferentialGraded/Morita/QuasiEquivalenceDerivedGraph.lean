module
public import SerrePositivity.DifferentialGraded.Morita.KernelDerivedFunctor
public import SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceGraphAction

/-! # 主導来kernel上の実際のgraph作用と既存導来擬同値の比較

U16aの公開済み降下APIを使い、通常kernel版の比較を主導来graphへ移す。
随伴・単位・余単位は既存の延長–制限随伴から自然同型に沿って運ぶ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

def quasiEquivalenceDerivedGraphIso :
    kernelDerivedTensor A D E (kernelGraph A D E F) ≅ dgDerivedExtension A D E F :=
  kernelDerivedTensorOnBimoduleIso A D E (BimoduleCategory.of A E D (functorGraph A D E F)) ≪≫
    quasiEquivalenceGraphActionIso A D E F

local instance moritaDerivedGraphExtensionShift : (dgDerivedExtension A D E F).CommShift ℤ :=
  dgDerivedExtensionCommShift A D E F

@[instance_reducible]
def quasiEquivalenceDerivedGraphCommShift :
    (kernelDerivedTensor A D E (kernelGraph A D E F)).CommShift ℤ :=
  Functor.CommShift.ofIso (quasiEquivalenceDerivedGraphIso A D E F).symm ℤ

attribute [local instance] quasiEquivalenceDerivedGraphCommShift

lemma quasiEquivalenceDerivedGraphIsoCommShift :
    NatTrans.CommShift (quasiEquivalenceDerivedGraphIso A D E F).hom ℤ := by
  let : NatTrans.CommShift (quasiEquivalenceDerivedGraphIso A D E F).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (quasiEquivalenceDerivedGraphIso A D E F).symm ℤ
  exact NatTrans.CommShift.of_iso_inv (quasiEquivalenceDerivedGraphIso A D E F).symm ℤ

attribute [local instance] quasiEquivalenceDerivedGraphIsoCommShift

lemma quasiEquivalenceDerivedGraphIsTriangulated :
    (kernelDerivedTensor A D E (kernelGraph A D E F)).IsTriangulated := by
  let := dgDerivedExtensionIsTriangulated A D E F
  exact Functor.isTriangulated_of_iso (quasiEquivalenceDerivedGraphIso A D E F).symm

lemma quasiEquivalenceDerivedGraphIsEquivalence (hF : QuasiEquivalence F) :
    (kernelDerivedTensor A D E (kernelGraph A D E F)).IsEquivalence := by
  let : (dgDerivedExtension A D E F).IsEquivalence :=
    (dgFunctorDerivedEquivalence A D E F hF).isEquivalence_functor
  exact Functor.isEquivalence_of_iso (quasiEquivalenceDerivedGraphIso A D E F).symm

def quasiEquivalenceDerivedGraphAdjunction :
    kernelDerivedTensor A D E (kernelGraph A D E F) ⊣ dgDerivedRestriction A D E F :=
  (dgDerivedExtensionRestrictionAdjunction A D E F).ofNatIsoLeft
    (quasiEquivalenceDerivedGraphIso A D E F).symm

lemma quasiEquivalenceDerivedGraphUnit_app (X : DerivedModuleCategory A D) :
    (quasiEquivalenceDerivedGraphAdjunction A D E F).unit.app X =
      (dgDerivedExtensionUnit A D E F).app X ≫
        (dgDerivedRestriction A D E F).map
          ((quasiEquivalenceDerivedGraphIso A D E F).inv.app X) := rfl

lemma quasiEquivalenceDerivedGraphCounit_app (Y : DerivedModuleCategory A E) :
    (quasiEquivalenceDerivedGraphAdjunction A D E F).counit.app Y =
      (quasiEquivalenceDerivedGraphIso A D E F).hom.app ((dgDerivedRestriction A D E F).obj Y) ≫
        (dgDerivedExtensionCounit A D E F).app Y := rfl

lemma quasiEquivalenceDerivedGraph_perfect {X : DerivedModuleCategory A D}
    (hX : modulePerfect A D X) :
    modulePerfect A E ((kernelDerivedTensor A D E (kernelGraph A D E F)).obj X) :=
  (modulePerfect A E).prop_of_iso ((quasiEquivalenceDerivedGraphIso A D E F).app X).symm
    (dgDerivedExtension_perfect A D E F hX)

def quasiEquivalenceDerivedGraphOnPerfectIso :
    perfectFunctorRestriction A D E (kernelDerivedTensor A D E (kernelGraph A D E F))
        (fun _ h => quasiEquivalenceDerivedGraph_perfect A D E F h) ≅
      quasiEquivalencePerfectExtension A D E F :=
  perfectFunctorIso A D E _ _
    (fun _ h => quasiEquivalenceDerivedGraph_perfect A D E F h)
    (fun _ h => dgDerivedExtension_perfect A D E F h) (quasiEquivalenceDerivedGraphIso A D E F)

end SerrePositivity.DifferentialGraded.Morita
