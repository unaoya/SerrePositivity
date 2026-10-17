module
public import SerrePositivity.DifferentialGraded.Morita.KernelResolution
public import SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceGraphNaturality
public import SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceTriangles

/-! # U16aの実際の通常kernel導来作用とU16bのgraph比較

公開済みkernelDerivedTensorOnBimoduleを使う。kernel変数の局所化への降下は別のU16a API。
同値本体・随伴・単位・余単位は既存の導来延長–制限のものを保つ。
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

/-- 公開済みの実際の通常kernel導来作用から、既存導来延長への関手自然同型。 -/
def quasiEquivalenceGraphActionIso :
    kernelDerivedTensorOnBimodule A D E (functorGraph A D E F) ≅ dgDerivedExtension A D E F :=
  eqToIso (kernelDerivedTensorOnBimodule_graph A D E F)

lemma quasiEquivalenceGraphDerivedEquivalence_functor (hF : QuasiEquivalence F) :
    (dgFunctorDerivedEquivalence A D E F hF).functor =
      kernelDerivedTensorOnBimodule A D E (functorGraph A D E F) := rfl

@[instance_reducible]
def quasiEquivalenceGraphActionCommShift :
    (kernelDerivedTensorOnBimodule A D E (functorGraph A D E F)).CommShift ℤ :=
  dgDerivedExtensionCommShift A D E F

attribute [local instance] quasiEquivalenceGraphActionCommShift
local instance moritaGraphActionExtensionShift : (dgDerivedExtension A D E F).CommShift ℤ :=
  dgDerivedExtensionCommShift A D E F

lemma quasiEquivalenceGraphActionIsoCommShift :
    NatTrans.CommShift (quasiEquivalenceGraphActionIso A D E F).hom ℤ := by
  change NatTrans.CommShift (𝟙 (dgDerivedExtension A D E F)) ℤ
  infer_instance

lemma quasiEquivalenceGraphActionIsTriangulated :
    (kernelDerivedTensorOnBimodule A D E (functorGraph A D E F)).IsTriangulated :=
  dgDerivedExtensionIsTriangulated A D E F

lemma quasiEquivalenceGraphAction_perfect {X : DerivedModuleCategory A D}
    (hX : modulePerfect A D X) :
    modulePerfect A E
      ((kernelDerivedTensorOnBimodule A D E (functorGraph A D E F)).obj X) :=
  dgDerivedExtension_perfect A D E F hX

def quasiEquivalenceGraphActionOnPerfectIso :
    perfectFunctorRestriction A D E
        (kernelDerivedTensorOnBimodule A D E (functorGraph A D E F))
        (fun _ h => quasiEquivalenceGraphAction_perfect A D E F h) ≅
      quasiEquivalencePerfectExtension A D E F :=
  perfectFunctorIso A D E _ _
    (fun _ h => quasiEquivalenceGraphAction_perfect A D E F h)
    (fun _ h => dgDerivedExtension_perfect A D E F h)
    (quasiEquivalenceGraphActionIso A D E F)

/-- 自然モデルから復元した比較も、公開された実際のgraph比較と一致する。 -/
lemma quasiEquivalenceGraphActionComparisonOfModel
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    quasiEquivalenceGraphComparisonOfModel A D E F R
        (kernelDerivedTensorOnBimodule A D E (functorGraph A D E F))
        (Functor.isoWhiskerLeft (moduleToDerived A D) (quasiEquivalenceGraphActionIso A D E F) ≪≫
          quasiEquivalenceGraphDerivedModelIso A D E F R) =
      quasiEquivalenceGraphActionIso A D E F := by
  apply Iso.ext
  symm
  apply quasiEquivalenceGraphComparisonOfModel_unique
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

end SerrePositivity.DifferentialGraded.Morita
