module
public import SerrePositivity.DifferentialGraded.Tensor.RightUnit
public import SerrePositivity.DifferentialGraded.Module.YonedaFunctor
public import SerrePositivity.DifferentialGraded.Derived.Restriction

/-! # dg関手のgraph bimoduleによる加群延長

Hom_E(e,Fd)を値とする右E・左D bimoduleを既存tensor合成へ入力する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- dg関手のgraph。各D対象でE上の実際の代表右加群となる。 -/
def functorGraph : Bimodule A E D := F.comp (dgYoneda A E)

omit [Small.{u} D] in
lemma functorGraph_value (e : E) (d : D) :
    (functorGraph A D E F).value e d = homObject A E e (F.obj d) := rfl

/-- graphとのtensorによる右dg加群の延長。全加群型のsmallnessは不要。 -/
def dgModuleExtension : DGFunctor A (RightModule A D) (RightModule A E) :=
  (BimoduleTensor.compose A E D (RightModule A D) (functorGraph A D E F)
    (DGFunctor.id (RightModule A D))).toFunctor

lemma dgModuleExtension_value (M : RightModule A D) (e : E) :
    ((dgModuleExtension A D E F).obj M).obj (op e) =
      BalancedTensor.obj A D M ((functorGraph A D E F).leftAt e) := rfl

/-- 代表加群の延長は対応するEの代表加群。Hom flatness仮定は不要。 -/
def dgModuleExtensionRepresentableIso (d : D) :
    ForgetEnrichment.of (Complex A) ((dgModuleExtension A D E F).obj (representable A d)) ≅
      ForgetEnrichment.of (Complex A) (representable A (F.obj d)) :=
  BimoduleTensor.rightUnitIso A E D (functorGraph A D E F) d

end SerrePositivity.DifferentialGraded
