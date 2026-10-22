module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelCone
public import SerrePositivity.InfinityCategories.Derived.Gluing.ClosedSquareHomotopy

/-! 元の閉 comma 射の右成分の cone を、同じ通常 tensor の代表加群 cone の像へ比較する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y : DGFunctorCommaObject R D (RightModule R C) M.toFunctor)
  (f : ForgetEnrichment.of (Complex R) X ⟶ ForgetEnrichment.of (Complex R) Y)

omit [Small.{u} D] in
/-- 同じ右成分の閉射作用を、元の双加群関手の閉射作用として厳密に回収する。 -/
lemma dgGluingCommaClosedSourceMap_eq :
    dgGluingCommaClosedSourceMap R C D M X Y f =
    M.toFunctor.onClosed.map
      ((dgFunctorCommaSource R D (RightModule R C) M.toFunctor).onClosed.map f) := by
  change ForgetEnrichment.homTo (Complex R) f ≫
      (dgFunctorCommaSourceHomMap R D (RightModule R C) M.toFunctor X Y ≫
        M.toFunctor.map X.source Y.source) =
    (ForgetEnrichment.homTo (Complex R) f ≫
      dgFunctorCommaSourceHomMap R D (RightModule R C) M.toFunctor X Y) ≫
        M.toFunctor.map X.source Y.source
  exact (Category.assoc _ _ _).symm

/-- 元の閉射に対する、右成分の cone の実 tensor 比較。 -/
def dgGluingCommaKernelConeIso :
    moduleCone R C (dgGluingCommaClosedSourceMap R C D M X Y f) ≅
    (Morita.kernelTensor R D C M).onClosed.obj
      (moduleCone R D ((dgYoneda R D).onClosed.map
        ((dgFunctorCommaSource R D (RightModule R C) M.toFunctor).onClosed.map f))) :=
  eqToIso (congrArg (fun a ↦ moduleCone R C a)
    (dgGluingCommaClosedSourceMap_eq R C D M X Y f)) ≪≫
    dgGluingKernelConeIso R C D M
      ((dgFunctorCommaSource R D (RightModule R C) M.toFunctor).onClosed.map f)

end SerrePositivity.InfinityCategories
