module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexCochainAugmentationZero
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexTensorAugmentation
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits

/-!
# 同じ正規化テンソル augmentation の零次数 curry は元の恒等射

概要：元の augmentation の curry を同じ零次数生成元で評価すると恒等 cochain になる。
方針：同じ右単位子の curry と単体 augmentation の生成元での値を使う。
規約：元の Hom 同値・augmentation・生成元を保つ。
使われ方：正規化 Hom の零次数像と元の恒等辺の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

lemma normalizedTensorAugmentation_curry (X : Complex A) (n : SimplexCategory) :
    tensorHomEquiv X ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n)) X
      ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation A X).app n) =
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).hom ≫ MonoidalClosed.id X := by
  change tensorHomEquiv X _ X
    ((X ◁ (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).hom) ≫ (ρ_ X).hom) = _
  rw [tensorHomEquiv_naturality_source]
  rfl

lemma normalizedSimplexCochainAugmentation_zero_generator_eq :
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A ⦋0⦌).hom.f 0 (_root_.SerrePositivity.ComplexLimits.normalizedSimplexZeroGenerator A) =
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) := by
  apply (ModuleCat.mono_iff_injective (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom).mp
    inferInstance
  simpa only [Iso.inv_hom_id_apply] using _root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainAugmentation_zero_generator A

lemma normalizedTensorAugmentation_curry_zero (X : Complex A) :
    (tensorHomEquiv X ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj ⦋0⦌)) X
      ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation A X).app ⦋0⦌)).f 0
        (_root_.SerrePositivity.ComplexLimits.normalizedSimplexZeroGenerator A) = CochainComplex.HomComplex.Cochain.ofHom (𝟙 X) := by
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorAugmentation_curry]
  change (MonoidalClosed.id X).f 0
    ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A ⦋0⦌).hom.f 0 (_root_.SerrePositivity.ComplexLimits.normalizedSimplexZeroGenerator A)) = _
  rw [_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainAugmentation_zero_generator_eq]
  change (cycleFromUnit (homComplex A X X) (MonoidalClosed.id X)).val = _
  rw [closedIdentity_eq, identity, cycleFromUnit_unitFromCycle]

end SerrePositivity.ComplexLimits
