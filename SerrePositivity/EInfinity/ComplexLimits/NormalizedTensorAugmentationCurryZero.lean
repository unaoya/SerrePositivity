module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexCochainAugmentationZero
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexTensorAugmentation
public import SerrePositivity.DifferentialGraded.Complexes.Enrichment

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma normalizedTensorAugmentation_curry (X : Complex A) (n : SimplexCategory) :
    tensorHomEquiv X ((BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n)) X
      ((normalizedSimplexTensorAugmentation A X).app n) =
    (normalizedSimplexCochainContraction A n).hom ≫ MonoidalClosed.id X := by
  change tensorHomEquiv X _ X
    ((X ◁ (normalizedSimplexCochainContraction A n).hom) ≫ (ρ_ X).hom) = _
  rw [tensorHomEquiv_naturality_source]
  rfl

lemma normalizedSimplexCochainAugmentation_zero_generator_eq :
    (normalizedSimplexCochainContraction A ⦋0⦌).hom.f 0 (normalizedSimplexZeroGenerator A) =
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) := by
  apply (ModuleCat.mono_iff_injective (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom).mp
    inferInstance
  simpa only [Iso.inv_hom_id_apply] using normalizedSimplexCochainAugmentation_zero_generator A

lemma normalizedTensorAugmentation_curry_zero (X : Complex A) :
    (tensorHomEquiv X ((BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj ⦋0⦌)) X
      ((normalizedSimplexTensorAugmentation A X).app ⦋0⦌)).f 0
        (normalizedSimplexZeroGenerator A) = CochainComplex.HomComplex.Cochain.ofHom (𝟙 X) := by
  rw [normalizedTensorAugmentation_curry]
  change (MonoidalClosed.id X).f 0
    ((normalizedSimplexCochainContraction A ⦋0⦌).hom.f 0 (normalizedSimplexZeroGenerator A)) = _
  rw [normalizedSimplexCochainAugmentation_zero_generator_eq]
  change (cycleFromUnit (homComplex A X X) (MonoidalClosed.id X)).val = _
  rw [closedIdentity_eq, identity, cycleFromUnit_unitFromCycle]

end SerrePositivity.EInfinity.ComplexLimits
