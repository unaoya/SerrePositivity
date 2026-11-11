module

public import SerrePositivity.EInfinity.ComplexLimits.StandardDoldKanZeroRawEvaluation
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorAugmentationRawIdentity
public import SerrePositivity.EInfinity.ComplexLimits.OrdinaryDerivedSource
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedClosedStandardConstant

/-!
# 同じ正規化 augmentation と標準閉恒等辺の Γ 零次数像の一致

概要：元の二つの零次数像を同じ単射な直接評価で照合する。
方針：元の標準定数の全体集合成分と元の恒等 cochain を比較する。
規約：元の Γ・標準同型・正規化 Hom 同値を保つ。
使われ方：普遍 Hom 族の augmentation 像を元の恒等辺に同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma complexClosedIdentity_value (X : Complex A) :
    (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map (𝟙 X))).val =
      CochainComplex.HomComplex.Cochain.ofHom (𝟙 X) := by
  rw [CategoryTheory.Functor.map_id, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_id]
  change (cycleFromUnit (homComplex A X X) (identity X)).val = _
  rw [identity, cycleFromUnit_unitFromCycle]

def complexIdentityDoldKanVertex (X : Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomSpace (R := A) (D := Complex A) X X) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardDoldKanModuleIso (R := A) X X).hom.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map (𝟙 X))) 0)

lemma complexIdentityDoldKanVertex_raw (X : Complex A) :
    truncationExtendedZeroInclusion A ComplexShape.embeddingDownNat
      embeddingDownNat_eq_upIntLE_zero rfl (homComplex A X X)
      ((gammaDegreeZeroIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex (R := A) X X)).hom
        (complexIdentityDoldKanVertex A X)) = CochainComplex.HomComplex.Cochain.ofHom (𝟙 X) := by
  have h0 := standardDoldKanModuleIso_zero_raw (R := A) (D := Complex A) X X
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map (𝟙 X))) 0)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant_singleton
    (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map (𝟙 X))) (0 : Fin 1)
  have h' : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant
      (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map (𝟙 X))) 0).val.component
      Finset.univ 0 Finset.univ_nonempty (by simp) =
      (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map (𝟙 X))).val := by
    simpa only [show (Finset.univ : Finset (Fin 1)) = {0} from by decide] using h
  exact h0.trans (h'.trans (complexClosedIdentity_value A X))

lemma normalizedTensorAugmentation_gamma_zero_eq (X : Complex A) :
    normalizedSimplexTensorHomEquiv A X X ⦋0⦌
      ((normalizedSimplexTensorAugmentation A X).app ⦋0⦌) = complexIdentityDoldKanVertex A X := by
  apply gammaDegreeZero_raw_injective A (homComplex A X X)
  exact (normalizedTensorAugmentation_gamma_zero_raw A X).trans
    (complexIdentityDoldKanVertex_raw A X).symm

end SerrePositivity.EInfinity.ComplexLimits
