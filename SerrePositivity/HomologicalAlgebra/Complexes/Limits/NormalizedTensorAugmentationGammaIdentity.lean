module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.StandardDoldKanZeroRawEvaluation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorAugmentationRawIdentity
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.OrdinaryDerivedSource
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedClosedStandardConstant

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
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories

open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

lemma complexClosedIdentity_value (X : Complex A) :
    (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (𝟙 X))).val =
      CochainComplex.HomComplex.Cochain.ofHom (𝟙 X) := by
  rw [CategoryTheory.Functor.map_id, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_id]
  change (cycleFromUnit (homComplex A X X) (identity X)).val = _
  rw [identity, cycleFromUnit_unitFromCycle]

def complexIdentityDoldKanVertex (X : Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomSpace (R := A) (D := Complex A) X X) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardDoldKanModuleIso (R := A) X X).hom.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (𝟙 X))) 0)

lemma complexIdentityDoldKanVertex_raw (X : Complex A) :
    _root_.SerrePositivity.ComplexLimits.truncationExtendedZeroInclusion A ComplexShape.embeddingDownNat
      _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero rfl (homComplex A X X)
      ((_root_.SerrePositivity.ComplexLimits.gammaDegreeZeroIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex (R := A) X X)).hom
        (_root_.SerrePositivity.ComplexLimits.complexIdentityDoldKanVertex A X)) = CochainComplex.HomComplex.Cochain.ofHom (𝟙 X) := by
  have h0 := _root_.SerrePositivity.ComplexLimits.standardDoldKanModuleIso_zero_raw (R := A) (D := Complex A) X X
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (𝟙 X))) 0)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant_singleton
    (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (𝟙 X))) (0 : Fin 1)
  have h' : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant
      (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (𝟙 X))) 0).val.component
      Finset.univ 0 Finset.univ_nonempty (by simp) =
      (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (𝟙 X))).val := by
    simpa only [show (Finset.univ : Finset (Fin 1)) = {0} from by decide] using h
  exact h0.trans (h'.trans (_root_.SerrePositivity.ComplexLimits.complexClosedIdentity_value A X))

lemma normalizedTensorAugmentation_gamma_zero_eq (X : Complex A) :
    _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomEquiv A X X ⦋0⦌
      ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation A X).app ⦋0⦌) = _root_.SerrePositivity.ComplexLimits.complexIdentityDoldKanVertex A X := by
  apply _root_.SerrePositivity.ComplexLimits.gammaDegreeZero_raw_injective A (homComplex A X X)
  exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorAugmentation_gamma_zero_raw A X).trans
    (_root_.SerrePositivity.ComplexLimits.complexIdentityDoldKanVertex_raw A X).symm

end SerrePositivity.ComplexLimits
