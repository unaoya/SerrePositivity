module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSimplicialRingShuffleNative
/-!
概要：実 Moore 複体の次数別乗法と同じ shuffle 射影公式。
方針：元の実 tensor 鎖写像の成分・包含・正規化射影を照合する。
規約：選ばれた乗法そのものを保持する。使われ方：β5(g) の正規化 dg 代数化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite AlgebraicTopology AlgebraicTopology.DoldKan HomologicalComplex

open scoped _root_.Simplicial
variable (A : SimplicialObject RingCat.{u})
local notation "C" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A
local notation "N" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A
local notation "I" => inclusionOfMooreComplexMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)
local notation "P" => PInftyToNormalizedMooreComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)
local notation "mu" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerMultiplication A
lemma simplicialRingNormalizedMultiplication_rawFactor :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMultiplication A =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap I I ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffle C C ≫
        (alternatingFaceMapComplex _).map mu ≫ P := by
  have h := congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap I I ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffle C C ≫ f)
    (PInftyToNormalizedMooreComplex_naturality mu).symm
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMultiplication, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedShuffle, Category.assoc] using! h

def simplicialRingNormalizedDegreeProduct (p q : ℕ) (x : (N).X p) (y : (N).X q) :
    (N).X (p + q) :=
  (ιMapBifunctor N N _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) p q (p + q) rfl ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMultiplication A).f (p + q)).hom (TensorProduct.tmul ℤ x y)

lemma simplicialRingNormalizedMultiplication_bidegree (p q : ℕ) :
    ιMapBifunctor N N _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) p q (p + q) rfl ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMultiplication A).f (p + q) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap ((I).f p) ((I).f q) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBidegree C C p q (p + q) rfl ≫
        (mu).app (op ⦋p + q⦌) ≫ (P).f (p + q) := by
  rw [simplicialRingNormalizedMultiplication_rawFactor]
  simp only [comp_f]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ι_chainIntegerTensorMap]
  simp only [Category.assoc]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap ((I).f p) ((I).f q) ≫
    ιMapBifunctor ((alternatingFaceMapComplex _).obj C)
      ((alternatingFaceMapComplex _).obj C) _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ)
      p q (p + q) rfl ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleApp C C (p + q) ≫
        (mu).app (op ⦋p + q⦌) ≫ (P).f (p + q) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ι_shuffleApp_assoc]
lemma simplicialRingNormalizedDegreeProduct_value (p q : ℕ) (x : (N).X p) (y : (N).X q) :
    simplicialRingNormalizedDegreeProduct A p q x y = (P).f (p + q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct A p q (((I).f p).hom x) (((I).f q).hom y)) := by
  change (ιMapBifunctor N N _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) p q (p + q) rfl ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMultiplication A).f (p + q)).hom (TensorProduct.tmul ℤ x y) = _
  rw [simplicialRingNormalizedMultiplication_bidegree]
  change ((P).f (p + q)).hom
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBidegree C C p q (p + q) rfl ≫ (mu).app (op ⦋p + q⦌)).hom
      (TensorProduct.map ((I).f p).hom ((I).f q).hom (TensorProduct.tmul ℤ x y))) = _
  rw [TensorProduct.map_tmul, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct_eq_shuffleBidegree]
lemma simplicialRingNormalizedDegreeProduct_inclusion (p q : ℕ) (x : (N).X p) (y : (N).X q) :
    ((I).f (p + q)).hom (simplicialRingNormalizedDegreeProduct A p q x y) =
      ((PInfty (X := C)).f (p + q)).hom
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct A p q (((I).f p).hom x) (((I).f q).hom y)) := by
  rw [simplicialRingNormalizedDegreeProduct_value]
  have h := congrArg (fun f ↦ (f.f (p + q)).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct A p q (((I).f p).hom x) (((I).f q).hom y)))
      (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap C)
  exact h
lemma simplicialRingNormalizedInclusion_injective (n : ℕ) :
    Function.Injective (((I).f n).hom) := by
  apply (ModuleCat.mono_iff_injective ((I).f n)).mp
  change Mono (NormalizedMooreComplex.objX C n).arrow
  infer_instance
def simplicialRingNormalizedOne : (N).X 0 := ((P).f 0).hom (1 : A.obj (op ⦋0⦌))
lemma simplicialRingNormalizedOne_inclusion :
    ((I).f 0).hom (simplicialRingNormalizedOne A) = (1 : A.obj (op ⦋0⦌)) := by
  have h := congrArg (fun f ↦ (f.f 0).hom (1 : A.obj (op ⦋0⦌)))
    (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap C)
  simpa only [simplicialRingNormalizedOne, comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    PInfty_f_0, ModuleCat.hom_id, LinearMap.id_apply] using! h
lemma simplicialRingNormalizedDegreeProduct_right_unit (p : ℕ) (x : (N).X p) :
    simplicialRingNormalizedDegreeProduct A p 0 x (simplicialRingNormalizedOne A) = x := by
  apply simplicialRingNormalizedInclusion_injective A p
  have h := simplicialRingNormalizedDegreeProduct_inclusion A p 0 x
    (simplicialRingNormalizedOne A)
  rw [simplicialRingNormalizedOne_inclusion, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct_right_unit] at h
  exact h.trans (congrArg (fun f ↦ (f.f p).hom x) (inclusionOfMooreComplexMap_comp_PInfty C))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
