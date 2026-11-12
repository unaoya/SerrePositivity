module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitCapFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NormalizationStandardCompositionFaces

/-! # 元入力を保つ標準合成面への実単位補正

概要：前側と終側の補正端を、元の二つの入力を持つ標準合成三角形へつなぐ。
方針：同じ augmentation 面へ単位補正の再添字を適用し、実射影の自然性で端を同定する。
規約：元固定辺・全時間の可変入力・両補正端を厳密に回収する。
使われ方：共有四面体を含む相対二次元比較の左右の標準面を供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
  {K : SSet.{max u v}} (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)) X Y)

def dgGluingPreUnitCapTriangleFamily :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCap ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeAugmentationTriangle R E X Y f ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max u v, max u v} R E)

def dgGluingExitUnitCapTriangleFamily :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCap ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitAugmentationTriangle R E X Y f ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max u v, max u v} R E)

lemma dgGluingPreUnitCapTriangleFamily_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫ dgGluingPreUnitCapTriangleFamily R E X Y f =
      fst (Δ[1] : SSet.{max u v}) (K ⊗ Δ[1]) ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E X.augmentation).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCapFamily_first _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeUnitCollarSide R E X Y f)

lemma dgGluingPreUnitCapTriangleFamily_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫ dgGluingPreUnitCapTriangleFamily R E X Y f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (fst K (Δ[1] : SSet.{max u v}) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaSourceIntervalFamily R E X Y f) := by
  have h : (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCap =
      (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollar := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCapFamily_last, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollarFamily_last]
  have ht := congrArg (fun s => s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeAugmentationTriangle R E X Y f ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max u v, max u v} R E)) h
  calc
    _ = (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeUnitCollarTriangleFamily R E X Y f := by
      simpa only [dgGluingPreUnitCapTriangleFamily,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeUnitCollarTriangleFamily, Category.assoc] using ht
    _ = _ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeUnitCollarTriangleFamily_last_input R E X Y f

lemma dgGluingPreUnitCapTriangleFamily_zero :
    (Δ[2] ◁ (ι₀ : K ⟶ _)) ≫ dgGluingPreUnitCapTriangleFamily R E X Y f =
      (Δ[2] ◁ (ι₀ : K ⟶ _)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeUnitCollarTriangleFamily R E X Y f := by
  have h := congrArg (fun s => s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeAugmentationTriangle R E X Y f ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max u v, max u v} R E))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCapFamily_zero (K := K))
  simpa only [dgGluingPreUnitCapTriangleFamily,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeUnitCollarTriangleFamily, Category.assoc] using h

lemma dgGluingPreUnitCapTriangleFamily_one :
    (Δ[2] ◁ (ι₁ : K ⟶ _)) ≫ dgGluingPreUnitCapTriangleFamily R E X Y f =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R E
        (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R E X.augmentation))
        (f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R E E (DGFunctor.id E)).map X Y)) := by
  rw [dgGluingPreUnitCapTriangleFamily, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCapFamily_one]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreAugmentationTriangle_target_standard R E X Y f

lemma dgGluingExitUnitCapTriangleFamily_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫ dgGluingExitUnitCapTriangleFamily R E X Y f =
      fst (Δ[1] : SSet.{max u v}) (K ⊗ Δ[1]) ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E Y.augmentation).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCapFamily_last _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCollarSide R E X Y f)

lemma dgGluingExitUnitCapTriangleFamily_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫ dgGluingExitUnitCapTriangleFamily R E X Y f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (fst K (Δ[1] : SSet.{max u v}) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaReplacementIntervalFamily R E X Y f) := by
  have h : (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCap =
      (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCapFamily_first, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollarFamily_first]
  have ht := congrArg (fun s => s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitAugmentationTriangle R E X Y f ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max u v, max u v} R E)) h
  calc
    _ = (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCollarTriangleFamily R E X Y f := by
      simpa only [dgGluingExitUnitCapTriangleFamily,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCollarTriangleFamily, Category.assoc] using ht
    _ = _ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCollarTriangleFamily_first_original R E X Y f

lemma dgGluingExitUnitCapTriangleFamily_zero :
    (Δ[2] ◁ (ι₀ : K ⟶ _)) ≫ dgGluingExitUnitCapTriangleFamily R E X Y f =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R E
        (f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R E E (DGFunctor.id E)).map X Y))
        (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R E Y.augmentation)) := by
  rw [dgGluingExitUnitCapTriangleFamily, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCapFamily_zero]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitAugmentationTriangle_source_standard R E X Y f

lemma dgGluingExitUnitCapTriangleFamily_one :
    (Δ[2] ◁ (ι₁ : K ⟶ _)) ≫ dgGluingExitUnitCapTriangleFamily R E X Y f =
      (Δ[2] ◁ (ι₁ : K ⟶ _)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCollarTriangleFamily R E X Y f := by
  have h := congrArg (fun s => s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitAugmentationTriangle R E X Y f ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max u v, max u v} R E))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCapFamily_one (K := K))
  simpa only [dgGluingExitUnitCapTriangleFamily,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCollarTriangleFamily, Category.assoc] using h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
