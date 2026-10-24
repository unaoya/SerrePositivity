module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitCapFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationStandardCompositionFaces

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) [DGCategory R E]
  (X Y : DGFunctorCommaObject R E E (DGFunctor.id E))
  {K : SSet.{max u v}} (f : K ⟶ DGNerve.pinchedHom R
    (DGFunctorCommaObject R E E (DGFunctor.id E)) X Y)

def dgGluingPreUnitCapTriangleFamily :=
  dgGluingTriangleTimeReindex dgGluingFirstUnitCap ≫
    dgGluingPreNormalizeAugmentationTriangle R E X Y f ≫
      dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)

def dgGluingExitUnitCapTriangleFamily :=
  dgGluingTriangleTimeReindex dgGluingLastUnitCap ≫
    dgGluingExitAugmentationTriangle R E X Y f ≫
      dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)

lemma dgGluingPreUnitCapTriangleFamily_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫ dgGluingPreUnitCapTriangleFamily R E X Y f =
      fst (Δ[1] : SSet.{max u v}) (K ⊗ Δ[1]) ≫
        SSet.yonedaEquiv.symm (dgClosedEdge R E X.augmentation).edge :=
  dgGluingFirstUnitCapFamily_first _ _ (dgGluingPreNormalizeUnitCollarSide R E X Y f)

lemma dgGluingPreUnitCapTriangleFamily_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫ dgGluingPreUnitCapTriangleFamily R E X Y f =
      intervalMappingUncurry (fst K (Δ[1] : SSet.{max u v}) ≫
        dgGluingIdentityCommaSourceIntervalFamily R E X Y f) := by
  have h : (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      dgGluingTriangleTimeReindex dgGluingFirstUnitCap =
      (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
        dgGluingTriangleTimeReindex dgGluingFirstUnitCollar := by
    rw [dgGluingFirstUnitCapFamily_last, dgGluingFirstUnitCollarFamily_last]
  have ht := congrArg (fun s => s ≫ dgGluingPreNormalizeAugmentationTriangle R E X Y f ≫
    dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) h
  calc
    _ = (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
        dgGluingPreNormalizeUnitCollarTriangleFamily R E X Y f := by
      simpa only [dgGluingPreUnitCapTriangleFamily,
        dgGluingPreNormalizeUnitCollarTriangleFamily, Category.assoc] using ht
    _ = _ := dgGluingPreNormalizeUnitCollarTriangleFamily_last_input R E X Y f

lemma dgGluingPreUnitCapTriangleFamily_zero :
    (Δ[2] ◁ (ι₀ : K ⟶ _)) ≫ dgGluingPreUnitCapTriangleFamily R E X Y f =
      (Δ[2] ◁ (ι₀ : K ⟶ _)) ≫ dgGluingPreNormalizeUnitCollarTriangleFamily R E X Y f := by
  have h := congrArg (fun s => s ≫ dgGluingPreNormalizeAugmentationTriangle R E X Y f ≫
    dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E))
    (dgGluingFirstUnitCapFamily_zero (K := K))
  simpa only [dgGluingPreUnitCapTriangleFamily,
    dgGluingPreNormalizeUnitCollarTriangleFamily, Category.assoc] using h

lemma dgGluingPreUnitCapTriangleFamily_one :
    (Δ[2] ◁ (ι₁ : K ⟶ _)) ≫ dgGluingPreUnitCapTriangleFamily R E X Y f =
      dgGluingDGCompositionTriangleFamily R E
        (SSet.const (X := K) (pinchedClosedVertex R E X.augmentation))
        (f ≫ pinchedHomChainMap ((dgFunctorCommaSource R E E (DGFunctor.id E)).map X Y)) := by
  rw [dgGluingPreUnitCapTriangleFamily, ← Category.assoc, dgGluingFirstUnitCapFamily_one]
  exact dgGluingPreAugmentationTriangle_target_standard R E X Y f

lemma dgGluingExitUnitCapTriangleFamily_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫ dgGluingExitUnitCapTriangleFamily R E X Y f =
      fst (Δ[1] : SSet.{max u v}) (K ⊗ Δ[1]) ≫
        SSet.yonedaEquiv.symm (dgClosedEdge R E Y.augmentation).edge :=
  dgGluingLastUnitCapFamily_last _ _ (dgGluingExitUnitCollarSide R E X Y f)

lemma dgGluingExitUnitCapTriangleFamily_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫ dgGluingExitUnitCapTriangleFamily R E X Y f =
      intervalMappingUncurry (fst K (Δ[1] : SSet.{max u v}) ≫
        dgGluingIdentityCommaReplacementIntervalFamily R E X Y f) := by
  have h : (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      dgGluingTriangleTimeReindex dgGluingLastUnitCap =
      (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
        dgGluingTriangleTimeReindex dgGluingLastUnitCollar := by
    rw [dgGluingLastUnitCapFamily_first, dgGluingLastUnitCollarFamily_first]
  have ht := congrArg (fun s => s ≫ dgGluingExitAugmentationTriangle R E X Y f ≫
    dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) h
  calc
    _ = (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
        dgGluingExitUnitCollarTriangleFamily R E X Y f := by
      simpa only [dgGluingExitUnitCapTriangleFamily,
        dgGluingExitUnitCollarTriangleFamily, Category.assoc] using ht
    _ = _ := dgGluingExitUnitCollarTriangleFamily_first_original R E X Y f

lemma dgGluingExitUnitCapTriangleFamily_zero :
    (Δ[2] ◁ (ι₀ : K ⟶ _)) ≫ dgGluingExitUnitCapTriangleFamily R E X Y f =
      dgGluingDGCompositionTriangleFamily R E
        (f ≫ pinchedHomChainMap ((dgFunctorCommaReplacement R E E (DGFunctor.id E)).map X Y))
        (SSet.const (X := K) (pinchedClosedVertex R E Y.augmentation)) := by
  rw [dgGluingExitUnitCapTriangleFamily, ← Category.assoc, dgGluingLastUnitCapFamily_zero]
  exact dgGluingExitAugmentationTriangle_source_standard R E X Y f

lemma dgGluingExitUnitCapTriangleFamily_one :
    (Δ[2] ◁ (ι₁ : K ⟶ _)) ≫ dgGluingExitUnitCapTriangleFamily R E X Y f =
      (Δ[2] ◁ (ι₁ : K ⟶ _)) ≫ dgGluingExitUnitCollarTriangleFamily R E X Y f := by
  have h := congrArg (fun s => s ≫ dgGluingExitAugmentationTriangle R E X Y f ≫
    dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E))
    (dgGluingLastUnitCapFamily_one (K := K))
  simpa only [dgGluingExitUnitCapTriangleFamily,
    dgGluingExitUnitCollarTriangleFamily, Category.assoc] using h

end SerrePositivity.InfinityCategories
