module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeStandardCoefficientInputs
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseCompositionTriangleInputs
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationUnitCaps
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseCanonicalCoefficientTriangles
/-! # native 単位補正の標準端と正本係数三角形

概要：二つの単位補正族の標準端を、正本係数三角形そのものへ同定する。
方針：標準面の二入力の因子分解を、同じ coherent 三角形の入力外延性へ入れる。
規約：全三角形・元 Hom 入力・実 augmentation を選び直さない。
使われ方：実三変形の相対比較と選択済み二変形を接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
private lemma dgGluingUliftSimplexFamily_post {K E F : SSet.{u}} (n : ℕ)
    (h : (Δ[n] : SSet.{u}) ⊗ K ⟶ E) (q : E ⟶ F) :
    dgGluingUliftSimplexFamily.{u, v} n (h ≫ q) =
      dgGluingUliftSimplexFamily.{u, v} n h ≫ (SSet.uliftFunctor.{v, u}).map q := by
  simp only [dgGluingUliftSimplexFamily, CategoryTheory.Functor.map_comp, Category.assoc]
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "RM" => RightModule R C
local notation "IX" => dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => dgGluingNativeIdentityCommaObject R C D M Y
local notation "P" => dgGluingNativePinchedHomParameter R C D M X Y

def dgGluingNativeRightCoefficientTriangleParameter := dgGluingNativeHomModelMap R C D M X Y ≫
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y)) ≫
    (dgGluingComplexPinchedUniverseIso.{u, max u v w, max (u + 1) v}
      (homObject R D X.right Y.right)).hom

def dgGluingNativeRightProjectedStandardTriangle :=
  (Δ[2] ◁ dgGluingNativeNormalizationHomInput R C D M X Y) ≫
    dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 2
      (dgGluingDGCompositionTriangleFamily R RM
        (SSet.const (pinchedClosedVertex R RM (IX).augmentation))
        (𝟙 _ ≫ pinchedHomChainMap ((dgFunctorCommaSource R RM RM (DGFunctor.id RM)).map IX IY)))

lemma dgGluingNativePreUnitCapTriangleFamily_one_standard :
    (Δ[2] ◁ (ι₁ : P ⟶ _)) ≫ dgGluingNativePreUnitCapTriangleFamily R C D M X Y =
      dgGluingNativeRightProjectedStandardTriangle R C D M X Y ≫
        dgGluingUniverseModuleDerivedComparison.{u, v, w} R C := by
  have he := dgGluingTriangleTimeTransport_endpoint.{max (u + 1) v,
      max (u + 1) v w} 2 1
    (dgGluingPreUnitCapTriangleFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _))
    (dgGluingNativeNormalizationHomInput R C D M X Y)
    (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
  simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false] at he
  rw [dgGluingNativePreUnitCapTriangleFamily, he,
    dgGluingPreUnitCapTriangleFamily_one R RM IX IY (𝟙 _)]
  rfl

lemma dgGluingNativeRightProjectedStandardTriangle_inputs :
    dgGluingNativeRightProjectedStandardTriangle R C D M X Y =
      (Δ[2] ◁ dgGluingNativeRightCoefficientTriangleParameter R C D M X Y) ≫
      dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 2
        (dgGluingDGCompositionTriangleFamily R RM
          (SSet.const (pinchedClosedVertex R RM (dgGluingAugmentation R C D M X)))
          (dgGluingNativeRightCoefficientInput R C D M X Y)) := by
  have ht := dgGluingUliftDGCompositionTriangleFamily_input_ext.{u, max (u + 1) v,
      max (u + 1) v w} R RM
    (SSet.const (pinchedClosedVertex R RM (dgGluingAugmentation R C D M X)))
    (𝟙 _ ≫ pinchedHomChainMap ((dgFunctorCommaSource R RM RM (DGFunctor.id RM)).map IX IY))
    (SSet.const (pinchedClosedVertex R RM (dgGluingAugmentation R C D M X)))
    (dgGluingNativeRightCoefficientInput R C D M X Y)
    (dgGluingNativeNormalizationHomInput R C D M X Y)
      (dgGluingNativeRightCoefficientTriangleParameter R C D M X Y)
    (by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl)
    (by simpa only [dgGluingNativeRightCoefficientTriangleParameter,
      Category.id_comp, Category.assoc] using
      dgGluingNativeNormalizationHomInput_source_factor R C D M X Y)
  exact ht

lemma dgGluingNativeRightCoefficientTriangleParameter_canonical :
    ((Δ[2] ◁ dgGluingNativeRightCoefficientTriangleParameter R C D M X Y) ≫
      dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 2
        (dgGluingDGCompositionTriangleFamily R RM
          (SSet.const (pinchedClosedVertex R RM (dgGluingAugmentation R C D M X)))
          (dgGluingNativeRightCoefficientInput R C D M X Y))) ≫
      dgGluingUniverseModuleDerivedComparison.{u, v, w} R C =
      (Δ[2] ◁ dgGluingNativeHomModelMap R C D M X Y) ≫
        dgGluingHomDerivedRightCoefficientTriangle R C D M X Y := by
  simp only [dgGluingNativeRightCoefficientTriangleParameter,
    dgGluingHomDerivedRightCoefficientTriangle_canonical R C D M X Y,
    dgGluingUniverseModuleDerivedSimplexFamily,
    dgGluingCanonicalDerivedRightCoefficientTriangleFamily,
    dgGluingDGCompositionTriangleFamilyPost, dgGluingUliftSimplexFamily_post,
    dgGluingUniverseModuleDerivedComparison, whiskerLeft_comp, Category.assoc]

lemma dgGluingNativePreUnitCapTriangleFamily_one_canonical :
    (Δ[2] ◁ (ι₁ : P ⟶ _)) ≫ dgGluingNativePreUnitCapTriangleFamily R C D M X Y =
      (Δ[2] ◁ dgGluingNativeHomModelMap R C D M X Y) ≫
        dgGluingHomDerivedRightCoefficientTriangle R C D M X Y := by
  rw [dgGluingNativePreUnitCapTriangleFamily_one_standard R C D M X Y,
    dgGluingNativeRightProjectedStandardTriangle_inputs R C D M X Y,
    dgGluingNativeRightCoefficientTriangleParameter_canonical R C D M X Y]

def dgGluingNativeLeftCoefficientTriangleParameter := dgGluingNativeHomModelMap R C D M X Y ≫
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)) ≫
    (dgGluingComplexPinchedUniverseIso.{u, max u v w, max (u + 1) v}
      (homObject R C X.left Y.left)).hom

def dgGluingNativeLeftProjectedStandardTriangle :=
  (Δ[2] ◁ dgGluingNativeNormalizationHomInput R C D M X Y) ≫
    dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 2
      (dgGluingDGCompositionTriangleFamily R RM
        (𝟙 _ ≫ pinchedHomChainMap ((dgFunctorCommaReplacement R RM RM (DGFunctor.id RM)).map IX IY))
        (SSet.const (pinchedClosedVertex R RM (IY).augmentation)))

lemma dgGluingNativeExitUnitCapTriangleFamily_zero_standard :
    (Δ[2] ◁ (ι₀ : P ⟶ _)) ≫ dgGluingNativeExitUnitCapTriangleFamily R C D M X Y =
      dgGluingNativeLeftProjectedStandardTriangle R C D M X Y ≫
        dgGluingUniverseModuleDerivedComparison.{u, v, w} R C := by
  have he := dgGluingTriangleTimeTransport_endpoint.{max (u + 1) v,
      max (u + 1) v w} 2 0
    (dgGluingExitUnitCapTriangleFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _))
    (dgGluingNativeNormalizationHomInput R C D M X Y)
    (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
  simp only [ite_true] at he
  rw [dgGluingNativeExitUnitCapTriangleFamily, he,
    dgGluingExitUnitCapTriangleFamily_zero R RM IX IY (𝟙 _)]
  rfl

lemma dgGluingNativeLeftProjectedStandardTriangle_inputs :
    dgGluingNativeLeftProjectedStandardTriangle R C D M X Y =
      (Δ[2] ◁ dgGluingNativeLeftCoefficientTriangleParameter R C D M X Y) ≫
      dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 2
        (dgGluingDGCompositionTriangleFamily R RM
          (dgGluingNativeLeftCoefficientInput R C D M X Y)
          (SSet.const (pinchedClosedVertex R RM (dgGluingAugmentation R C D M Y)))) := by
  have ht := dgGluingUliftDGCompositionTriangleFamily_input_ext.{u, max (u + 1) v,
      max (u + 1) v w} R RM
    (𝟙 _ ≫ pinchedHomChainMap ((dgFunctorCommaReplacement R RM RM (DGFunctor.id RM)).map IX IY))
    (SSet.const (pinchedClosedVertex R RM (dgGluingAugmentation R C D M Y)))
    (dgGluingNativeLeftCoefficientInput R C D M X Y)
    (SSet.const (pinchedClosedVertex R RM (dgGluingAugmentation R C D M Y)))
    (dgGluingNativeNormalizationHomInput R C D M X Y)
      (dgGluingNativeLeftCoefficientTriangleParameter R C D M X Y)
    (by simpa only [dgGluingNativeLeftCoefficientTriangleParameter,
      Category.id_comp, Category.assoc] using
      dgGluingNativeNormalizationHomInput_replacement_factor R C D M X Y)
    (by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl)
  exact ht

lemma dgGluingNativeLeftCoefficientTriangleParameter_canonical :
    ((Δ[2] ◁ dgGluingNativeLeftCoefficientTriangleParameter R C D M X Y) ≫
      dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 2
        (dgGluingDGCompositionTriangleFamily R RM
          (dgGluingNativeLeftCoefficientInput R C D M X Y)
          (SSet.const (pinchedClosedVertex R RM (dgGluingAugmentation R C D M Y))))) ≫
      dgGluingUniverseModuleDerivedComparison.{u, v, w} R C =
      (Δ[2] ◁ dgGluingNativeHomModelMap R C D M X Y) ≫
        dgGluingHomDerivedLeftCoefficientTriangle R C D M X Y := by
  simp only [dgGluingNativeLeftCoefficientTriangleParameter,
    dgGluingHomDerivedLeftCoefficientTriangle_canonical R C D M X Y,
    dgGluingUniverseModuleDerivedSimplexFamily,
    dgGluingCanonicalDerivedLeftCoefficientTriangleFamily,
    dgGluingDGCompositionTriangleFamilyPost, dgGluingUliftSimplexFamily_post,
    dgGluingUniverseModuleDerivedComparison, whiskerLeft_comp, Category.assoc]

lemma dgGluingNativeExitUnitCapTriangleFamily_zero_canonical :
    (Δ[2] ◁ (ι₀ : P ⟶ _)) ≫ dgGluingNativeExitUnitCapTriangleFamily R C D M X Y =
      (Δ[2] ◁ dgGluingNativeHomModelMap R C D M X Y) ≫
        dgGluingHomDerivedLeftCoefficientTriangle R C D M X Y := by
  rw [dgGluingNativeExitUnitCapTriangleFamily_zero_standard R C D M X Y,
    dgGluingNativeLeftProjectedStandardTriangle_inputs R C D M X Y,
    dgGluingNativeLeftCoefficientTriangleParameter_canonical R C D M X Y]

end SerrePositivity.InfinityCategories
