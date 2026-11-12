module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NegativeEZCoefficient
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.IntegerCoefficientFree

/-!
概要：一般係数の自由線形化した積と正規化テンソルを、指定 EZ 写像で結ぶ。
方針：整数の積自由化同型と係数自由化の自然同型で負次数 EZ 写像を移す。
規約：標的と始域は元の ModuleCat.free の Moore 正規化。平坦性を追加しない。
使われ方：HA 1.2.4、G10 の積重みと全単体 Hom パラメータの接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory HomologicalComplex AlgebraicTopology
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type u} [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A)

/-- 元の A 自由化を Moore 正規化して負次数へ延長した複体。 -/
abbrev freeNegativeChains (X : SSet.{u}) :=
  ((normalizedMooreComplex (ModuleCat A)).obj (X ⋙ ModuleCat.free A)).extend
    ComplexShape.embeddingDownNat

/-- 単体的自由化の同じ係数比較。 -/
def integerCoefficientSimplicialFreeIso (X : SSet.{u}) :
    linearizedSpace X ⋙ integerCoefficientExtension φ ≅ X ⋙ ModuleCat.free A :=
  Functor.isoWhiskerLeft X (integerCoefficientFreeIso φ)

/-- 因子の自由化比較を元の Moore 正規化へ送る。 -/
def integerCoefficientFreeChainsIso (X : SSet.{u}) :
    (((normalizedMooreComplex (ModuleCat A)).obj
      (linearizedSpace X ⋙ integerCoefficientExtension φ)).extend
      ComplexShape.embeddingDownNat) ≅ freeNegativeChains (A := A) X :=
  (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).mapIso
    ((normalizedMooreComplex (ModuleCat A)).mapIso (integerCoefficientSimplicialFreeIso φ X))

/-- 整数テンソルの自由化を元の積の A 正規化鎖へ結ぶ指定同型。 -/
def integerCoefficientProductChainsIso (X Y : SSet.{u}) :
    (((normalizedMooreComplex (ModuleCat A)).obj
      (simplicialIntegerTensor (linearizedSpace X) (linearizedSpace Y) ⋙
        integerCoefficientExtension φ)).extend ComplexShape.embeddingDownNat) ≅
      freeNegativeChains (A := A) (X ⊗ Y) :=
  (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).mapIso
    ((normalizedMooreComplex (ModuleCat A)).mapIso
      (Functor.isoWhiskerRight (linearizedTensorIso X Y) (integerCoefficientExtension φ) ≪≫
        integerCoefficientSimplicialFreeIso φ (X ⊗ Y)))

/-- 元の積の自由正規化鎖から二因子のテンソルへの指定 AW 射。 -/
def freeProductAlexanderWhitney (X Y : SSet.{u}) :
    freeNegativeChains (A := A) (X ⊗ Y) ⟶
      freeNegativeChains (A := A) X ⊗ freeNegativeChains (A := A) Y :=
  (integerCoefficientProductChainsIso φ X Y).inv ≫
    negativeCoefficientAlexanderWhitney φ (linearizedSpace X) (linearizedSpace Y) ≫
    (tensorIso (integerCoefficientFreeChainsIso φ X)
      (integerCoefficientFreeChainsIso φ Y)).hom

/-- 二因子のテンソルから元の積の自由正規化鎖への指定 shuffle 射。 -/
def freeProductShuffle (X Y : SSet.{u}) :
    freeNegativeChains (A := A) X ⊗ freeNegativeChains (A := A) Y ⟶
      freeNegativeChains (A := A) (X ⊗ Y) :=
  (tensorIso (integerCoefficientFreeChainsIso φ X)
      (integerCoefficientFreeChainsIso φ Y)).inv ≫
    negativeCoefficientShuffle φ (linearizedSpace X) (linearizedSpace Y) ≫
    (integerCoefficientProductChainsIso φ X Y).hom

/-- 元の積の A 自由正規化鎖上で、指定 AW→shuffle を恒等へ結ぶホモトピー。 -/
def freeProductEZHomotopy (X Y : SSet.{u}) :
    Homotopy (𝟙 _) (freeProductAlexanderWhitney φ X Y ≫ freeProductShuffle φ X Y) := by
  let e := integerCoefficientProductChainsIso φ X Y
  let h := ((negativeCoefficientEZHomotopy φ (linearizedSpace X) (linearizedSpace Y)).compLeft
    e.inv).compRight e.hom
  refine (Homotopy.ofEq ?_).trans (h.trans (Homotopy.ofEq ?_))
  · change 𝟙 _ = (e.inv ≫ 𝟙 _) ≫ e.hom
    rw [Category.comp_id, Iso.inv_hom_id]
  · dsimp only [freeProductAlexanderWhitney, freeProductShuffle, e]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
