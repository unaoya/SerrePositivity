module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.BousfieldKanWeightEndComparison
public import SerrePositivity.HomologicalAlgebra.LinearWeightEndNormalization
public import SerrePositivity.HomologicalAlgebra.WeightEndHomIso

/-!
概要：元の非有界積 Tot と、実 Moore 正規化した BK over 重みからの Hom 複体を比較する。
方針：指定 over 比較、Moore 包含の前合成、符号付き end–Hom 同型を順に合成する。
規約：前向き射を固定した鎖ホモトピー同値。native な錐の極限性は別に示す。
使われ方：HA 1.2.4、G10 の Dold–Kan Hom 空間への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite AlgebraicTopology CochainComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- BK over の同じ係数重みを、図式圏で実 Moore 正規化した鎖複体。 -/
def normalizedBousfieldKanWeight : ChainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℕ :=
  (normalizedMooreComplex _).obj (doubleOppositeOverWeight SimplexCategory (ModuleCat.of A A))

/-- 実正規化 BK 重みから係数図式への、非有界線形 Hom 複体。 -/
def normalizedBousfieldKanHom (X : CosimplicialObject (Complex A)) : Complex A :=
  linearHomComplex A (normalizedBousfieldKanWeight.extend ComplexShape.embeddingDownNat)
    ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat.{u} A) (.up ℤ)).obj
      (doubleOppositeDiagram X))

/-- 元の Tot と実正規化 BK Hom を同じ指定射で結ぶ鎖ホモトピー同値。 -/
def normalizedBousfieldKanHomHomotopyEquiv (X : CosimplicialObject (Complex A)) :
    HomotopyEquiv ((productTotalFunctor A).obj X) (normalizedBousfieldKanHom X) :=
  (bousfieldKanWeightEndTotalHomotopyEquiv X).trans
    ((linearWeightEndNormalizationHomotopyEquiv A (doubleOppositeDiagram X)
      (doubleOppositeOverWeight SimplexCategory (ModuleCat.of A A))).trans
      (HomotopyEquiv.ofIso (weightEndHomIso A normalizedBousfieldKanWeight
        (doubleOppositeDiagram X))))

/-- 前向き射は、指定 over 比較と正規化包含と符号付き同型の合成。 -/
def normalizedBousfieldKanHomComparison (X : CosimplicialObject (Complex A)) :
    (productTotalFunctor A).obj X ⟶ normalizedBousfieldKanHom X :=
  bousfieldKanWeightEndTotalComparison.app X ≫
    linearWeightEndNormalizationMap A (doubleOppositeDiagram X)
      (doubleOppositeOverWeight SimplexCategory (ModuleCat.of A A)) ≫
    (weightEndHomIso A normalizedBousfieldKanWeight (doubleOppositeDiagram X)).hom

/-- 比較の前向き射を保つ等式。 -/
theorem normalizedBousfieldKanHomHomotopyEquiv_hom (X : CosimplicialObject (Complex A)) :
    (normalizedBousfieldKanHomHomotopyEquiv X).hom = normalizedBousfieldKanHomComparison X := rfl

/-- 同じ指定比較は擬同型。 -/
instance normalizedBousfieldKanHomComparison_quasiIso (X : CosimplicialObject (Complex A)) :
    QuasiIso (normalizedBousfieldKanHomComparison X) :=
  inferInstanceAs (QuasiIso (normalizedBousfieldKanHomHomotopyEquiv X).hom)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
