module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardWeightTotalNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.BarWeightEndComparison

/-!
概要：元の積 Tot から bar 重みの線形 end への指定比較を全図式上の自然変換にする。
方針：標準重みの自然同型の逆射に、固定された bar 重みの比較射の評価自然変換を合成する。
規約：各対象での前向き射は既存の鎖ホモトピー同値の前向き射そのもの。
使われ方：HA 1.2.4、G10 の図式の全射と指定計算比較の両立。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 係数の全余単体図式から、固定された bar 鎖重みの線形 end の積全複体を取る関手。 -/
def barWeightEndTotalFunctor : CosimplicialObject (Complex A) ⥤ Complex A :=
  (Functor.whiskeringLeft SimplexCategoryᵒᵖᵒᵖ SimplexCategory (Complex A)).obj
      (opOpEquivalence SimplexCategory).functor ⋙
    linearWeightEndTotalFamily A ⋙
    (evaluation (ChainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℕ)ᵒᵖ (Complex A)).obj
      (op (coefficientBarWeightResolution SimplexCategoryᵒᵖ (ModuleCat.of A A)).complex)

/-- 元の積 Tot から、同じ指定 bar 比較の前合成で得る全関手上の自然変換。 -/
def barWeightEndTotalComparison : productTotalFunctor A ⟶ barWeightEndTotalFunctor (A := A) :=
  standardWeightEndTotalNatIso.inv ≫
    Functor.whiskerLeft
      ((Functor.whiskeringLeft SimplexCategoryᵒᵖᵒᵖ SimplexCategory (Complex A)).obj
        (opOpEquivalence SimplexCategory).functor ⋙ linearWeightEndTotalFamily A)
      ((evaluation (ChainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℕ)ᵒᵖ (Complex A)).map
        ((alternatingFaceMapComplex _).map
          (SimplicialRealization.barStandardWeightComparison (ModuleCat.of A A))).op)

/-- 自然変換の各対象での射は、指定された鎖ホモトピー同値の前向き射そのもの。 -/
theorem barWeightEndTotalComparison_app (X : CosimplicialObject (Complex A)) :
    barWeightEndTotalComparison.app X = (barWeightEndTotalHomotopyEquiv X).hom := rfl

/-- 同じ全関手上の比較は各図式で擬同型。 -/
instance barWeightEndTotalComparison_quasiIso (X : CosimplicialObject (Complex A)) :
    QuasiIso (barWeightEndTotalComparison.app X) :=
  inferInstanceAs (QuasiIso (barWeightEndTotalHomotopyEquiv X).hom)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
