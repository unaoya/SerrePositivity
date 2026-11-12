module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.BarWeightEndNaturality
public import SerrePositivity.HomologicalAlgebra.DoubleOppositeOverWeight

/-!
概要：元の積 Tot を BK の over 重みの線形 end の積全複体へ、全図式に自然に比較する。
方針：指定 bar 比較の後に、under/over の反転符号付き鎖同型の前合成を使う。
規約：各対象で同じ射を持つ鎖ホモトピー同値。native 錐の極限性はまだ含まない。
使われ方：HA 1.2.4、G10 の元の指定積 Tot と BK の重み付き計算との接続。
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

/-- 元の全余単体図式を、同じ BK over 鎖重みの線形 end へ送る関手。 -/
def bousfieldKanWeightEndTotalFunctor : CosimplicialObject (Complex A) ⥤ Complex A :=
  (Functor.whiskeringLeft SimplexCategoryᵒᵖᵒᵖ SimplexCategory (Complex A)).obj
      (opOpEquivalence SimplexCategory).functor ⋙
    linearWeightEndTotalFamily A ⋙
    (evaluation (ChainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℕ)ᵒᵖ (Complex A)).obj
      (op ((alternatingFaceMapComplex _).obj
        (doubleOppositeOverWeight SimplexCategory (ModuleCat.of A A))))

/-- bar から BK over への同じ重み比較を、全係数図式に自然な射へ移す。 -/
def barToBousfieldKanWeightEndComparison :
    barWeightEndTotalFunctor (A := A) ⟶ bousfieldKanWeightEndTotalFunctor :=
  Functor.whiskerLeft
    ((Functor.whiskeringLeft SimplexCategoryᵒᵖᵒᵖ SimplexCategory (Complex A)).obj
      (opOpEquivalence SimplexCategory).functor ⋙ linearWeightEndTotalFamily A)
    ((evaluation (ChainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℕ)ᵒᵖ (Complex A)).map
      (barDoubleOppositeOverChainIso SimplexCategory (ModuleCat.of A A)).inv.op)

/-- 元の積 Tot から BK over 重みの end への指定された自然変換。 -/
def bousfieldKanWeightEndTotalComparison :
    productTotalFunctor A ⟶ bousfieldKanWeightEndTotalFunctor :=
  barWeightEndTotalComparison ≫ barToBousfieldKanWeightEndComparison

/-- 同じ比較の各対象での鎖ホモトピー同値。 -/
def bousfieldKanWeightEndTotalHomotopyEquiv (X : CosimplicialObject (Complex A)) :
    HomotopyEquiv ((productTotalFunctor A).obj X) (bousfieldKanWeightEndTotalFunctor.obj X) :=
  (barWeightEndTotalHomotopyEquiv X).trans
    (HomotopyEquiv.ofIso
      ((linearWeightEndTotalFunctor A (doubleOppositeDiagram X)).mapIso
        (barDoubleOppositeOverChainIso SimplexCategory (ModuleCat.of A A)).op).symm)

/-- 自然変換の各成分は、同じ鎖ホモトピー同値の前向き射そのもの。 -/
theorem bousfieldKanWeightEndTotalComparison_app (X : CosimplicialObject (Complex A)) :
    bousfieldKanWeightEndTotalComparison.app X =
      (bousfieldKanWeightEndTotalHomotopyEquiv X).hom := rfl

/-- 同じ全図式上の指定比較は各対象で擬同型。 -/
instance bousfieldKanWeightEndTotalComparison_quasiIso (X : CosimplicialObject (Complex A)) :
    QuasiIso (bousfieldKanWeightEndTotalComparison.app X) :=
  inferInstanceAs (QuasiIso (bousfieldKanWeightEndTotalHomotopyEquiv X).hom)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
