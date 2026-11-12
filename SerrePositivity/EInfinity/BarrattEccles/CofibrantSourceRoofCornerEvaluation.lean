module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofSliceCriterion
public import SerrePositivity.EInfinity.FrameHom.FrameRoofCornerEvaluation

/-!
# 元の cofibrant 屋根 corner の同じ Kan Hom への全体評価

概要：元の全 corner と積単体比較を、同じ次数の元の代数からの pinched Hom へ送る。
方針：既存の屋根射影の左ファイブレーション性を実全体評価へ代入する。
規約：任意可換環・元の qD_n・qY・元の積単体を保持する。
使われ方：保存済みの Kan Hom 高次比較との全単体の照合と cofinal 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite SSet
open SerrePositivity.EInfinity.FrameHom.FrameArrows SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

abbrev cofibrantSourceRoofDegreeAlgebra : CofibrantAlgebra A :=
  (cofibrantSourceFrame A X).obj (ULift.down (cofibrantSourceRoofDegree A X Y b))

def cofibrantSourceRoofCornerEvaluation :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCorner (SSet.yonedaEquiv.symm b) (cofibrantSourceRoofProjection A X Y) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (cofibrantHammockVertex A (cofibrantSourceRoofDegreeAlgebra A X Y b))
        (cofibrantHammockVertex A Y) := by
  have := cofibrantSourceRoofProjection_leftFibration A X Y
  exact roofCornerEvaluation (cofibrantDKSourceFrame A X)
    (show (cofibrantAlgebraRelativeCategory A).category from Y)
    (SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) b

lemma cofibrantSourceRoofCornerEvaluation_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantSourceRoofCornerEvaluation A X Y b) := by
  have := cofibrantSourceRoofProjection_leftFibration A X Y
  exact roofCornerEvaluation_weak (cofibrantDKSourceFrame A X)
    (show (cofibrantAlgebraRelativeCategory A).category from Y)
    (SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) b

def cofibrantSourceRoofProductHomMap : nerve (cofibrantSourceRoofProductElements A X Y b) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (cofibrantHammockVertex A (cofibrantSourceRoofDegreeAlgebra A X Y b))
      (cofibrantHammockVertex A Y) :=
  cofibrantSourceRoofProductCornerMap A X Y b ≫ cofibrantSourceRoofCornerEvaluation A X Y b

lemma cofibrantSourceRoofProductCorner_weak_iff_hom :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantSourceRoofProductCornerMap A X Y b) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantSourceRoofProductHomMap A X Y b) :=
  ⟨fun h => h.comp (cofibrantSourceRoofCornerEvaluation_weak A X Y b),
    fun h => (cofibrantSourceRoofCornerEvaluation_weak A X Y b).cancel_right h⟩

lemma cofibrantSourceRoofSlice_weaklyContractible_of_productHom_weak
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantSourceRoofProductHomMap A X Y b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (cofibrantSourceRoofSlice A X Y b) :=
  cofibrantSourceRoofSlice_weaklyContractible_of_productCorner_weak A X Y b
    ((cofibrantSourceRoofProductCorner_weak_iff_hom A X Y b).2 h)

lemma cofibrantSourceRoofMap_isLeftCofinal_of_productHom_weak
    (h : ∀ b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantSourceRoofProductHomMap A X Y b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (cofibrantSourceFrameRoofMap A X Y) :=
  cofibrantSourceRoofMap_isLeftCofinal_of_productCorner_weak A X Y
    (fun b => (cofibrantSourceRoofProductCorner_weak_iff_hom A X Y b).2 (h b))

end SerrePositivity.EInfinity.BarrattEccles
