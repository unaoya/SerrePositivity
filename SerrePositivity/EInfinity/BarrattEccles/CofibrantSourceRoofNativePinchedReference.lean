module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofEvaluationImage
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofGeometricLeftCell
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.AnodyneFamilyHomotopy

/-!
# 元の指定次数 native roof の pinched 像と保存済み実基準射

概要：元の評価 roof の全族を同じ pinched Hom へ送り、保存済みの弱基準射と比較する。
方針：元の包含の全関手同型・同じ Ex∞ 単位の自然性・実 roof 比較を接続する。
規約：全パラメータ・元の選択済み逆・同じ端点を保持する。
使われ方：基準射側 hR の元の roof の合成三角形への還元。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

def cofibrantSourceRoofProductCommaNativePinchedMap :
    nerve (cofibrantSourceRoofProductComma A X Y b) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (cofibrantHammockVertex A (cofibrantSourceRoofDegreeAlgebra A X Y b))
        (cofibrantHammockVertex A Y) :=
  cofibrantSourceRoofProductCommaEvaluationRoofMap A X Y b ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (cofibrantAlgebraRelativeCategory A).weakEquivalences
      (show (cofibrantAlgebraRelativeCategory A).category from
        cofibrantSourceRoofDegreeAlgebra A X Y b)
      (show (cofibrantAlgebraRelativeCategory A).category from Y)) ≫
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap (cofibrantAlgebraRelativeCategory A)
      (show (cofibrantAlgebraRelativeCategory A).category from
        cofibrantSourceRoofDegreeAlgebra A X Y b)
      (show (cofibrantAlgebraRelativeCategory A).category from Y)

lemma cofibrantSourceRoofProductCommaNativePinchedMap_reference_Q :
    AnodyneHomotopy.anodyneQ.map (cofibrantSourceRoofProductCommaNativePinchedMap A X Y b) =
      AnodyneHomotopy.anodyneQ.map (cofibrantSourceRoofProductCommaReferenceMap A X Y b) := by
  let D := cofibrantSourceRoofDegreeAlgebra A X Y b
  let L := cofibrantAlgebraHammockColimitInclusionMap A D Y
  have hi := AnodyneHomotopy.map_homotopy_eq AnodyneHomotopy.anodyneQ
    SSet.anodyneExtensions.Q_inverts (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy
      (cofibrantHammockPinchedReferenceMap_inclusion A D Y).hom)
  have hu : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ ≫ cofibrantKanHammockInclusionMap A D Y =
      L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality L).symm
  have huQ := congrArg AnodyneHomotopy.anodyneQ.map hu
  have he := cofibrantSourceRoofProductCommaEvaluationRoofMap_image_Q A X Y b
  simp only [Functor.map_comp] at hi huQ he
  simp only [cofibrantSourceRoofProductCommaNativePinchedMap,
    cofibrantSourceRoofProductCommaReferenceMap, cofibrantSourceRoofProductPinchedReferenceMap,
    Functor.map_comp]
  rw [← hi, ← Category.assoc _ _
    (AnodyneHomotopy.anodyneQ.map (cofibrantHammockPinchedReferenceMap A D Y)), huQ]
  simp only [Category.assoc]
  rw [reassoc_of% he]
  rfl

lemma cofibrantSourceRoofProductCommaNativePinchedMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantSourceRoofProductCommaNativePinchedMap A X Y b) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence
  rw [cofibrantSourceRoofProductCommaNativePinchedMap_reference_Q]
  exact Hammock.anodyneQ_map_isIso_of_weak _
    (cofibrantSourceRoofProductCommaReferenceMap_weak A X Y b)

def cofibrantSourceRoofProductCommaNativeIntervalCell : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
    (SSet.const (X := nerve (cofibrantSourceRoofProductComma A X Y b))
      (cofibrantHammockVertex A (cofibrantSourceRoofDegreeAlgebra A X Y b)))
    (SSet.const (X := nerve (cofibrantSourceRoofProductComma A X Y b))
      (cofibrantHammockVertex A Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (cofibrantSourceRoofProductCommaNativePinchedMap A X Y b ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)

lemma cofibrantSourceRoofProductCommaNativeIntervalCell_eq_reference :
    cofibrantSourceRoofProductCommaNativeIntervalCell A X Y b =
      cofibrantSourceRoofProductReferenceIntervalCell A X Y b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedFamily_intervalHom_eq_of_anodyneQ_eq _ _
    (cofibrantSourceRoofProductCommaNativePinchedMap_reference_Q A X Y b)

lemma cofibrantSourceRoofProductReference_triangle_of_native_triangle
    (hN : (cofibrantSourceRoofProductCommaEvaluationIso A X Y b).hom ≫
      cofibrantSourceRoofProductCommaNativeIntervalCell A X Y b =
        cofibrantSourceRoofProductCommaRightCell A X Y b) :
    (cofibrantSourceRoofProductCommaEvaluationIso A X Y b).hom ≫
      cofibrantSourceRoofProductReferenceIntervalCell A X Y b =
        cofibrantSourceRoofProductCommaRightCell A X Y b := by
  rw [← cofibrantSourceRoofProductCommaNativeIntervalCell_eq_reference]
  exact hN

lemma cofibrantSourceRoofMap_isLeftCofinal_of_native_triangles
    (hN : ∀ b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌,
      (cofibrantSourceRoofProductCommaEvaluationIso A X Y b).hom ≫
        cofibrantSourceRoofProductCommaNativeIntervalCell A X Y b =
          cofibrantSourceRoofProductCommaRightCell A X Y b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (cofibrantSourceFrameRoofMap A X Y) :=
  cofibrantSourceRoofMap_isLeftCofinal_of_reference_triangle A X Y
    (fun b => cofibrantSourceRoofProductReference_triangle_of_native_triangle A X Y b (hN b))

end SerrePositivity.EInfinity.BarrattEccles
