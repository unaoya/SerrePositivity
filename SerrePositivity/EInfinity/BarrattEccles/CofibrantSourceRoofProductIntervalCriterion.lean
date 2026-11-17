module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofProductFunctorCell
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofPinchedReference
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.PinchedFamilyWeakDetection

/-!
# 同じ逆左脚と右脚を表す全区間族による実屋根 cofinality の還元

概要：実射と弱な基準射を、元の comma 圏上の二つの区間族の射として扱う。
方針：同じ左脚との合成が元の右脚に一致すれば、全族の一致から元の実射を反転する。
規約：二つの全三角形の証明は別工程。個々の頂点の π₀ の一致を入力とはしない。
使われ方：実屋根の全 slice の弱可縮性と局所化普遍性への比較の出口。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SSet SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

def cofibrantSourceRoofProductCommaHomMap : nerve (cofibrantSourceRoofProductComma A X Y b) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (cofibrantHammockVertex A (cofibrantSourceRoofDegreeAlgebra A X Y b))
      (cofibrantHammockVertex A Y) :=
  (cofibrantSourceRoofProductCommaIso A X Y b).inv ≫ cofibrantSourceRoofProductHomMap A X Y b

def cofibrantSourceRoofProductCommaReferenceMap :
    nerve (cofibrantSourceRoofProductComma A X Y b) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (cofibrantHammockVertex A (cofibrantSourceRoofDegreeAlgebra A X Y b))
        (cofibrantHammockVertex A Y) :=
  (cofibrantSourceRoofProductCommaIso A X Y b).inv ≫
    cofibrantSourceRoofProductPinchedReferenceMap A X Y b

lemma cofibrantSourceRoofProductCommaReferenceMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantSourceRoofProductCommaReferenceMap A X Y b) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (cofibrantSourceRoofProductCommaIso A X Y b).symm).isWeakHomotopyEquivalence.comp
      (cofibrantSourceRoofProductPinchedReferenceMap_weak A X Y b)

def cofibrantSourceRoofProductActualIntervalCell : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
    (SSet.const (X := nerve (cofibrantSourceRoofProductComma A X Y b))
      (cofibrantHammockVertex A (cofibrantSourceRoofDegreeAlgebra A X Y b)))
    (SSet.const (X := nerve (cofibrantSourceRoofProductComma A X Y b))
      (cofibrantHammockVertex A Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (cofibrantSourceRoofProductCommaHomMap A X Y b ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)

def cofibrantSourceRoofProductReferenceIntervalCell : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
    (SSet.const (X := nerve (cofibrantSourceRoofProductComma A X Y b))
      (cofibrantHammockVertex A (cofibrantSourceRoofDegreeAlgebra A X Y b)))
    (SSet.const (X := nerve (cofibrantSourceRoofProductComma A X Y b))
      (cofibrantHammockVertex A Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (cofibrantSourceRoofProductCommaReferenceMap A X Y b ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)

lemma cofibrantSourceRoofProductHomMap_weak_of_intervalCell_eq
    (h : cofibrantSourceRoofProductActualIntervalCell A X Y b =
      cofibrantSourceRoofProductReferenceIntervalCell A X Y b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantSourceRoofProductHomMap A X Y b) := by
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (cofibrantSourceRoofProductCommaIso A X Y b).symm).isWeakHomotopyEquivalence
  apply he.cancel_left
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.pinchedFamily_weak_of_intervalFamilyHom_eq _ _
    (cofibrantSourceRoofProductCommaReferenceMap_weak A X Y b) h

lemma cofibrantSourceRoofProductHomMap_weak_of_interval_triangles
    (hA : (cofibrantSourceRoofProductCommaEvaluationIso A X Y b).hom ≫
      cofibrantSourceRoofProductActualIntervalCell A X Y b =
        cofibrantSourceRoofProductCommaRightCell A X Y b)
    (hR : (cofibrantSourceRoofProductCommaEvaluationIso A X Y b).hom ≫
      cofibrantSourceRoofProductReferenceIntervalCell A X Y b =
        cofibrantSourceRoofProductCommaRightCell A X Y b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantSourceRoofProductHomMap A X Y b) := by
  apply cofibrantSourceRoofProductHomMap_weak_of_intervalCell_eq A X Y b
  exact (cofibrantSourceRoofProductCommaComparisonCell_unique A X Y b _ hA).trans
    (cofibrantSourceRoofProductCommaComparisonCell_unique A X Y b _ hR).symm

lemma cofibrantSourceRoofMap_isLeftCofinal_of_interval_triangles
    (hA : ∀ b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌,
      (cofibrantSourceRoofProductCommaEvaluationIso A X Y b).hom ≫
        cofibrantSourceRoofProductActualIntervalCell A X Y b =
          cofibrantSourceRoofProductCommaRightCell A X Y b)
    (hR : ∀ b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌,
      (cofibrantSourceRoofProductCommaEvaluationIso A X Y b).hom ≫
        cofibrantSourceRoofProductReferenceIntervalCell A X Y b =
          cofibrantSourceRoofProductCommaRightCell A X Y b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (cofibrantSourceFrameRoofMap A X Y) :=
  cofibrantSourceRoofMap_isLeftCofinal_of_productHom_weak A X Y
    (fun b => cofibrantSourceRoofProductHomMap_weak_of_interval_triangles A X Y b (hA b) (hR b))

end SerrePositivity.EInfinity.BarrattEccles
