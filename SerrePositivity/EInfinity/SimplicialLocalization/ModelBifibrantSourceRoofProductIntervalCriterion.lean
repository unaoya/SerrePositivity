module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductFunctorCell
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductReference
public import SerrePositivity.EInfinity.FrameHom.PinchedFamilyWeakDetection

/-!
概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Opposite SSet SerrePositivity.InfinityCategories
open scoped Simplicial
open HomotopicalAlgebra SerrePositivity.Reedy
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductCommaHomMap :
  nerve (modelBifibrantSourceRoofProductComma X Y q b) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (modelBifibrantHammockVertex (modelBifibrantSourceRoofDegreeObject X Y q b))
      (modelBifibrantHammockVertex Y) :=
  (modelBifibrantSourceRoofProductCommaIso X Y q b).inv ≫
    modelBifibrantSourceRoofProductHomMap X Y q b

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductActualIntervalCell : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
    (SSet.const (X := nerve (modelBifibrantSourceRoofProductComma X Y q b))
      (modelBifibrantHammockVertex (modelBifibrantSourceRoofDegreeObject X Y q b)))
    (SSet.const (X := nerve (modelBifibrantSourceRoofProductComma X Y q b))
      (modelBifibrantHammockVertex Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (modelBifibrantSourceRoofProductCommaHomMap X Y q b ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductReferenceIntervalCell : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
    (SSet.const (X := nerve (modelBifibrantSourceRoofProductComma X Y q b))
      (modelBifibrantHammockVertex (modelBifibrantSourceRoofDegreeObject X Y q b)))
    (SSet.const (X := nerve (modelBifibrantSourceRoofProductComma X Y q b))
      (modelBifibrantHammockVertex Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (modelBifibrantSourceRoofProductCommaReferenceMap X Y q b ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)

variable [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

include r in
/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductHomMap_weak_of_intervalCell_eq
    (h : modelBifibrantSourceRoofProductActualIntervalCell X Y q b =
      modelBifibrantSourceRoofProductReferenceIntervalCell X Y q b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (modelBifibrantSourceRoofProductHomMap X Y q b) := by
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (modelBifibrantSourceRoofProductCommaIso X Y q b).symm).isWeakHomotopyEquivalence
  apply he.cancel_left
  exact FrameHom.pinchedFamily_weak_of_intervalFamilyHom_eq _ _
    (modelBifibrantSourceRoofProductCommaReferenceMap_weak X Y q b r) h

include r in
/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductHomMap_weak_of_interval_triangles
    (hA : (modelBifibrantSourceRoofProductCommaEvaluationIso X Y q b).hom ≫
      modelBifibrantSourceRoofProductActualIntervalCell X Y q b =
        modelBifibrantSourceRoofProductCommaRightCell X Y q b)
    (hR : (modelBifibrantSourceRoofProductCommaEvaluationIso X Y q b).hom ≫
      modelBifibrantSourceRoofProductReferenceIntervalCell X Y q b =
        modelBifibrantSourceRoofProductCommaRightCell X Y q b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (modelBifibrantSourceRoofProductHomMap X Y q b) := by
  apply modelBifibrantSourceRoofProductHomMap_weak_of_intervalCell_eq X Y q b r
  exact (modelBifibrantSourceRoofProductCommaComparisonCell_unique X Y q b _ hA).trans
    (modelBifibrantSourceRoofProductCommaComparisonCell_unique X Y q b _ hR).symm

include r in
/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofMap_isLeftCofinal_of_interval_triangles
    (hA : ∀ b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌,
      (modelBifibrantSourceRoofProductCommaEvaluationIso X Y q b).hom ≫
        modelBifibrantSourceRoofProductActualIntervalCell X Y q b =
          modelBifibrantSourceRoofProductCommaRightCell X Y q b)
    (hR : ∀ b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌,
      (modelBifibrantSourceRoofProductCommaEvaluationIso X Y q b).hom ≫
        modelBifibrantSourceRoofProductReferenceIntervalCell X Y q b =
          modelBifibrantSourceRoofProductCommaRightCell X Y q b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (modelBifibrantSourceFrameRoofMap X Y q) :=
  modelBifibrantSourceRoofMap_isLeftCofinal_of_productHom_weak X Y q
    (fun b => modelBifibrantSourceRoofProductHomMap_weak_of_interval_triangles X Y q b r (hA
      b) (hR b))

end SerrePositivity.EInfinity.SimplicialLocalization
