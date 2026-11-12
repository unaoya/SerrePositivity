module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofSliceCriterion
public import SerrePositivity.EInfinity.FrameHom.FrameRoofCornerEvaluation

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
open CategoryTheory Limits Opposite SSet
open SerrePositivity.EInfinity.FrameHom.FrameArrows SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
abbrev modelBifibrantSourceRoofDegreeObject : HomotopicalAlgebra.BifibrantObject C :=
  (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantFrame X q).obj (ULift.down (modelBifibrantSourceRoofDegree X Y q b))

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofCornerEvaluation :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCorner (SSet.yonedaEquiv.symm b) (modelBifibrantSourceRoofProjection X Y q) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (modelBifibrantHammockVertex (modelBifibrantSourceRoofDegreeObject X Y q b))
        (modelBifibrantHammockVertex Y) := by
  have := modelBifibrantSourceRoofProjection_leftFibration X Y q
  exact roofCornerEvaluation (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
    (SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) b

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofCornerEvaluation_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (modelBifibrantSourceRoofCornerEvaluation X Y q b) := by
  have := modelBifibrantSourceRoofProjection_leftFibration X Y q
  exact roofCornerEvaluation_weak (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
    (SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) b

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductHomMap :
  nerve (modelBifibrantSourceRoofProductElements X Y q b) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (modelBifibrantHammockVertex (modelBifibrantSourceRoofDegreeObject X Y q b))
      (modelBifibrantHammockVertex Y) :=
  modelBifibrantSourceRoofProductCornerMap X Y q b ≫
    modelBifibrantSourceRoofCornerEvaluation X Y q b

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCorner_weak_iff_hom :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (modelBifibrantSourceRoofProductCornerMap X Y q b) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (modelBifibrantSourceRoofProductHomMap X Y q b) :=
  ⟨fun h => h.comp (modelBifibrantSourceRoofCornerEvaluation_weak X Y q b),
    fun h => (modelBifibrantSourceRoofCornerEvaluation_weak X Y q b).cancel_right h⟩

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofSlice_weaklyContractible_of_productHom_weak
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (modelBifibrantSourceRoofProductHomMap X Y q b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (modelBifibrantSourceRoofSlice X Y q b) :=
  modelBifibrantSourceRoofSlice_weaklyContractible_of_productCorner_weak X Y q b
    ((modelBifibrantSourceRoofProductCorner_weak_iff_hom X Y q b).2 h)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofMap_isLeftCofinal_of_productHom_weak
    (h : ∀ b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (modelBifibrantSourceRoofProductHomMap X Y q b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (modelBifibrantSourceFrameRoofMap X Y q) :=
  modelBifibrantSourceRoofMap_isLeftCofinal_of_productCorner_weak X Y q
    (fun b => (modelBifibrantSourceRoofProductCorner_weak_iff_hom X Y q b).2 (h b))

end SerrePositivity.EInfinity.SimplicialLocalization
