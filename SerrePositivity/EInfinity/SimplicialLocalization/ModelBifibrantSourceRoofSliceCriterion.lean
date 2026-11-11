module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofSliceFibration
public import SerrePositivity.EInfinity.FrameHom.FrameRoofSliceWeakContractibility

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
def modelBifibrantSourceRoofProductCornerMap :
  nerve (modelBifibrantSourceRoofProductElements X Y q b) ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCorner (SSet.yonedaEquiv.symm b) (modelBifibrantSourceRoofProjection X Y q) :=
  (modelBifibrantSourceRoofProductIso X Y q b).hom ≫
    (modelBifibrantSourceRoofDegreeTransportIso X Y q b).inv ≫
      roofQuillenDegreeCornerMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
        (SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
        b (modelBifibrantSourceFrameRoofMap X Y q)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofSlice_weaklyContractible_of_productCorner_weak
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (modelBifibrantSourceRoofProductCornerMap X Y q b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (modelBifibrantSourceRoofSlice X Y q b) := by
  have := modelBifibrantSourceRoofProjection_leftFibration X Y q
  let e := modelBifibrantSourceRoofProductIso X Y q b ≪≫
    (modelBifibrantSourceRoofDegreeTransportIso X Y q b).symm
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e).isWeakHomotopyEquivalence
  apply roofQuillenSlice_weaklyContractible_of_corner_weak (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
    (SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
    b (modelBifibrantSourceFrameRoofMap X Y q)
  exact he.cancel_left h

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofMap_isLeftCofinal_of_productCorner_weak
    (h : ∀ b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (modelBifibrantSourceRoofProductCornerMap X Y q b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (modelBifibrantSourceFrameRoofMap X Y q) :=
  (modelBifibrantSourceRoofMap_isLeftCofinal_iff_slices X Y q).2
    (fun b => modelBifibrantSourceRoofSlice_weaklyContractible_of_productCorner_weak X Y q b (h b))

end SerrePositivity.EInfinity.SimplicialLocalization
