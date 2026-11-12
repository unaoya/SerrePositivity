module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ContinuousLeftFibrationHomIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinityEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace

/-!
概要：元の left fibration から連続置換への単位は、同じ底上の ∞ 圏で可逆である。
方針：左アノダインな単位上の恒等射を延長し、可縮な相対延長空間で逆条件を比較する。
規約：元の単位と底への射を保持し、全空間の圏同値性を仮定しない。
使われ方：有限底上模型の全表示を、元の指定 left fibration 自身へ戻す。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の連続置換の単位は、left fibrations の coherent nerve の可逆辺である。
方針：相対延長で底上の逆射を作り、同じ単位を固定する延長空間で他方の逆条件を得る。
規約：元の対象 X と元の単位を用いる。
使われ方：全表示の頂点を置換前の X へ厳密に戻す比較。 -/
lemma continuousLeftFibrationUnit_isInvertible {B : SSet.{u}} (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (show X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousReplacementLeftFibrationObject X.val from
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousLeftFibrationReplacementUnit B).app X.val)) := by
  let R := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousReplacementLeftFibrationObject X.val
  let f : X ⟶ R := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousLeftFibrationReplacementUnit B).app X.val
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions f.left :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousLeftFibrationReplacementUnit_leftAnodyne X.val
  obtain ⟨r, hr, hfr⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.exists_relativeFunctorExtension_of_leftAnodyne
    X.val.hom R.val.hom f.left hf (𝟙 X.val.left) (by
      rw [Category.id_comp, f.w])
  let g : R ⟶ X := Over.homMk r hr
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveEdge_isInvertible_of_enrichedInverse f g
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationHom_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationHom_vertex]
    apply eqToIso
    apply congrArg HomotopyCategory.mk
    apply Subtype.ext
    exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex hfr
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationHom_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationHom_vertex]
    have hrf : (r ≫ f.left) ≫ R.val.hom = R.val.hom := by
      rw [Category.assoc, f.w, hr]
    have hi : f.left ≫ (r ≫ f.left) = f.left := by
      rw [← Category.assoc, hfr, Category.id_comp]
    let x := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv R.val.hom R.val.hom f.left f.left
      (by rfl) ⟨r ≫ f.left, hrf, hi⟩
    let y := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv R.val.hom R.val.hom f.left f.left
      (by rfl) ⟨𝟙 R.val.left, Category.id_comp _, Category.comp_id _⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan R.val.hom R.val.hom f.left hf
        f.left (by rfl)).vertexIso x y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι R.val.hom R.val.hom f.left f.left (by rfl))

/-- 概要：元の指定 left fibration と連続置換の頂点を同じ ∞ 圏内で比較する。
方針：元の単位の可逆な辺をホモトピー圏の同型にする。
規約：底の quasicategory 性は不要。
使われ方：元の対象を厳密な頂点に持つ有限模型の filtered 全表示。 -/
def continuousLeftFibrationUnitVertexIso {B : SSet.{u}} (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousReplacementLeftFibrationObject X.val)) := by
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (show X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousReplacementLeftFibrationObject X.val from
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousLeftFibrationReplacementUnit B).app X.val)).toTruncated) :=
    continuousLeftFibrationUnit_isInvertible X
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
    (show X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousReplacementLeftFibrationObject X.val from
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousLeftFibrationReplacementUnit B).app X.val)).toTruncated)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
