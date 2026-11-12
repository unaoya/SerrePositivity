module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SliceEndpointConeComparison

/-!
概要：同じ錐の slice の点と標準の切断の点は、両端固定の共通模型で厳密に一致する。
方針：零単体を Yoneda 表示し、二つの普遍族を uncurry して点の直積成分を射影する。
規約：同値の逆や比較 span の切断の選択は使わない。quasicategory 性も不要。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS）、native な制限の fiber の固定点の照合。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
noncomputable section

/-- 概要：錐の標準の切断の点を展開すると、点の直積成分を射影した元の錐となる。
方針：相対 curry の逆関係と coslice の uncurry の前合成則を使う。
規約：元の錐は厳密な射 d.val として回収する。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、標準の切断の点の共通模型での値。 -/
lemma sectionConeUncurry_sectionPoint {K X : SSet.{u}} {p : K ⟶ X} (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionConeUncurry (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionPoint d)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (fst K (Δ[0] : SSet.{u})) ≫ d.val := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionConeUncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry (fst K (Δ[0] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection d)
      (by rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection_projection])))) = _
  rw [Equiv.symm_apply_apply]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionConeUncurry
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry]

/-- 概要：slice の錐の点を共通模型で評価すると点の直積成分を射影した元の錐となる。
方針：普遍族の式と点の join・直積の比較の単位則を使う。
規約：固定点は coneVertexFiberPoint d そのもの。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、slice と切断で同じ元の錐を固定することの検証。 -/
lemma sliceEndpointConeComparison_point_uncurry {K X : SSet.{u}} {p : K ⟶ X}
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    uncurry (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneVertexFiberPoint d) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sliceEndpointConeComparison p d.vertex ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.endpointConeEvaluation p d.vertex) =
      fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K) (Δ[0] : SSet.{u}) ≫ d.val := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sliceEndpointConeComparison_uncurry, SSet.yonedaEquiv_symm_comp]
  change _ ≫ _ ≫ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (SSet.yonedaEquiv.symm d) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverUncurry_yoneda]
  have h : fst (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u}) =
      snd (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u}) := stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft _ _ _), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft_unit, ← Category.assoc]
  rfl

/-- 概要：標準の切断の錐の点を共通模型で評価すると元の錐を回収する。
方針：切断の点の展開と右側の join・直積の比較の単位則を使う。
規約：選んだ頂点 fiber・切断同値の像ではなく標準の切断の点を使う。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、標準の切断制限の fiber の固定点の保持。 -/
lemma sectionEndpointConeComparison_point_uncurry {K X : SSet.{u}} {p : K ⟶ X}
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    uncurry (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionPoint d) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionEndpointConeComparison p d.vertex ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.endpointConeEvaluation p d.vertex) =
      fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K) (Δ[0] : SSet.{u}) ≫ d.val := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionEndpointConeComparison_uncurry, sectionConeUncurry_sectionPoint,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinTensorRight_unit]

/-- 概要：同じ錐の slice の点と標準の切断の点は両端固定の共通模型で厳密に一致する。
方針：二つの fiber の包含と uncurry の単射性で、展開した元の錐の一致へ帰着する。
規約：充填性も同値の選択も不要。零単体の等式として述べる。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS）、slice・切断の導来 fiber の固定点の同定。 -/
lemma coneEndpointComparison_point_eq {K X : SSet.{u}} {p : K ⟶ X} (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sliceEndpointConeComparison p d.vertex).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneVertexFiberPoint d) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionEndpointConeComparison p d.vertex).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionPoint d) := by
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.yonedaEquiv_symm_comp, ← SSet.yonedaEquiv_symm_comp]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
    ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm d.vertex) p))
  change (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneVertexFiberPoint d) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sliceEndpointConeComparison p d.vertex) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.endpointConeEvaluation p d.vertex =
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionPoint d) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionEndpointConeComparison p d.vertex) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.endpointConeEvaluation p d.vertex
  apply uncurry_injective
  simp only [Category.assoc]
  exact (sliceEndpointConeComparison_point_uncurry d).trans
    (sectionEndpointConeComparison_point_uncurry d).symm

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
