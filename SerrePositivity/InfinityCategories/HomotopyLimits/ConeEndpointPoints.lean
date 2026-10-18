module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SliceEndpointConeComparison

/-!
概要：同じ錐の slice の点と標準の切断の点は、両端固定の共通模型で厳密に一致する。
方針：零単体を Yoneda 表示し、二つの普遍族を uncurry して点の直積成分を射影する。
規約：同値の逆や比較 span の切断の選択は使わない。quasicategory 性も不要。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6、native な制限の fiber の固定点の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：錐の標準の切断の点を展開すると、点の直積成分を射影した元の錐となる。
方針：相対 curry の逆関係と coslice の uncurry の前合成則を使う。
規約：元の錐は厳密な射 d.val として回収する。
使われ方：Kerodon 7.4.1.6、標準の切断の点の共通模型での値。 -/
lemma sectionConeUncurry_sectionPoint {K X : SSet.{u}} {p : K ⟶ X} (d : JoinCone p) :
    sectionConeUncurry (SSet.yonedaEquiv.symm (coherentConeSectionPoint d)) =
      joinMap (𝟙 (Δ[0] : SSet.{u})) (fst K (Δ[0] : SSet.{u})) ≫ d.val := by
  change sectionConeUncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv
    (relativeFunctorCurry (fst K (Δ[0] : SSet.{u}) ≫ coherentConeCosliceSection d)
      (by rw [Category.assoc, coherentConeCosliceSection_projection])))) = _
  rw [Equiv.symm_apply_apply]
  unfold sectionConeUncurry
  rw [relativeFunctorUncurry_curry, sliceUnderUncurry_precomp,
    coherentConeCosliceSection, sliceUnderUncurry_curry]

/-- 概要：slice の錐の点を共通模型で評価すると点の直積成分を射影した元の錐となる。
方針：普遍族の式と点の join・直積の比較の単位則を使う。
規約：固定点は coneVertexFiberPoint d そのもの。
使われ方：Kerodon 7.4.1.6、slice と切断で同じ元の錐を固定することの検証。 -/
lemma sliceEndpointConeComparison_point_uncurry {K X : SSet.{u}} {p : K ⟶ X}
    (d : JoinCone p) :
    uncurry (SSet.yonedaEquiv.symm (coneVertexFiberPoint d) ≫
        sliceEndpointConeComparison p d.vertex ≫ endpointConeEvaluation p d.vertex) =
      fst (join (Δ[0] : SSet.{u}) K) (Δ[0] : SSet.{u}) ≫ d.val := by
  rw [sliceEndpointConeComparison_uncurry, SSet.yonedaEquiv_symm_comp]
  change _ ≫ _ ≫ _ ≫ sliceOverUncurry (SSet.yonedaEquiv.symm d) = _
  rw [sliceOverUncurry_yoneda]
  have h : fst (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u}) =
      snd (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u}) := stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h, ← Category.assoc (joinTensorLeft _ _ _), joinTensorLeft_unit, ← Category.assoc]
  rfl

/-- 概要：標準の切断の錐の点を共通模型で評価すると元の錐を回収する。
方針：切断の点の展開と右側の join・直積の比較の単位則を使う。
規約：選んだ頂点 fiber・切断同値の像ではなく標準の切断の点を使う。
使われ方：Kerodon 7.4.1.6、標準の切断制限の fiber の固定点の保持。 -/
lemma sectionEndpointConeComparison_point_uncurry {K X : SSet.{u}} {p : K ⟶ X}
    (d : JoinCone p) :
    uncurry (SSet.yonedaEquiv.symm (coherentConeSectionPoint d) ≫
        sectionEndpointConeComparison p d.vertex ≫ endpointConeEvaluation p d.vertex) =
      fst (join (Δ[0] : SSet.{u}) K) (Δ[0] : SSet.{u}) ≫ d.val := by
  rw [sectionEndpointConeComparison_uncurry, sectionConeUncurry_sectionPoint,
    ← Category.assoc, joinTensorRight_unit]

/-- 概要：同じ錐の slice の点と標準の切断の点は両端固定の共通模型で厳密に一致する。
方針：二つの fiber の包含と uncurry の単射性で、展開した元の錐の一致へ帰着する。
規約：充填性も同値の選択も不要。零単体の等式として述べる。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6、slice・切断の導来 fiber の固定点の同定。 -/
lemma coneEndpointComparison_point_eq {K X : SSet.{u}} {p : K ⟶ X} (d : JoinCone p) :
    (sliceEndpointConeComparison p d.vertex).app _ (coneVertexFiberPoint d) =
      (sectionEndpointConeComparison p d.vertex).app _ (coherentConeSectionPoint d) := by
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.yonedaEquiv_symm_comp, ← SSet.yonedaEquiv_symm_comp]
  apply vertexFiber_hom_ext
    ((pre (joinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
    (functorVertex (joinEndpointDesc (SSet.yonedaEquiv.symm d.vertex) p))
  change (SSet.yonedaEquiv.symm (coneVertexFiberPoint d) ≫
    sliceEndpointConeComparison p d.vertex) ≫ endpointConeEvaluation p d.vertex =
      (SSet.yonedaEquiv.symm (coherentConeSectionPoint d) ≫
        sectionEndpointConeComparison p d.vertex) ≫ endpointConeEvaluation p d.vertex
  apply uncurry_injective
  simp only [Category.assoc]
  exact (sliceEndpointConeComparison_point_uncurry d).trans
    (sectionEndpointConeComparison_point_uncurry d).symm

end
end SerrePositivity.InfinityCategories.HomotopyLimits
