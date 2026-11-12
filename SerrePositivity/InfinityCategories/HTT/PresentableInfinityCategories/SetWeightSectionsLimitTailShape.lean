module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightMappedSectionsEdge

/-!
概要：G8 の正本の後段は、実切断の形状制限と標準後合成を全族で結ぶ。
方針：指定極限の値比較の形状自然性に、同じテンソル随伴の Hom 値比較を合成する。
規約：元の随伴・極限錐・普遍辺・比較同値の選択をすべて保持する。
使われ方：四角形②の固定端点錐への全族比較、および空間のホモトピー圏への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

/-- 元の指定極限への後段は、実切断の制限と同じ普遍辺の標準後合成に全自然。 -/
def setWeightSectionsLimitTail_shapeIso {I : Type u} [SmallCategory I]
    {X Y : I ⥤ Type u} (φ : X ⟶ Y)
    {E : SSet.{u + 1}} [Quasicategory E] (hE : IsPresentable E) (M : E _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)
    (cX : JoinCone (SetWeight.diagram X F)) (hcX : IsLimitCone cX)
    (cY : JoinCone (SetWeight.diagram Y F)) (hcY : IsLimitCone cY) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map
        (setWeightActualSectionsRestriction φ (F ≫ (spaceTensorData hE M).hom)) ≫
          (setWeightSectionsLimitTail X hE M F cX hcX).hom)
      ((setWeightSectionsLimitTail Y hE M F cY hcY).hom ≫
        postcompose M (SSet.Truncated.HomotopyCategory.homMk
          (SetWeight.sectionsMap φ F cX hcX cY hcY))) := by
  let t := spaceTensorData hE M
  let gY := SetWeight.diagram Y (F ≫ t.hom)
  let gX := SetWeight.diagram X (F ≫ t.hom)
  let d := mapJoinCone t.hom (SetWeight.restrictSectionsCone φ F cY)
  have hd : d.val = joinMap (𝟙 (Δ[0] : SSet.{u + 1}))
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap φ.mapElements)) ≫
        (mapJoinCone t.hom cY).val := rfl
  have hv : d.vertex = (mapJoinCone t.hom cY).vertex := by
    simp only [d, mapJoinCone_vertex, SetWeight.restrictSectionsCone_vertex]
  let e := setWeightMappedSectionsConeEdge φ F cX hcX cY t.hom
  let δ := SetWeight.sectionsMap φ F cX hcX cY hcY
  have he : coneApexEdgeAt e (mapJoinCone t.hom cY).vertex hv = δ.map t.hom := by
    apply SSet.Edge.ext
    change (Eq.mp (congrArg (fun z ↦ SSet.Edge z (mapJoinCone t.hom cX).vertex) hv)
      (e.map (sliceOverProjection gX))).edge = _
    rw [edge_source_transport_simplex hv]
    exact setWeightMappedSectionsConeEdge_simplex φ F cX hcX cY hcY t.hom
  have h := sectionsLimitValue_normalizedShapeIso gY gX (nerveMap φ.mapElements)
    (SetWeight.elementsMap_diagram φ (F ≫ t.hom))
    (mapJoinCone t.hom cY) (mapJoinCone_isLimit_of_adjunction t.adjunction cY hcY)
    (mapJoinCone t.hom cX) (mapJoinCone_isLimit_of_adjunction t.adjunction cX hcX)
    d hd hv e
  rw [he] at h
  have h₀ := FunctorIso.postcomp h (spaceTensorHomValueTail t cX.vertex).hom
  have h₁ := FunctorIso.precomp (spaceTensorHomValueTail_edgeIso t δ)
    ((SSet.uliftFunctor.{u + 1, u}).map
      (sectionsLimitValueEquivalence gY (mapJoinCone t.hom cY)
        (mapJoinCone_isLimit_of_adjunction t.adjunction cY hcY)).hom)
  simp only [Category.assoc] at h₀ h₁
  simpa only [setWeightSectionsLimitTail, setWeightActualSectionsRestriction,
    spaceTensorHomValueTail, QCatEquivalence.trans, IsQCatEquivalence.choose,
    Category.assoc, t, gX, gY, δ] using h₀ ≪≫ h₁

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
