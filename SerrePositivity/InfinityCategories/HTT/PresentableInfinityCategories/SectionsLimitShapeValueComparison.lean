module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SectionsLimitValueInverse
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.NormalizedSectionsValueShape

/-!
概要：実切断の形状制限と同じ指定極限の値比較を、指定した錐の辺で結ぶ。
方針：錐の値の切断写像の形状自然性・辺自然性を合成し、同じ値比較で相殺する。
規約：両側の極限錐と元の切断比較を保持する。各頂点でなく全写像の同型。
使われ方：G8 の後段で、同じテンソル随伴による普遍辺を代入する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
universe u
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

/-- 錐の辺の頂点を指定表示へ移した値の辺。 -/
def coneApexEdgeAt {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}
    {c d : JoinCone F} (e : (sliceOver F).Edge c d)
    (z : SpaceInfinity.{u} _⦋0⦌) (hz : c.vertex = z) : SSet.Edge z d.vertex :=
  Eq.mp (congrArg (fun t ↦ SSet.Edge t d.vertex) hz) (e.map (sliceOverProjection F))

/-- 始点の表示を移しても、元の錐の辺の値と切断写像の全族比較を保つ。 -/
def coneSectionsValueMap_edgeAtIso {B : SSet.{u}}
    {F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    {c d : JoinCone F} (e : (sliceOver F).Edge c d)
    (z : SpaceInfinity.{u} _⦋0⦌) (hz : c.vertex = z) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (spaceInfinityEdgeValue (coneApexEdgeAt e z hz)) ≫
        coneSectionsValueMapAt F d d.vertex rfl)
      (coneSectionsValueMapAt F c z hz) := by
  cases hz
  exact coneSectionsValueMap_edgeIso e

/-- 元の切断制限と同じ指定極限比較は、制限錐からの指定辺の値に全自然。 -/
def sectionsLimitValue_normalizedShapeIso {B K : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ SpaceInfinity.{u})
    (i : K ⟶ B) (hi : (SSet.uliftFunctor.{u + 1, u}).map i ≫ F = G)
    (cY : JoinCone F) (hcY : IsLimitCone cY)
    (cX : JoinCone G) (hcX : IsLimitCone cX) (d : JoinCone G)
    (hd : d.val = joinMap (𝟙 (Δ[0] : SSet.{u + 1}))
      ((SSet.uliftFunctor.{u + 1, u}).map i) ≫ cY.val)
    (hv : d.vertex = cY.vertex) (e : (sliceOver G).Edge d cX) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (normalizedSmallSectionsRestriction F G i hi) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (sectionsLimitValueEquivalence G cX hcX).hom)
      ((SSet.uliftFunctor.{u + 1, u}).map (sectionsLimitValueEquivalence F cY hcY).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (spaceInfinityEdgeValue (coneApexEdgeAt e cY.vertex hv))) := by
  let U := SSet.uliftFunctor.{u + 1, u}
  let ρ := U.map (normalizedSmallSectionsRestriction F G i hi)
  let a := U.map (sectionsLimitValueEquivalence F cY hcY).hom
  let b := U.map (sectionsLimitValueEquivalence G cX hcX).hom
  let v := U.map (spaceInfinityEdgeValue (coneApexEdgeAt e cY.vertex hv))
  have hshape := coneSectionsValueMapAt_normalizedShapeIso F G i hi cY d hd cY.vertex rfl hv
  have hedge := coneSectionsValueMap_edgeAtIso e cY.vertex hv
  have h := FunctorIso.precomp (hedge ≪≫ hshape.symm) a
  have hu := FunctorIso.postcomp (sectionsLimitValueEquivalence_coneSectionsIso F cY hcY) ρ
  simp only [Category.assoc] at h hu
  have h₀ : FunctorIso (a ≫ v ≫ coneSectionsValueMapAt G cX cX.vertex rfl) ρ := by
    simpa only [Category.assoc, Category.id_comp, a, v, ρ] using h ≪≫ hu
  have h₁ := FunctorIso.postcomp h₀ b
  have h₂ := FunctorIso.precomp (coneSectionsValueMap_sectionsLimitValueIso G cX hcX) (a ≫ v)
  simp only [Category.assoc] at h₁ h₂
  simpa only [Category.assoc, Category.comp_id, a, b, v, ρ] using h₁.symm ≪≫ h₂

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
