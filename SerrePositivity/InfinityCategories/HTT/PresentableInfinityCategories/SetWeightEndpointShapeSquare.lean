module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightLimitTailConeSquare
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightEndpointRestrictionComparison
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightFixedEndpointEdgeComparison

/-!
概要：元の後段の形状自然性を、固定端点の錐の実際の制限と結ぶ。
方針：既存の錐の制限・指定辺の全族比較を合成し、同じ後段で前合成する。
規約：頂点の等式による移送を保持し、制限射を別の選択に置き換えない。
使われ方：切断制限の厳密な等式 sectionsConeFamilyRestriction_fromSections との接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

/-- 元の制限錐を指定表示しても、固定端点模型での全族比較を保つ。 -/
def limitConeEndpointComparison_restrictAtIso {K J E : SSet.{u}} [Quasicategory E]
    (p : J ⟶ E) (q : K ⟶ E) (i : K ⟶ J) (hi : i ≫ p = q)
    (c : JoinCone p) (d : JoinCone q)
    (hd : d.val = joinMap (𝟙 (Δ[0] : SSet.{u})) i ≫ c.val)
    (hv : d.vertex = c.vertex) (x : E _⦋0⦌) :
    FunctorIso
      (eqToHom (congrArg (Basic.pinchedHom x) hv.symm) ≫
        SetWeight.limitConeEndpointComparison d x)
      (SetWeight.limitConeEndpointComparison c x ≫
        normalizedEndpointConeRestriction p q i hi x) := by
  subst q
  have hd' : d = restrictJoinCone c i := Subtype.ext hd
  subst d
  simpa only [normalizedConeRestriction, eqToHom_refl, Category.comp_id,
    Category.id_comp, restrictJoinCone, JoinCone.vertex, NatTrans.comp_app,
    NatTrans.id_app, types_comp_apply, types_id_apply] using
    limitConeEndpointComparison_restrictIso p (i ≫ p) i rfl c x

/-- 辺の始点の表示変更は、標準後合成の始域の表示変更に一致する。 -/
lemma postcompose_source_transport {E : SSet.{u}} [Quasicategory E]
    (x : E _⦋0⦌) {y y' z : E _⦋0⦌} (h : y = y') (e : E.Edge y z) :
    eqToHom (congrArg (Basic.pinchedHom x) h.symm) ≫
      postcompose x (Truncated.HomotopyCategory.homMk e) =
    postcompose x (Truncated.HomotopyCategory.homMk
      (Eq.mp (congrArg (fun t ↦ E.Edge t z) h) e)) := by
  cases h
  exact Category.id_comp _

/-- 同じ指定普遍辺の後合成は、固定端点錐の元の形状制限と全族で可換。 -/
def setWeightEndpointRestriction_sectionsMapIso {I : Type u} [SmallCategory I]
    {X Y : I ⥤ Type u} (φ : X ⟶ Y) {E : SSet.{u + 1}} [Quasicategory E]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)
    (cX : JoinCone (SetWeight.diagram X F)) (hcX : IsLimitCone cX)
    (cY : JoinCone (SetWeight.diagram Y F)) (hcY : IsLimitCone cY) (M : E _⦋0⦌) :
    FunctorIso
      (SetWeight.limitConeEndpointComparison cY M ≫
        SetWeight.sectionsConeFamilyRestriction φ F M)
      (postcompose M (Truncated.HomotopyCategory.homMk
        (SetWeight.sectionsMap φ F cX hcX cY hcY)) ≫
        SetWeight.limitConeEndpointComparison cX M) := by
  let d := SetWeight.restrictSectionsCone φ F cY
  let hv := SetWeight.restrictSectionsCone_vertex φ F cY
  let a := eqToHom (congrArg (Basic.pinchedHom M) hv.symm)
  have hr := limitConeEndpointComparison_restrictAtIso
    (SetWeight.diagram Y F) (SetWeight.diagram X F) (SetWeight.elementsMap φ)
    (SetWeight.elementsMap_diagram φ F) cY d rfl hv M
  have he := FunctorIso.precomp (setWeightLimitConeEndpointComparison_edgeIso
    (SetWeight.sectionsConeMap φ F cX hcX cY) M) a
  have hδ : a ≫ postcompose M (Truncated.HomotopyCategory.homMk
      ((SetWeight.sectionsConeMap φ F cX hcX cY).map
        (sliceOverProjection (SetWeight.diagram X F)))) =
      postcompose M (Truncated.HomotopyCategory.homMk
        (SetWeight.sectionsMap φ F cX hcX cY hcY)) :=
    postcompose_source_transport M hv _
  have h := hr.symm ≪≫ he
  simp only [← Category.assoc] at h
  rw [hδ] at h
  exact h

/-- 元の後段を固定端点模型へ送る比較は、元の錐の族の制限に全自然。 -/
def setWeightLimitTail_endpointRestrictionIso {I : Type u} [SmallCategory I]
    {X Y : I ⥤ Type u} (φ : X ⟶ Y) {E : SSet.{u + 1}} [Quasicategory E]
    (hE : IsPresentable E) (M : E _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)
    (cX : JoinCone (SetWeight.diagram X F)) (hcX : IsLimitCone cX)
    (cY : JoinCone (SetWeight.diagram Y F)) (hcY : IsLimitCone cY) :
    FunctorIso
      (((SSet.uliftFunctor.{u + 1, u}).map
        (setWeightActualSectionsRestriction φ (F ≫ (spaceTensorData hE M).hom)) ≫
          (setWeightSectionsLimitTail X hE M F cX hcX).hom) ≫
        SetWeight.limitConeEndpointComparison cX M)
      (((setWeightSectionsLimitTail Y hE M F cY hcY).hom ≫
        SetWeight.limitConeEndpointComparison cY M) ≫
        SetWeight.sectionsConeFamilyRestriction φ F M) := by
  have h := FunctorIso.precomp
    (setWeightEndpointRestriction_sectionsMapIso φ F cX hcX cY hcY M)
    (setWeightSectionsLimitTail Y hE M F cY hcY).hom
  have h₀ := setWeightLimitTailConeFamilyIso φ hE M F cX hcX cY hcY
  simp only [Category.assoc] at h₀ h
  simpa only [Category.assoc] using h₀ ≪≫ h.symm

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
