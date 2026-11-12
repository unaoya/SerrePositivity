module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsLimitNaturality
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightSectionsLimitFactorization
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightSpaceValueComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.ConeSectionsValueEdgeNaturality
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.SectionsConeMapEquivalence
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsNaturality

/-!
概要：G8 の正本の比較の後段を、元の選択のまま独立に表示する。
方針：切断錐から指定極限への辺、宇宙変更、表現可能値の比較を同じ順で合成する。
規約：既存の比較の本文・型・選択を変更しない。
使われ方：G8 の四角形②の全族自然性の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions MorphismSpaces IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors

namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

/-- 概要：指定極限頂点の同じ値比較は、同じ錐の辺の値の作用と全写像として同型。
方針：元の値比較の類を回収し、錐の終対象性で同じ辺の類と照合する。
規約：指定した比較の実射を保持。使われ方：G8 の切断錐から指定極限への接続。 -/
def limitVertexValue_edgeIso {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}
    (c d : JoinCone F) (hc : IsLimitCone c) (hd : IsLimitCone d)
    (e : (sliceOver F).Edge c d) :
    FunctorIso (SetWeight.spaceValueEquivalence (limitVertexIso c d hc hd)).hom
      (spaceInfinityEdgeValue (e.map (sliceOverProjection F))) := by
  apply spaceValueFunctorIso_of_homClass_eq (x := c.vertex) (y := d.vertex)
  rw [spaceValueHomClass_spaceValueEquivalence, spaceValueHomClass_edgeValue]
  exact SetWeight.limitVertexIso_hom_eq_coneEdge c d hc hd e

/-- 概要：指定極限頂点の同じ値比較は、元の錐の値の切断写像と全族で可換。
方針：二つの極限錐の間の辺を取り、その実際の値の自然性へ同じ頂点比較を移す。
規約：新しい選択した極限には置き換えない。使われ方：G8 の後段の極限比較。 -/
def limitVertexValue_coneSectionsIso {B : SSet.{u}}
    {F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (c d : JoinCone F) (hc : IsLimitCone c) (hd : IsLimitCone d) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map
        (SetWeight.spaceValueEquivalence (limitVertexIso c d hc hd)).hom ≫
          coneSectionsValueMapAt F d d.vertex rfl)
      (coneSectionsValueMapAt F c c.vertex rfl) := by
  let e : (sliceOver F).Edge c d := SSet.Edge.ofTruncated
    (homotopyCategory_homMk_surjective (X := sliceOver F) c d
      (limitConeIso c d hc hd).hom).choose
  exact (FunctorIso.postcomp
    (FunctorIso.ulift.{u, u + 1} (limitVertexValue_edgeIso c d hc hd e))
      (coneSectionsValueMapAt F d d.vertex rfl)) ≪≫ coneSectionsValueMap_edgeIso e

/-- 概要：同じ切断錐の頂点を指定表示しても、値の切断写像との比較は保たれる。
方針：頂点の等式を消去して、同じ極限頂点の比較を使う。
規約：表示以外を変更しない。使われ方：選ばれた切断錐の頂点の正規化。 -/
def limitVertexValueAt_coneSectionsIso {B : SSet.{u}}
    {F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (c d : JoinCone F) (hc : IsLimitCone c) (hd : IsLimitCone d)
    (z : SpaceInfinity.{u} _⦋0⦌) (hv : c.vertex = z) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map
        (SetWeight.spaceValueEquivalence
          (show VertexIso z d.vertex from by rw [← hv]; exact limitVertexIso c d hc hd)).hom ≫
          coneSectionsValueMapAt F d d.vertex rfl)
      (coneSectionsValueMapAt F c z hv) := by
  cases hv
  exact limitVertexValue_coneSectionsIso c d hc hd

/-- 概要：正本の切断から指定極限への同じ比較は、元の値の切断写像の右逆になる。
方針：同じ極限頂点の比較と、切断錐の恒等写像への全族同型を合成する。
規約：元の選ばれた順射を保持。使われ方：G8 の切断制限との接続。 -/
def sectionsLimitValueEquivalence_coneSectionsIso {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (c : JoinCone F) (hc : IsLimitCone c) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (sectionsLimitValueEquivalence F c hc).hom ≫
        coneSectionsValueMapAt F c c.vertex rfl)
      (𝟙 _) := by
  let a := eqToIso (coherentSpaceSectionsVertex_object F)
  have h₀ := limitVertexValueAt_coneSectionsIso (coherentDiagramSectionsCone F) c
    (coherentDiagramSectionsCone_isLimit F) hc (coherentSpaceSectionsVertex F)
    (coherentDiagramSectionsCone_vertex F)
  have h₁ := FunctorIso.precomp h₀ ((SSet.uliftFunctor.{u + 1, u}).map a.inv)
  have h₂ := FunctorIso.precomp (coherentSectionsConeValueIdentityIso F)
    ((SSet.uliftFunctor.{u + 1, u}).map a.inv)
  have he : (SSet.uliftFunctor.{u + 1, u}).map a.inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (coherentSpaceSectionsIdentity F) = 𝟙 _ := by
    rw [← Functor.map_comp]
    change (SSet.uliftFunctor.{u + 1, u}).map (a.inv ≫ a.hom) = _
    rw [Iso.inv_hom_id]
    exact (SSet.uliftFunctor.{u + 1, u}).map_id _
  rw [he] at h₂
  simp only [sectionsLimitValueEquivalence, QCatEquivalence.trans,
    QCatEquivalence.symm, qCatEquivalenceOfIso, CategoryTheory.Functor.map_comp, Category.assoc]
  convert h₁ ≪≫ h₂ using 1 <;> rfl

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
