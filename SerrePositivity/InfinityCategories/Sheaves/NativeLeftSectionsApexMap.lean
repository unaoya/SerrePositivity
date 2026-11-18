module

public import SerrePositivity.InfinityCategories.Sheaves.RightKanMovingTransportApex
public import SerrePositivity.InfinityCategories.Sheaves.NativeLeftSectionsTransportCone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitComparisonRestrictionSquare

/-!
概要：指定右 Kan 輸送を小さい left 全空間へ制限すると、元の比較錐の射に同じ頂点射が出る。
方針：指定した辺と添字の座標に既存の評価則を適用する。
使われ方：離散前層の重み付き切断の自然性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Sheaves
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

namespace SerrePositivity.InfinityCategories.Sheaves

private lemma transportApex_of_diagramEq
    {J K C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    {δ : K ⟶ C} {O : K ⟶ D} {G : C ⟶ D} (α : SSet.Homotopy (δ ≫ G) O)
    {v₀ v₁ : C _⦋0⦌} (e : C.Edge v₀ v₁)
    (j₀ : J ⟶ rightKanShape δ v₀) (j₁ : J ⟶ rightKanShape δ v₁)
    (hj : j₀ ≫ rightKanProjection δ v₀ = j₁ ≫ rightKanProjection δ v₁)
    (hface : rightKanMovingIndexFace δ (SSet.yonedaEquiv.symm e.edge)
      e.δ_one_yonedaEquiv_symm e.δ_zero_yonedaEquiv_symm j₀ j₁)
    (t₀ : RightKanConeTransport δ O G α v₀) (t₁ : RightKanConeTransport δ O G α v₁)
    (p : J ⟶ D) (hp : (j₀ ≫ rightKanProjection δ v₀) ≫ O = p)
    (h₀ : j₀ ≫ rightKanDiagram δ O v₀ = p) (h₁ : j₁ ≫ rightKanDiagram δ O v₁ = p)
    (c d : JoinCone p)
    (hcv : c.val = (restrictJoinCone t₀.cone j₀).val)
    (hdv : d.val = (restrictJoinCone t₁.cone j₁).val)
    (hc : c.vertex = G.app _ v₀) (hd : d.vertex = G.app _ v₁)
    (hl : IsLimitCone d)
    (k : (HomotopyCategory.mk c : hoFunctor.obj (sliceOver p)) ⟶ HomotopyCategory.mk d) :
    Truncated.HomotopyCategory.homMk (e.map G).toTruncated =
      eqToHom (congrArg HomotopyCategory.mk hc).symm ≫
        (hoFunctor.map (sliceOverProjection p)).toFunctor.map k ≫
          eqToHom (congrArg HomotopyCategory.mk hd) := by
  have ec : c = (restrictJoinCone t₀.cone j₀).cast h₀ := Subtype.ext hcv
  have ed : d = (restrictJoinCone t₁.cone j₁).cast h₁ := Subtype.ext hdv
  subst c d p
  exact rightKanMovingIndex_transportApex α e j₀ j₁ hj hface t₀ t₁ h₀ h₁ hl k

/-- 指定右 Kan 輸送を小さい left 全空間へ制限すると、元の比較錐の射に同じ頂点射が出る。
Kerodon Definition 7.3.1.2（Tag 02Y9）、HTT 5.1.5.6 の指定局所極限。 -/
lemma nativeLeftSectionsTransport_apexMap
    {A : SSet.{u}} [Quasicategory A]
    {P Q : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u}}
    {E : SSet.{u + 1}} [Quasicategory E]
    (O : ((SSet.uliftFunctor.{u + 1, u}).obj A).op ⟶ E) (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let δ := SSet.opFunctor.map (yonedaInfinityMap A)
    let v₀ := SSet.opObjEquiv.symm (functorVertex Q)
    let v₁ := SSet.opObjEquiv.symm (functorVertex P)
    ∀ (e : (PresheafInfinity A).op.Edge v₀ v₁)
      (a : U.obj (smallLeftUnstraightening P) ⟶ U.obj (smallLeftUnstraightening Q)),
    let j₀ := a ≫ leftElementsRightKanComparison Q
    let j₁ := leftElementsRightKanComparison P
    ∀ (hj : j₀ ≫ rightKanProjection δ v₀ = j₁ ≫ rightKanProjection δ v₁)
      (hface : rightKanMovingIndexFace δ (SSet.yonedaEquiv.symm e.edge)
        e.δ_one_yonedaEquiv_symm e.δ_zero_yonedaEquiv_symm j₀ j₁)
      (h : a ≫ nativeLeftSectionsDiagram Q O = nativeLeftSectionsDiagram P O),
    let c := nativeLeftSectionsTransportCone Q O hE
    let d := nativeLeftSectionsTransportCone P O hE
    let rc := (restrictJoinCone c a).cast h
    let hc := ((JoinCone.vertex_cast _ h).trans (restrictJoinCone_vertex c a)).trans
      (nativeLeftSectionsTransportCone_vertex Q O hE)
    let hd := nativeLeftSectionsTransportCone_vertex P O hE
    ∀ (k : (HomotopyCategory.mk rc : hoFunctor.obj (sliceOver (nativeLeftSectionsDiagram P O))) ⟶
      HomotopyCategory.mk d),
    Arrow.mk (Truncated.HomotopyCategory.homMk (e.map (nativeWeightedSections O hE)).toTruncated) =
      Arrow.mk ((hoFunctor.map (sliceOverProjection (nativeLeftSectionsDiagram P O))).toFunctor.map k) := by
  intro U δ v₀ v₁ e a j₀ j₁ hj hface h c d rc hc hd k
  let G := nativeWeightedSections O hE
  let α := (nativeWeightedSectionsData O hE).2.val
  let t₀ := nativeWeightedSections_valueTransport O hE v₀
  let t₁ := nativeWeightedSections_valueTransport O hE v₁
  let D := nativeLeftSectionsDiagram P O
  have hp₁ : j₁ ≫ rightKanDiagram δ O v₁ = D := by
    let w := U.map (smallLeftUnstraighteningProjection P)
    let i := (uliftOppositeIso A).hom
    have hproj : j₁ ≫ rightKanProjection δ v₁ = w ≫ i :=
      leftElementsRightKanComparison_projection P
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ O) hproj).trans (Category.assoc _ _ _))
  have hp : (j₀ ≫ rightKanProjection δ v₀) ≫ O = D := by
    rw [hj, Category.assoc]
    exact hp₁
  have hp₀ : j₀ ≫ rightKanDiagram δ O v₀ = D := (Category.assoc _ _ _).symm.trans hp
  have hcv : rc.val = (restrictJoinCone t₀.cone j₀).val := by
    change joinMap (𝟙 Δ[0]) a ≫ (joinMap (𝟙 Δ[0]) (leftElementsRightKanComparison Q) ≫ _) =
      joinMap (𝟙 (Δ[0] : SSet.{u+1})) j₀ ≫ _
    rw [← Category.assoc, ← joinMap_comp, Category.id_comp]
    rfl
  have hdv : d.val = (restrictJoinCone t₁.cone j₁).val := rfl
  have H := transportApex_of_diagramEq α e j₀ j₁ hj hface t₀ t₁ D hp hp₀ hp₁
    rc d hcv hdv hc hd (nativeLeftSectionsTransportCone_isLimit P O hE) k
  simpa only [Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom] using congrArg Arrow.mk H

end SerrePositivity.InfinityCategories.Sheaves
