module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.SiteLiftRepresentableSectionsRestriction
public import SerrePositivity.InfinityCategories.Sheaves.SiteLiftLocalEquivalence
public import SerrePositivity.InfinityCategories.Sheaves.AsSmallSiteInvariance
public import SerrePositivity.InfinityCategories.Sheaves.SectionsSpaceLocalEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.NormalizedSliceRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RepresentableLimitCharacterization

/-!
概要：表現可能関手は、局所同値に沿って制限した同じ指定切断錐を極限錐に送る。
方針：持ち上げた site で空間値の結果を使い、制限と表現可能値の全錐の比較で戻す。
  文献対応：HTT 6.2.2.6、Kerodon §7.1（Tag 02H1）。
使われ方：集合値局所同値に沿う指定切断の可逆性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors

namespace SerrePositivity.InfinityCategories.Sheaves

private lemma spaceRestriction_isLimit
    {C : Type u} [SmallCategory C] (K : GrothendieckTopology C)
    {P Q : Cᵒᵖ ⥤ Type u} (a : P ⟶ Q) (ha : IsLocalEquivSet K a)
    (G : Presheaf C SpaceInfinity.{u}) (hG : IsSheaf K G)
    (t : JoinCone (sectionsOfDiagram Q G)) (ht : IsLimitCone t) :
    IsLimitCone (SetWeight.restrictSectionsCone a G t) := by
  let hP := sectionsOfDiagram_hasLimit space_isPresentable.{u} P G
  let hQ := sectionsOfDiagram_hasLimit space_isPresentable.{u} Q G
  let cP := sectionsOfCone P G hP
  let cQ := sectionsOfCone Q G hQ
  let hcP := sectionsOfCone_isLimit P G hP
  let hcQ := sectionsOfCone_isLimit Q G hQ
  have hQ' : IsLimitCone (SetWeight.restrictSectionsCone a G cQ) :=
    (sectionsMap_isInvertible_iff a G cP hcP cQ hcQ).mp
      (sections_localEquiv_iso_space K a ha G hG hP hQ)
  let j := SetWeight.elementsMap a
  let e := (hoFunctor.map (sliceOverRestrict (sectionsOfDiagram Q G) j)).toFunctor.mapIso
    (limitConeIso t cQ ht hcQ)
  exact
    (isLimitCone_iff_of_cone_val_eq _ (restrictJoinCone t j) rfl).mpr
      ((isLimitCone_iff_of_vertexIso e).mpr
        ((isLimitCone_iff_of_cone_val_eq _ (restrictJoinCone cQ j) rfl).mp hQ'))

private lemma siteLiftRepresentable_isSheaf
    {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
    (J : GrothendieckTopology C) (O : Presheaf C E) (hO : IsSheaf J O) (x : E _⦋0⦌) :
    IsSheaf ((AsSmall.down : AsSmall.{u + 1} C ⥤ C).inducedTopology J)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map ((asSmallSiteShapeIso C).inv ≫ O) ≫
        covariantRepresentableInfinity x) := by
  let i := asSmallSiteShapeIso C
  let F := i.inv ≫ O
  have hi : i.hom ≫ F = O := Iso.hom_inv_id_assoc _ _
  have hO' : IsSheaf J (i.hom ≫ F) := hi.symm ▸ hO
  exact ((isSheaf_asSmall_inducedTopology_iff J F).mp hO').covariantRepresentable x

private lemma isLimitCone_of_siteLiftRepresentable
    {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
    (P : Cᵒᵖ ⥤ Type u) (O : Presheaf C E) (s : JoinCone (sectionsOfDiagram P O))
    (x : E _⦋0⦌)
    (h : IsLimitCone (mapJoinCone (covariantRepresentableInfinity x)
      (JoinCone.ulift.{u + 1, u + 2} (siteLiftSectionsCone P O s)))) :
    IsLimitCone (mapJoinCone (covariantRepresentableInfinity x)
      (JoinCone.ulift.{u + 1, u + 2} s)) := by
  let U := SSet.uliftFunctor.{u + 2, u + 1}
  let Y := covariantRepresentableInfinity x
  let v := mapJoinCone Y (JoinCone.ulift.{u + 1, u + 2} s)
  let b := (siteLiftElementsShapeIso P).inv
  have hv : (mapJoinCone Y (JoinCone.ulift.{u + 1, u + 2} (siteLiftSectionsCone P O s))).val =
      (restrictJoinCone v (U.map b)).val := by
    change (JoinCone.ulift.{u + 1, u + 2} (restrictJoinCone s b)).val ≫ Y =
      joinMap (𝟙 _) (U.map b) ≫ ((JoinCone.ulift.{u + 1, u + 2} s).val ≫ Y)
    rw [ulift_restrictJoinCone_val]
    exact Category.assoc _ _ _
  have hrv := (isLimitCone_iff_of_cone_val_eq _ _ hv).mp h
  letI : IsIso (U.map b) := inferInstanceAs
    (IsIso (U.mapIso (siteLiftElementsShapeIso P).symm).hom)
  exact (isLimitCone_restrict_iff_of_isIso v (U.map b)).mp hrv

private lemma siteLiftRestrictedRepresentable_isLimit
    {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
    (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q)
    (hφ : IsLocalEquivSet J φ) (O : Presheaf C E) (hO : IsSheaf J O)
    (c : JoinCone (sectionsOfDiagram Q O)) (hc : IsLimitCone c) (x : E _⦋0⦌) :
    let U := SSet.uliftFunctor.{u + 2, u + 1}
    let Y := covariantRepresentableInfinity x
    let F := (asSmallSiteShapeIso C).inv ≫ O
    let G := U.map F ≫ Y
    let a := siteLiftPresheafMap φ
    let t := mapJoinCone Y (JoinCone.ulift.{u + 1, u + 2} (siteLiftSectionsCone Q O c))
    IsLimitCone (SetWeight.restrictSectionsCone a G t) := by
  intro U Y F G a t
  let K := (AsSmall.down : AsSmall.{u + 1} C ⥤ C).inducedTopology J
  have hG : IsSheaf K G := siteLiftRepresentable_isSheaf J O hO x
  have ha : IsLocalEquivSet K a := isLocalEquivSet_siteLift J φ hφ
  let c' := siteLiftSectionsCone Q O c
  have hc' : IsLimitCone c' := (siteLiftSectionsCone_isLimit_iff Q O c).mpr hc
  have ht : IsLimitCone t := covariantRepresentableInfinity_isLimit c' hc' x
  exact spaceRestriction_isLimit (C := AsSmall.{u + 1} C) K a ha G hG t ht

/-- 表現可能関手は、局所同値に沿って制限した同じ指定切断錐を極限錐に送る。 -/
@[cite HTT "6.2.2.6" (partial := special) "小さい通常の site の集合値前層の局所同値。"]
lemma representable_restrictedSectionsCone_isLimit :
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q)
 (hφ : IsLocalEquivSet J φ) (O : Presheaf C E) (hO : IsSheaf J O),
∀ (c : JoinCone (sectionsOfDiagram Q O)) (hc : IsLimitCone c) (x : E _⦋0⦌),
let U := SSet.uliftFunctor.{u + 2, u + 1};
let Y := covariantRepresentableInfinity x;
IsLimitCone (mapJoinCone Y (JoinCone.ulift.{u + 1, u + 2}
 (SetWeight.restrictSectionsCone φ O c))) := by
  intro C hC E hQC J P Q φ hφ O hO c hc x U Y
  let s := SetWeight.restrictSectionsCone φ O c
  have hR := siteLiftRestrictedRepresentable_isLimit J φ hφ O hO c hc x
  have hval := siteLift_representable_restrictSectionsCone_val φ O c x
  exact isLimitCone_of_siteLiftRepresentable P O s x
    ((isLimitCone_iff_of_cone_val_eq _ _ hval).mp hR)

end SerrePositivity.InfinityCategories.Sheaves
