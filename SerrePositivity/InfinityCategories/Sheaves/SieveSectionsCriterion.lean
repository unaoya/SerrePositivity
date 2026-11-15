module

public import SerrePositivity.InfinityCategories.Sheaves.SectionsOf
public import SerrePositivity.InfinityCategories.Sheaves.RepresentableSections

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSections
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationReflection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.QCatEquivalence
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.UniverseConeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.PointConeLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.PointJoinNerveExt
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.SimplexConeRestriction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableSmallLimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.EquivalentConeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeNaturality
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Sites.Sieves.Presheaf
public import SerrePositivity.InfinityCategories.Sheaves.GlobalSections
public import SerrePositivity.InfinityCategories.Sheaves.SieveSectionsDiagram

/-!
概要：集合重みの指定切断錐を、元の篩の制限錐へ接続する。
方針：既存のG8の射と錐の普遍性を使い、全錐の再添字を照合する。
使われ方：HTT 6.2.2.6、Kerodon §7.1（Tag 02H1）の層条件の切断表示。
規約：元の指定錐・比較辺を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Sheaves
variable {𝒞 : Type u} [SmallCategory 𝒞] {E : SSet.{u+1}} [Quasicategory E]

/-! ## 制限辺の可逆性と restrictionCone の極限性 -/

/-- 終錐への比較辺は、その頂点辺が可逆なとき、かつそのときだけ極限錐から来る。
右ファイブレーションの反映性を使うので、頂点の同型だけで錐を比較しない。 -/
lemma coneComparison_isInvertible_iff {K : SSet.{u + 1}} {p : K ⟶ E}
    (c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d) (e : SSet.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) c d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)).toTruncated ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c := by
  constructor
  · intro he
    have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.derived_rightFibration_reflects_invertibleEdge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) e.toTruncated he
    letI : IsIso (Truncated.HomotopyCategory.homMk e.toTruncated) := hi
    exact hd.of_vertexIso (asIso (Truncated.HomotopyCategory.homMk e.toTruncated)).symm
  · intro hc
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated :=
      isIso_of_isTerminal hc.isTerminalHo hd.isTerminalHo _
    exact he.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)

/-- G2 の指定錐から選んだ辺について、極限性の判定をそのまま適用する。 -/
lemma sectionsMap_isInvertible_iff {P Q : 𝒞ᵒᵖ ⥤ Type u} (φ : P ⟶ Q)
    (F : Presheaf 𝒞 E) (cP : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (sectionsOfDiagram P F)) (hcP : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone cP)
    (cQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (sectionsOfDiagram Q F)) (hcQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone cQ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.sectionsMap φ F cP hcP cQ hcQ).toTruncated ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.restrictSectionsCone φ F cQ) := by
  have cast_edge {x x' y : E _⦋0⦌} (h : x = x') (e : SSet.Edge x y) :
      ((Eq.mp (congrArg (fun z => SSet.Edge z y) h) e).toTruncated).edge = e.toTruncated.edge := by
    cases h
    rfl
  have hedge : (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.sectionsMap φ F cP hcP cQ hcQ).toTruncated.edge =
      ((_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.sectionsConeMap φ F cP hcP cQ).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (sectionsOfDiagram P F))).toTruncated.edge := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.sectionsMap, SSet.Edge.toTruncated, id]
    exact cast_edge (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.restrictSectionsCone_vertex φ F cQ)
        ((_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.sectionsConeMap φ F cP hcP cQ).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (sectionsOfDiagram P F)))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hedge).trans
    (coneComparison_isInvertible_iff (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.restrictSectionsCone φ F cQ) cP hcP
      (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.sectionsConeMap φ F cP hcP cQ))

/-- 通常の全錐の添字変更は、nerve・宇宙持ち上げ・F による像と可換。 -/
lemma uliftNerveCone_whisker_val {I D : Type u} [SmallCategory I] [SmallCategory D]
    {G : I ⥤ 𝒞ᵒᵖ} (c : Cone G) (H : D ⥤ I) (F : Presheaf 𝒞 E) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c).ulift).postcomp F)
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap H))).val =
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (c.whisker H)).ulift).postcomp F).val := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap H)) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c).ulift.val ≫ F) = _
  rw [← Category.assoc]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c).ulift)
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap H))).val ≫ F = _
  rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ulift_restrictJoinCone_val]
  change ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso _ 0).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (nerveMap H) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c).val)) ≫ F = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone_whisker]
  rfl

/-- 表現可能標準錐の篩への制限を元の圏の逆同値で引くと S1 の全錐になる。 -/
lemma sieveRestrictCanonicalCone_reindex_val {U : 𝒞} (S : Sieve U) (F : Presheaf 𝒞 E) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone
      (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.restrictSectionsCone S.functorInclusion F (representableSectionsCone U F))
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (sieveCategoryToElements S)))).val =
      (restrictionCone F S).val := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) ((SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (sieveCategoryToElements S))) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.elementsMap S.functorInclusion) ≫
        (representableSectionsCone U F).val) = _
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.elementsMap]
  rw [← Functor.map_comp]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone (representableSectionsCone U F)
    ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (sieveCategoryToElements S ⋙ S.functorInclusion.mapElements)))).val = _
  rw [representableSectionsCone, uliftNerveCone_whisker_val,
    representableElementsCone_sieve]
  rfl

/-- 表現可能側の任意の指定極限錐を制限しても、S1 の指定制限錐と同じ極限性を持つ。 -/
lemma sieveRestrictCone_isLimit_iff {U : 𝒞} (S : Sieve U) (F : Presheaf 𝒞 E)
    (cU : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (sectionsOfDiagram (yoneda.obj U) F)) (hcU : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone cU) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.restrictSectionsCone S.functorInclusion F cU) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (restrictionCone F S) := by
  let c₀ := representableSectionsCone U F
  let i := _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.elementsMap S.functorInclusion
  let e := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict (sectionsOfDiagram (yoneda.obj U) F) i)).toFunctor.mapIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeIso cU c₀ hcU (representableSectionsCone_isLimit U F))
  have hchange : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.restrictSectionsCone S.functorInclusion F cU) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.restrictSectionsCone S.functorInclusion F c₀) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone cU i) rfl).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isLimitCone_iff_of_vertexIso e).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c₀ i) _ rfl))
  let j := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (sieveCategoryToElements S))
  have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence j := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (sieveCategoryToElements S)))
    have he := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveQCatEquivalence
      (sieveElementsEquivalence S).symm).isQCatEquivalence
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveQCatEquivalence,
      CategoryTheory.Equivalence.symm, sieveElementsEquivalence] at he
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsQCatEquivalence.ulift.{u, u + 1} he
  exact hchange.trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLimitCone_iff_restrict_equivalentShape j hj
      (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.restrictSectionsCone S.functorInclusion F c₀)).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ (restrictionCone F S)
          (sieveRestrictCanonicalCone_reindex_val S F)))

/-- S4 で使う篩包含の判定。任意の篩・任意の前層・指定された二つの極限錐。 -/
lemma sieveSectionsMap_isInvertible_iff {U : 𝒞} (S : Sieve U) (F : Presheaf 𝒞 E)
    (cS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (sectionsOfDiagram S.functor F)) (hcS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone cS)
    (cU : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (sectionsOfDiagram (yoneda.obj U) F)) (hcU : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone cU) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.sieveSectionsMap S F cS hcS cU hcU).toTruncated ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (restrictionCone F S) :=
  (sectionsMap_isInvertible_iff S.functorInclusion F cS hcS cU hcU).trans
    (sieveRestrictCone_isLimit_iff S F cU hcU)

/-- 層条件は被覆篩に沿う sectionsOf_map の可逆性と同値。一般の重み射の自然性は不要。 -/
lemma isSheaf_iff_sieveSectionsMap_isInvertible (J : GrothendieckTopology 𝒞)
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) (F : Presheaf 𝒞 E) :
    IsSheaf J F ↔ ∀ (U : 𝒞) (S : Sieve U), S ∈ J U →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (sectionsOf_map S.functorInclusion F
        (sectionsOfDiagram_hasLimit hE S.functor F)
        (sectionsOfDiagram_hasLimit hE (yoneda.obj U) F)).toTruncated := by
  constructor
  · intro hF U S hS
    exact (sieveSectionsMap_isInvertible_iff S F _ (sectionsOfCone_isLimit _ _ _)
      _ (sectionsOfCone_isLimit _ _ _)).mpr (hF U S hS)
  · intro hF U S hS
    exact (sieveSectionsMap_isInvertible_iff S F _ (sectionsOfCone_isLimit _ _ _)
      _ (sectionsOfCone_isLimit _ _ _)).mp (hF U S hS)

end SerrePositivity.InfinityCategories.Sheaves
