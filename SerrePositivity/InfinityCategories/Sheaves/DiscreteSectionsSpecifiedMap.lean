module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.DiscreteSectionsLeftComparison
public import SerrePositivity.InfinityCategories.Sheaves.DiscreteElementsComparisonSpecifiedHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitComparisonRestrictionSquare
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SectionsMapConeProjection

/-!
概要：同じ指定切断の比較で、離散重みの射の作用を計算する。
方針：R06.1 の底上の相対同型を持ち上げ、指定された錐の制限四角形に適用する。
  文献対応：HTT 5.1.5.6（双対）、Kerodon §7.1（Tag 02H1）。
使われ方：全重み付き切断の指定値と要素圏切断の照合。
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
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Sheaves

/-- 重みの指定射を、同じ要素圏の切断と同じ指定極限の比較で計算する。 -/
@[cite HTT "5.1.5.6" (partial := special) "小さい通常の site の集合値重みに対する指定比較。"]
lemma discreteSectionsLeftComparison_specifiedMap :
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ (O : Presheaf C E) (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E),
∀ {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q),
let U := SSet.uliftFunctor.{u + 1, u}
let a := U.map (smallUnstraighteningFunctorHom (discretePresheafHom φ))
let DP := U.map (smallLeftUnstraighteningProjection (discretePresheaf P)) ≫ O
let DQ := U.map (smallLeftUnstraighteningProjection (discretePresheaf Q)) ≫ O
∀ (h : a ≫ DQ = DP) (dP : JoinCone DP) (dQ : JoinCone DQ)
 (hdP : IsLimitCone dP) (hdQ : IsLimitCone dQ),
let rQ := (restrictJoinCone dQ a).cast h
∀ (k : SSet.Edge (X := sliceOver DP) rQ dP),
let k₀ := eqToHom (congrArg HomotopyCategory.mk
 ((JoinCone.vertex_cast _ h).trans (restrictJoinCone_vertex dQ a)).symm) ≫
 Truncated.HomotopyCategory.homMk (k.map (sliceOverProjection DP)).toTruncated
∀ (hP : HasLimit (sectionsOfDiagram P O)) (hQ : HasLimit (sectionsOfDiagram Q O)),
 (discreteSectionsLeftComparison O Q hQ dQ hdQ).hom ≫ k₀ =
 Truncated.HomotopyCategory.homMk (sectionsOf_map φ O hP hQ).toTruncated ≫
 (discreteSectionsLeftComparison O P hP dP hdP).hom := by
  intro C hC E hq O hE P Q φ U a DP DQ h dP dQ hdP hdQ rQ k k₀ hP hQ
  let p := SetWeight.projection P
  let q := smallLeftUnstraighteningProjection (discretePresheaf Q)
  let p' := smallLeftUnstraighteningProjection (discretePresheaf P)
  let f := U.map (SetWeight.elementsComparisonNatural P)
  let g := U.map (SetWeight.elementsComparisonNatural Q)
  let b := SetWeight.elementsMap φ
  have hb : b ≫ U.map (SetWeight.projection Q) = U.map p := by
    change U.map (nerveMap φ.mapElements) ≫ U.map (SetWeight.projection Q) = _
    rw [← Functor.map_comp]
    exact congrArg U.map (congrArg nerveMap (NatTrans.mapElements_comp_π φ))
  have ha : a ≫ U.map q = U.map p' := by
    change U.map (smallUnstraighteningFunctorHom (discretePresheafHom φ)) ≫ U.map q = _
    rw [← Functor.map_comp]
    exact congrArg U.map (smallUnstraighteningFunctorHom_projection (discretePresheafHom φ))
  have hf : f ≫ U.map p' = U.map p := by
    change U.map (SetWeight.elementsComparisonNatural P) ≫ U.map p' = _
    rw [← Functor.map_comp]
    exact congrArg U.map (SetWeight.elementsComparisonNatural_projection P)
  have hg : g ≫ U.map q = U.map (SetWeight.projection Q) := by
    change U.map (SetWeight.elementsComparisonNatural Q) ≫ U.map q = _
    rw [← Functor.map_comp]
    exact congrArg U.map (SetWeight.elementsComparisonNatural_projection Q)
  have ef : IsQCatEquivalence f := IsQCatEquivalence.ulift.{u, u + 1}
    (SetWeight.elementsComparisonNatural_isPrecompositionEquivalence P).isQCatEquivalence
  have eg : IsQCatEquivalence g := IsQCatEquivalence.ulift.{u, u + 1}
    (SetWeight.elementsComparisonNatural_isPrecompositionEquivalence Q).isQCatEquivalence
  obtain ⟨hl, hr, ⟨i⟩⟩ := discreteElementsComparison_specifiedHom φ
  let M := uliftRelativeFunctorMap.{u, u + 1} q p
  let f₀ := SetWeight.elementsComparisonNatural P ≫
    smallUnstraighteningFunctorHom (discretePresheafHom φ)
  let g₀ := nerveMap φ.mapElements ≫ SetWeight.elementsComparisonNatural Q
  have hl' : f₀ ≫ q = p := hl
  have hr' : g₀ ≫ q = p := hr
  have e₀ : M.app _ (ULift.up (relativeFunctorVertex q p f₀ hl')) =
      relativeFunctorVertex (U.map q) (U.map p) (f ≫ a)
        (by rw [Category.assoc, ha, hf]) := by
    rw [uliftRelativeFunctorMap_vertex]
    apply Subtype.ext
    exact congrArg functorVertex (U.map_comp _ _)
  have e₁ : M.app _ (ULift.up (relativeFunctorVertex q p g₀ hr')) =
      relativeFunctorVertex (U.map q) (U.map p) (b ≫ g)
        (by rw [Category.assoc, hg, hb]) := by
    rw [uliftRelativeFunctorMap_vertex]
    apply Subtype.ext
    exact congrArg functorVertex (U.map_comp _ _)
  let j := (eqToIso (congrArg HomotopyCategory.mk e₀)).symm ≪≫
    (uliftVertexIso.{u, u + 1} i).map M ≪≫ eqToIso (congrArg HomotopyCategory.mk e₁)
  let cP := sectionsOfCone P O hP
  let cQ := sectionsOfCone Q O hQ
  let hcP := sectionsOfCone_isLimit P O hP
  let hcQ := sectionsOfCone_isLimit Q O hQ
  let s := Truncated.HomotopyCategory.homMk (SetWeight.sectionsConeMap φ O cP hcP cQ).toTruncated
  have h₀ := limitVertexIso_restrictionSquare (U.map p) (U.map (SetWeight.projection Q))
    (U.map p') (U.map q) b a f g hb ha hf hg ef eg j.symm O cP cQ dP dQ
      hcP hcQ hdP hdQ s (Truncated.HomotopyCategory.homMk k.toTruncated)
  change (discreteSectionsLeftComparison O Q hQ dQ hdQ).hom ≫ k₀ =
    Truncated.HomotopyCategory.homMk (SetWeight.sectionsMap φ O cP hcP cQ hcQ).toTruncated ≫
      (discreteSectionsLeftComparison O P hP dP hdP).hom
  rw [SetWeight.sectionsMap_hom_eq_projection]
  exact h₀

end SerrePositivity.InfinityCategories.Sheaves
