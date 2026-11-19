module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsDiscreteFactorization
public import SerrePositivity.InfinityCategories.Sheaves.DiscreteSectionsSpecifiedMap
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsOriginalSpecifiedMap

/-!
概要：集合値の重みに対する重み付き切断の写像は、要素圏上の切断の写像と両立する。
方針：同じ指定極限を二つの比較に使い、比較同型を消去する。
  文献対応：HTT 5.1.5.6（双対）。
使われ方：離散前層の重み付き切断の自然性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

namespace SerrePositivity.InfinityCategories.Sheaves

/-- 集合値の重みに対する重み付き切断の写像は、要素圏上の切断の写像と両立する。 -/
@[cite HTT "5.1.5.6" (partial := special) "小さい通常の site の集合値重みの指定比較。"]
lemma weightedSections_discrete_map :
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ (O : Presheaf C E) (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) {P Q : Cᵒᵖ ⥤ Type u}
  (φ : P ⟶ Q) (hP : HasLimit (sectionsOfDiagram P O))
  (hQ : HasLimit (sectionsOfDiagram Q O)),
  let e := (nerve.edgeMk φ).map (discretePresheafInclusion C).val
  let r := (edgeOp e.toTruncated).map ((truncation 2).map (weightedSections O hE))
  Truncated.HomotopyCategory.homMk r ≫ (weightedSections_discrete O hE P hP).hom =
    (weightedSections_discrete O hE Q hQ).hom ≫
      Truncated.HomotopyCategory.homMk (sectionsOf_map φ O hP hQ).toTruncated := by
  intro C hC E hQC O hE P Q φ hP hQ e r
  let U := SSet.uliftFunctor.{u + 1, u}
  let a := U.map (smallUnstraighteningFunctorHom (discretePresheafHom φ))
  let DP := U.map (smallLeftUnstraighteningProjection (discretePresheaf P)) ≫ O
  let DQ := U.map (smallLeftUnstraighteningProjection (discretePresheaf Q)) ≫ O
  have h : a ≫ DQ = DP := by
    dsimp only [a, DP, DQ]
    rw [← Category.assoc, ← Functor.map_comp, smallUnstraighteningFunctorHom_projection]
  obtain ⟨dP, hdP⟩ := hE.hasLimit DP
  obtain ⟨dQ, hdQ⟩ := hE.hasLimit DQ
  let rQ := (restrictJoinCone dQ a).cast h
  obtain ⟨k₀⟩ := IsTerminalVertex.nonempty_edge (X := sliceOver DP) hdP rQ
  let k := SSet.Edge.ofTruncated (X := sliceOver DP) k₀
  let f : (PresheafCat C SpaceInfinity.{u}) _⦋0⦌ → E _⦋0⦌ :=
    fun v => (weightedSections O hE).app _ (opObjEquiv.symm v)
  let cP := eqToHom (congrArg HomotopyCategory.mk
    (congrArg f ((discretePresheafInclusion C).property.1 P)))
  let cQ := eqToHom (congrArg HomotopyCategory.mk
    (congrArg f ((discretePresheafInclusion C).property.1 Q)))
  let iP := (weightedSections_originalLeftLimitIso O hE (discretePresheaf P) dP hdP).hom
  let iQ := (weightedSections_originalLeftLimitIso O hE (discretePresheaf Q) dQ hdQ).hom
  let zP := cP ≫ iP
  let zQ := cQ ≫ iQ
  let eP := (weightedSections_discrete O hE P hP).hom
  let eQ := (weightedSections_discrete O hE Q hQ).hom
  let d₀ := (discreteSectionsLeftComparison O Q hQ dQ hdQ).hom
  let d₁ := (discreteSectionsLeftComparison O P hP dP hdP).hom
  let m := Truncated.HomotopyCategory.homMk (sectionsOf_map φ O hP hQ).toTruncated
  let k' := eqToHom (congrArg HomotopyCategory.mk
    ((JoinCone.vertex_cast _ h).trans (restrictJoinCone_vertex dQ a)).symm) ≫
    Truncated.HomotopyCategory.homMk (k.map (sliceOverProjection DP)).toTruncated
  have hP₀ : eP ≫ d₁ = zP := weightedSections_discrete_hom_fac O hE P hP dP hdP
  have hQ₀ : eQ ≫ d₀ = zQ := weightedSections_discrete_hom_fac O hE Q hQ dQ hdQ
  have hS : d₀ ≫ k' = m ≫ d₁ :=
    discreteSectionsLeftComparison_specifiedMap O hE φ h dP dQ hdP hdQ k hP hQ
  let R := Truncated.HomotopyCategory.homMk r
  have hW₀ : R ≫ cP ≫ iP = cQ ≫ iQ ≫ k' :=
    weightedSections_originalLeftLimitIso_specifiedMap O hE φ h dP dQ hdP hdQ k
  have hW : R ≫ zP = zQ ≫ k' := hW₀.trans (Category.assoc cQ iQ k').symm
  letI : IsIso d₁ := inferInstanceAs
    (IsIso (discreteSectionsLeftComparison O P hP dP hdP).hom)
  apply (cancel_mono d₁).mp
  change (R ≫ eP) ≫ d₁ = (eQ ≫ m) ≫ d₁
  rw [Category.assoc, hP₀, hW, ← hQ₀, Category.assoc, hS, Category.assoc]

end SerrePositivity.InfinityCategories.Sheaves
