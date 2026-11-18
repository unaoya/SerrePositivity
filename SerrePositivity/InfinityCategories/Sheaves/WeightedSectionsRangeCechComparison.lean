module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsRangeCechApexIso
public import SerrePositivity.InfinityCategories.HA.Monads.NerveDegeneracyEdges
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeVertex

/-!
概要：像への元の射に沿う重み付き切断の指定辺は可逆。
方針：元の円柱の指定頂点面を使い、辺の類を端点の等号に沿って移す。
  文献対応：HTT 6.2.2.6 と Kerodon Proposition 7.1.6.13（Tag 02XB）。
使われ方：集合値前層の局所同値に沿う切断の可逆性。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open Truncated.HomotopyCategory

open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory
open SerrePositivity.InfinityCategories.HA.Monads

namespace SerrePositivity.InfinityCategories.Sheaves

/-- 像への元の射に沿う重み付き切断の指定辺は可逆。 -/
@[cite HTT "6.2.2.6" (partial := special) "小さい通常の site の集合値 Čech 解消の指定比較。"]
lemma weightedSections_toRangeHom_isInvertible :
∀ {C : Type u} [SmallCategory C] {E : SSet.{u+1}} [Quasicategory E]
  (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q)
  [CategoryTheory.Presheaf.IsLocallyInjective J f]
  (O : Presheaf C E) (hO : IsSheaf J O) (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E),
  let e := (nerve.edgeMk (Subfunctor.toRange f)).map (discretePresheafInclusion C).val
  let r := (edgeOp e.toTruncated).map ((truncation 2).map (weightedSections O hE))
  IsInvertibleEdge r := by
  intro C hC E hQC J P Q f hf O hO hE e r
  let g := Subfunctor.toRange f
  let L := weightedSections O hE
  let A := mapJoinCone L (coconeReverseCone (discretePresheafCocone (relativeCechCocone g)))
  let z := L.app _ (opObjEquiv.symm (functorVertex (discretePresheaf P)))
  let d := constantDiagramCone cechReverseIndex.{u} E z
  obtain ⟨H, ρ, h₀, h₁, hD, hV, he⟩ := weightedSections_toRange_conePrism f O hE
  let hρ := (simplicialHomotopyVertexEdge ρ (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))).toTruncated
  letI : IsIso (homMk hρ) := weightedSections_toRange_conePrism_apex_isInvertible
    J f O hO hE d (cechConstantCone_isLimit E z) H ρ h₀ h₁ hD hV
  have hA : A.vertex = L.app _ (opObjEquiv.symm
      ((discretePresheafInclusion C).val.app _ (nerveVertex ((Subfunctor.range f).toFunctor)))) := by
    dsimp only [A]
    rw [mapJoinCone_vertex, coconeReverseCone_vertex, discretePresheafCocone_vertex,
      (discretePresheafInclusion C).property.1]
    rfl
  have hd : d.vertex = L.app _ (opObjEquiv.symm
      ((discretePresheafInclusion C).val.app _ (nerveVertex P))) := by
    dsimp only [d, z]
    rw [constantDiagramCone_vertex, (discretePresheafInclusion C).property.1]
  have hpoint (x : E _⦋0⦌) :
      (SSet.yonedaEquiv.symm x).app _ (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)) = x :=
    SSet.yonedaEquiv_symm_app_id x
  exact isIso_of_equal_objects_hom_heq
    (congrArg HomotopyCategory.mk ((hpoint A.vertex).trans hA))
    (congrArg HomotopyCategory.mk ((hpoint d.vertex).trans hd))
    (homMk hρ) (homMk r) he

end SerrePositivity.InfinityCategories.Sheaves
