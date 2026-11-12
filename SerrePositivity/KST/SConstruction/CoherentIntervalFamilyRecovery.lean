module
public import SerrePositivity.KST.SConstruction.RelativeEquivalenceFamilyRecovery
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightIntervalEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.MappingParameters

/-! # Coherent nerve の固定端点の族の相対回収
概要：固定端点の全区間族を、指定境界を保持する元の豊穣 Hom の族へ戻す。
方針：豊穣 Hom・pinched Hom・区間模型の比較同値に path 置換の相対回収を適用する。
規約：対象と Hom の宇宙を分け、比較円柱の境界定数性まで保持する。
使われ方：元の構造射の高次円柱を豊穣な点つき写像空間へ復号する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の豊穣 Hom から coherent nerve の固定端点の区間模型への比較。 -/
def coherentMappingIntervalComparison (X Y : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _

/-- 局所 Kan 性から、元の固定端点比較そのものが同値。 -/
lemma coherentMappingIntervalComparison_isQCatEquivalence
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)] (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (coherentMappingIntervalComparison X Y) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_isQCatEquivalence X Y).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence _ _)

/-- 元の指定豊穣境界を厳密に保つ、固定端点の全区間族の回収。 -/
def relativeCoherentIntervalFamilyRecovery
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)] (X Y : C)
    {T U : SSet.{max u v}} (j : T ⟶ U) [Mono j]
    (a : T ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y))
    (b : U ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y))
    (h : a ≫ coherentMappingIntervalComparison X Y = j ≫ b) :
    RelativeEquivalenceFamilyData (coherentMappingIntervalComparison X Y) j a b :=
  relativeEquivalenceFamilyRecovery _
    (coherentMappingIntervalComparison_isQCatEquivalence X Y) j a b h

/-- 固定端点の元の円柱を curry して相対回収する。元の円柱は比較先に残す。 -/
def relativeCoherentCylinderFamilyRecovery
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)] (X Y : C)
    {T U : SSet.{max u v}} (j : T ⟶ U) [Mono j]
    (a : T ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y))
    (H : (Δ[1] : SSet.{max u v}) ⊗ U ⟶ SimplicialNerve C)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 U ≫ H = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X))
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 U ≫ H = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y))
    (h : a ≫ coherentMappingIntervalComparison X Y = j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyCurry H h₀ h₁) :
    RelativeEquivalenceFamilyData (coherentMappingIntervalComparison X Y) j a
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyCurry H h₀ h₁) :=
  relativeCoherentIntervalFamilyRecovery X Y j a _ h

end SerrePositivity.KST.SConstruction
