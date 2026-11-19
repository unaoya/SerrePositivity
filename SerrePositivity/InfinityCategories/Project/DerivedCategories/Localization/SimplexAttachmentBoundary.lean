module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SimplexTerminalCoconeExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.InnerAnodyneEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionLifting

/-!
概要：有限単体とその終端からの次辺を、共有点を保持する実部分図式として貼る。
方針：終点包含の像と空部分複体の pushout-join を用い、inner anodyne 性を証明する。
規約：零次を含む全次数、二つの元の包含、共有点の厳密等号を保持する。
使われ方：c5 の有限線型図式とその全比較を一段延長する工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet MorphismProperty
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 元の最後の点包含の像。 -/
def simplexLastVertex (n : ℕ) : (Δ[n] : SSet.{u}).Subcomplex :=
  Subfunctor.range (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)

/-- 最後の点はその像と同型。 -/
def simplexLastPointRangeIso (n : ℕ) :
    (Δ[0] : SSet.{u}) ≅ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexLastVertex n : SSet.{u}) := by
  have := Subfunctor.instIsIsoFunctorTypeToRangeOfMono (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint.{u} n)
  exact asIso (Subfunctor.toRange (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n))

@[reassoc]
lemma simplexLastPointRangeIso_hom_ι (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexLastPointRangeIso n).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexLastVertex n).ι =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint.{u} n := rfl

/-- 元の終点の像の包含も right anodyne。 -/
lemma simplexLastVertex_rightAnodyne (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexLastVertex.{u} n).ι := by
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.terminalPoint_rightAnodyne (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.stdSimplex_last_isTerminalVertex.{u} n)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.arrow_mk_iso_iff
    (Arrow.isoMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexLastPointRangeIso n) (Iso.refl _) (by rfl))).mp ht

/-- 前段の全単体と、その終点から新頂点への元の次辺の和。 -/
def simplexAttachmentBoundary (n : ℕ) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0]).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexLastVertex n) (⊥ : (Δ[0] : SSet.{u}).Subcomplex)

/-- 前段の全単体の元の包含。 -/
def simplexAttachmentPrefix (n : ℕ) :
    (Δ[n] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n : SSet.{u}) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.joinEmptyIso Δ[n] Δ[0]).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexLastVertex n) (⊥ : (Δ[0] : SSet.{u}).Subcomplex)

/-- 元の次辺の包含。始域は二点の join として固定する。 -/
def simplexAttachmentLastEdge (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[0] ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexLastPointRangeIso n).hom (𝟙 Δ[0]) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexLastVertex n) (⊥ : (Δ[0] : SSet.{u}).Subcomplex)

@[reassoc]
lemma simplexAttachmentPrefix_ι (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentPrefix n ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n).ι =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0] := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentPrefix _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.joinEmptyIso_inv,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]

@[reassoc]
lemma simplexAttachmentLastEdge_ι (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentLastEdge n ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n).ι =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint.{u} n) (𝟙 Δ[0]) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentLastEdge _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft_ι, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexLastPointRangeIso_hom_ι, Category.id_comp]

/-- 二つの元の包含は、指定された同じ終点を厳密に共有する。 -/
lemma simplexAttachmentBoundary_comm (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentLastEdge n =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentPrefix n := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n).ι).mp
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentLastEdge_ι, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentPrefix_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap]

/-- 前段と次辺の和は、元の共有点に沿う実 pushout。 -/
lemma simplexAttachmentBoundary_isPushout (n : ℕ) :
    IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0]) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentLastEdge n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentPrefix n) := by
  let R := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexLastVertex.{u} n
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexLastPointRangeIso.{u} n
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_isPushout R (⊥ : (Δ[0] : SSet.{u}).Subcomplex)).of_iso'
    (e ≪≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.joinEmptyIso R Δ[0]).symm) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso e (Iso.refl Δ[0]))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.joinEmptyIso Δ[n] Δ[0]).symm (Iso.refl _)
  · simp only [Iso.trans_hom, Iso.symm_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.joinEmptyIso_inv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso,
      Iso.refl_hom]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]
  · simp only [Iso.trans_hom, Iso.symm_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.joinEmptyIso_inv]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexLastPointRangeIso_hom_ι]
  · rfl
  · rfl

/-- この実部分図式から一段長い全単体への包含は inner anodyne。 -/
lemma simplexAttachmentBoundary_innerAnodyne (n : ℕ) :
    innerAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary.{u} n).ι :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_innerAnodyne_of_rightAnodyne _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexLastVertex_rightAnodyne n)

/-- 全比較の制限は、両端と任意の指定部分族を保持する自明 Kan ファイブレーション。 -/
instance simplexAttachmentRestriction_trivialKanFibration (n : ℕ)
    (X : SSet.{u}) [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n).ι).app X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary_innerAnodyne n) X

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
