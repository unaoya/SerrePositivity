module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratedSource
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.IteratedSliceUnderIso
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseJoinSimplexShapes
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitExistenceTransfer

/-!
概要：固定した元の始域の全 coslice は、元の圏の小余完備性を受け継ぐ。
方針：一点と小さい図式の join を小宇宙で作り、反復 coslice の同型で余極限を戻す。
規約：飽和射の部分圏の余完備性・accessibility はこの補題だけでは主張しない。
使われ方：P-1 f2b、固定始域の presentable 性に向けた余極限の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {C : SSet.{u + 1}} [Quasicategory C]

/-- 全 coslice の図式は、その展開した元の図式と余極限の存在が同値。 -/
lemma sourceCoslice_hasColimit_iff {K L : SSet.{u + 1}} {p : K ⟶ C}
    (D : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit D ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry D) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderIso D)
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨e.hom.app _ c, e.map_isInitialVertex hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨e.inv.app _ c, e.symm.map_isInitialVertex hc⟩

/-- 任意の元の小さい固定図式の全 coslice も、小余完備性を受け継ぐ。 -/
lemma smallDiagramCoslice_hasSmallColimits (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    {K : SSet.{u}} (p : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) := by
  intro L D
  apply (sourceCoslice_hasColimit_iff D).mpr
  let U := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry D
  let j := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso.{u, u + 1} K L).hom
  have hj : IsIso j := inferInstance
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict U j) :=
    ⟨MorphismProperty.rlp_of_isIso _ _⟩
  let := hr
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_iff_of_trivialRestriction U j).mpr (hC (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L) (j ≫ U))

/-- 元の圏が全小余極限を持てば、各元の始域の全 coslice も全小余極限を持つ。 -/
lemma sourceCoslice_hasSmallColimits (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x)) := by
  intro K D
  apply (sourceCoslice_hasColimit_iff D).mpr
  let U := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry D
  let j := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso.{u, u + 1} K 0).hom
  have hj : IsIso j := inferInstance
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict U j) :=
    ⟨MorphismProperty.rlp_of_isIso _ _⟩
  let := hr
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_iff_of_trivialRestriction U j).mpr
    (hC (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K) (j ≫ U))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
