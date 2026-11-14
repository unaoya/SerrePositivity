module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCoreSliceCones
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FiniteConeOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredWeakContractibility
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenALeft
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceIdentityTerminal
public import SerrePositivity.KST.Fibration.WeakHomotopyAnodyneComparison

/-!
概要：元の Verdier 商の core 逆像射影は left cofinal で、anodyne 局所化で可逆。
方針：元の各 slice の有限錐から反対圏の filtered 性・弱可縮性を証明し、Quillen A を使う。
規約：元の商射影の全 slice を扱い、完成の充満忠実性や有限境界充填を仮定しない。
使われ方：c5 の零次標準単体比較への元の対象側の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.LocalizingInvariants

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}

/-- 元の core 逆像射影の各 slice は、全有限図式に実錐を持つ。 -/
lemma verdierCoreQuotient_isLeftCofinal (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).fromPreimage q.hom) := by
  let W := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).preimage q.hom : SSet.{u})
  let Q := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).fromPreimage q.hom
  let : Quasicategory W := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.corePreimage_quasicategory q.hom
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_weaklyContractible_slices Q
  intro c
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c)
  let T := pullback Q r
  have hcones : ∀ {K : SSet.{u}} [K.Finite] (a : K ⟶ T), Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone a) := by
    intro K _ a
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierCorePullback_finiteCone h r (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceIdentityCone_isTerminalVertex c) a
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity T.op := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_op_of_finiteCones T hcones
  exact _root_.SerrePositivity.InfinityCategories.HTT.Section5_1_4.isWeaklyContractible_of_op (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_of_isFilteredInfinity T.op)

lemma verdierCoreQuotient_isWeakHomotopyEquivalence (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).fromPreimage q.hom) :=
  (verdierCoreQuotient_isLeftCofinal h).isWeakHomotopyEquivalence

lemma verdierCoreQuotient_localized_isIso (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).fromPreimage q.hom)) :=
  weakHomotopyEquivalence_anodyneQ_isIso _ (verdierCoreQuotient_isWeakHomotopyEquivalence h)

end SerrePositivity.KST.LocalizingInvariants
