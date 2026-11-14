module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.QCatEquivalenceOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OppositeInvolution
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.BoundaryPrismOpposite
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.OppositeInternalHom
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：前合成同値・同値の右持ち上げ・充満忠実な inner 射の反転による保存。
方針：内部 Hom の反転同型と全境界の反転で指定された比較と持ち上げを移す。
規約：新しい宣言は F1B 名前空間に置く。
使われ方：元の相対左 Kan 制限定理を右側へ厳密に移す。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 概要：任意の標的への前合成の同値は添字の反転で保たれる。
方針：内部 Hom の反転同型で前合成を挟み、標的の二重反転を消す。
規約：元の二つの添字に quasicategory 性は不要。
使われ方：右持ち上げ条件の試験射を反転する。 -/
lemma isPrecompositionEquivalence_op {A B : SSet.{u}} {f : A ⟶ B}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (SSet.opFunctor.map f) := by
  have aux (X : SSet.{u}) [Quasicategory X] :
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((pre (SSet.opFunctor.map f)).app X.op) := by
    have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_op (hf X)).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso A X)).isQCatEquivalence
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHom_pre] at h
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso B X)).isQCatEquivalence.cancel_left h
  have transport (Y Z : SSet.{u}) [Quasicategory Y] [Quasicategory Z] (h : Y = Z) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((pre (SSet.opFunctor.map f)).app Y) →
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((pre (SSet.opFunctor.map f)).app Z) := by
    subst Z
    exact fun h ↦ h
  intro X _
  exact transport X.op.op X (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.opposite_opposite_eq X) (aux X.op)

/-- 概要：単射な前合成同値の右持ち上げ条件は標的の射の反転で保たれる。
方針：試験射を反転して持ち上げ、反転関手の圏同値で二重反転を消す。
規約：U の両端に quasicategory 性を要求しない。
使われ方：相対右 Kan の厳密な構成へ isofibration の入力を渡す。 -/
@[kerodon 01EV]
lemma EquivalenceLifting.op {D E : SSet.{u}} {U : D ⟶ E}
    (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (SSet.opFunctor.map U) := by
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  intro A B i hm hi
  have : Mono i := hm
  have h := hU (SSet.opFunctor.map i) inferInstance (isPrecompositionEquivalence_op hi)
  have ho := (SSet.opFunctor.hasLiftingProperty_iff_of_isEquivalence
    (SSet.opFunctor.map i) U).mpr h
  change HasLiftingProperty ((SSet.opFunctor ⋙ SSet.opFunctor).map i) (SSet.opFunctor.map U) at ho
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.oppositeFunctor_square] at ho
  exact ho

/-- 概要：充満忠実な inner 射は反転後も充満忠実。
方針：正次元の全境界充填を反転し、各始点からの指定 pinched 比較を判定する。
規約：頂点全射性や単射性を追加しない。
使われ方：全部分圏包含に沿う右 Kan 制限の仮定を反転後へ渡す。 -/
lemma isFullyFaithful_op {D E : SSet.{u}} [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) [InnerFibration U] (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful U) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (SSet.opFunctor.map U) := by
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  intro x y
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pinchedHomMap_equivalence_of_initialBoundary (SSet.opFunctor.map U) x y
  intro n a b _ sq
  have h := hU.hasLiftingProperty_boundary_succ n
  have ho := (SSet.opFunctor.hasLiftingProperty_iff_of_isEquivalence
    (boundary (n + 1)).ι U).mpr h
  let e : Arrow.mk (boundary (n + 1)).ι ≅
      Arrow.mk (SSet.opFunctor.map (boundary (n + 1)).ι) :=
    Arrow.isoMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.boundaryReverseIso (n + 1)) (stdSimplex.opIso ⦋n + 1⦌).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.boundaryReverseIso_hom_ι (n + 1))
  have := (HasLiftingProperty.iff_of_arrow_iso_left e (SSet.opFunctor.map U)).mpr ho
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
