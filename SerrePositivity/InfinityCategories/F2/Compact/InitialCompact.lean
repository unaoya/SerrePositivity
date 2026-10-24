module

public import SerrePositivity.InfinityCategories.F2.Compact.TerminalApexColimit
public import SerrePositivity.InfinityCategories.F2.Compact.FilteredUniverse
public import SerrePositivity.InfinityCategories.F2.Compact.Definition
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.CoconeTransformationPointPost
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpaceTerminalValues
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeInitialBoundaryCriterion

/-!
概要：元の始対象は、任意の小さい無限 κ の κ-filtered 余極限に関して compact。
方針：元の全 Hom の各値の可縮性と、一般 coherent filtered 図式の終対象値の交換を使う。
規約：添字と標的の宇宙を分け、元の指定余錐像の全体の余極限性を証明する。
使われ方：compact 対象の有限余極限閉性の空形状。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の始対象からの全共変 Hom の各値は、同じ空間の頂点として終対象。 -/
lemma covariantRepresentableValue_isTerminal_of_initial {C : SSet.{u}} [Quasicategory C]
    {x : C _⦋0⦌} (hx : IsInitialVertex x) (y : C _⦋0⦌) :
    IsTerminalVertex ((covariantRepresentableInfinity x).app (Opposite.op ⦋0⦌) (ULift.up y)) := by
  apply (HomotopyLimits.spaceInfinity_isTerminal_iff_value_isContractibleKan _).mpr
  exact (covariantRepresentableValueEquivalence x y).isContractibleKan_iff.mpr
    (F1B.kanInitialVertex_pinchedHom_isContractibleKan hx y)

/-- 元の始対象は、添字より大きい標的でも無限 κ に関して κ-compact。 -/
lemma isKappaCompact_of_isInitialVertex {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {C : SSet.{max u v}} [Quasicategory C] {x : C _⦋0⦌} (hx : IsInitialVertex x) :
    IsKappaCompact.{u, v} κ x := by
  intro I hI hFiltered D c _hc
  have : IsFilteredInfinity I := isFilteredInfinity_of_isKappaFiltered hκ I
  have : IsFilteredInfinity ((SSet.uliftFunctor.{v, u}).obj I) := isFilteredInfinity_ulift I
  apply isColimitCone_of_terminal_values
    ((SSet.uliftFunctor.{max u v + 1, max u v}).map D ≫ covariantRepresentableInfinity x)
  · intro i
    exact covariantRepresentableValue_isTerminal_of_initial hx (D.app (Opposite.op ⦋0⦌) i)
  · rw [Ind.mapJoinCocone_vertex, JoinCocone.ulift_vertex]
    exact covariantRepresentableValue_isTerminal_of_initial hx c.vertex

/-- 空形状の余極限頂点は、同じ宇宙の compact 対象。 -/
lemma isCompact_of_isInitialVertex {C : SSet.{u}} [Quasicategory C]
    {x : C _⦋0⦌} (hx : IsInitialVertex x) : IsCompact x :=
  isKappaCompact_of_isInitialVertex le_rfl hx

end SerrePositivity.InfinityCategories.F2.Compact
