module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.JoinCells
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalMap
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaces
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SpaceSmallLimits
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.EmptyShapeConeCriterion
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorVertexConeReindex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialShapeLimitExistence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SimplexConeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SpaceTerminal
public import SerrePositivity.InfinityCategories.HTT.InitialAndFinalObjects.InitialBoundaryTransport

/-!
概要：有限セル帰納で必要な元の小さい形状の空間値極限の存在を明示する。
方針：空形状の slice 同型、始点での延長、形状同型による制限を使う。
規約：交換の仮定に部分極限の存在を隠さない。使われ方：存在と交換の同時帰納。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 元の小さい形状の全ての coherent な空間値図式が極限を持つ条件。 -/
def HasSpaceLimitsOfShape (K : SSet.{u}) : Prop :=
  ∀ p : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p

/-- 任意の小さい形状の空間値極限は、全切断による無条件の存在定理から得られる。 -/
lemma hasSpaceLimitsOfShape (K : SSet.{u}) : HasSpaceLimitsOfShape K :=
  fun p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.hasLimit_coherentSpaceDiagram p

/-- 元の形状の同型は空間値の極限の存在を移す。 -/
lemma hasSpaceLimitsOfShape_of_iso {K L : SSet.{u}} (e : K ≅ L)
    (hK : HasSpaceLimitsOfShape K) : HasSpaceLimitsOfShape L := by
  intro p
  let f := (SSet.uliftFunctor.{u + 1, u}).map e.hom
  let g := (SSet.uliftFunctor.{u + 1, u}).map e.inv
  have : IsIso g := by dsimp only [g]; infer_instance
  obtain ⟨c, hc⟩ := hK (f ≫ p)
  have hd := (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isLimitCone_restrict_iff_of_isIso c g).mpr hc
  have he : g ≫ (f ≫ p) = p := by
    dsimp only [f, g]
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, e.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c g).cast he, hd.cast he⟩

/-- 任意の空形状上の空間値図式は、元の slice の一点空間から極限を持つ。 -/
lemma hasSpaceLimitsOfShape_of_empty {K : SSet.{u}} (hK : ¬ K.Nonempty) :
    HasSpaceLimitsOfShape K := by
  intro p
  have hL : ¬ ((SSet.uliftFunctor.{u + 1, u}).obj K).Nonempty := by
    rintro ⟨x⟩
    exact hK ⟨x.down⟩
  have := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.emptyShapeSliceProjection_isIso hL p
  exact ⟨(inv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)).app (Opposite.op ⦋0⦌) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.pointSpaceVertex_isTerminalVertex.map_of_isIso (inv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p))⟩

/-- 有限セル帰納の空部分複体は、全ての元の空間値図式に極限を持つ。 -/
lemma hasSpaceLimitsOfShape_empty (X : SSet.{u}) :
    HasSpaceLimitsOfShape (⊥ : X.Subcomplex) := by
  apply hasSpaceLimitsOfShape_of_empty
  rintro ⟨x⟩
  exact x.property

/-- 全標準単体の元の coherent 空間値図式は極限を持つ。 -/
lemma hasSpaceLimitsOfShape_simplex (n : ℕ) :
    HasSpaceLimitsOfShape (Δ[n] : SSet.{u}) := by
  intro p
  let f : (Δ[0] : SSet.{u + 1}) ⟶ Δ[n] :=
    SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
  have : Mono f := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.stdSimplex_firstVertex_mono n
  let a := f ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} n).inv
  have : Mono a := by dsimp only [a]; infer_instance
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions a :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.comp_mem f _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.stdSimplex_firstVertex_leftAnodyne n)
      (MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions _)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasLimit_of_initialShape a ha p

end SerrePositivity.InfinityCategories.Project.FilteredExchange
