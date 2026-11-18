module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableFiniteLimitsColimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.ExactFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.EmptyShapeCone
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SquareConePostcomp
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FiniteLimitPreservationGeneration
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.LimitPreservationShapeIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.PointConeSpanIso
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite

/-!
概要：安定な両準圏の完全関手は、元の任意有限形状の指定極限錐を保つ。
方針：零頂点と引き戻しの保存を空形状と点 cospan に移し、既存の有限極限生成を使う。
使われ方：HA Proposition 1.1.4.1、Kerodon §7.1（Tag 02H1）の有限極限。
規約：元の全錐を量化し、終対象と引き戻しの二つの形だけを最終出力にしない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open ZeroObjects
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] [IsStable X] [IsStable Y]

/-- 完全関手は元の標準 cospan の指定極限錐を保つ。 -/
lemma isExactFunctor_map_isLimit_cospan (F : X ⟶ Y) [IsExactFunctor F]
    {p : (horn 2 2 : SSet.{u}) ⟶ X} (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone F c) := by
  have hQ := IsExactFunctor.preservesPullbackSquare F (coneSquare c) (coneSquare_isPullback c hc)
  have h := (isLimitCone_map_pullbackCone_iff F (coneSquare c)).mpr hQ
  have hv : (pullbackCone (coneSquare c)).val = c.val := by
    dsimp only [pullbackCone, coneSquare]
    rw [Iso.hom_inv_id_assoc]
  exact (isLimitCone_iff_of_diagram_eq
    (congrArg (fun f ↦ f ≫ F) (coneSquare_cospan c))
    (congrArg (fun f ↦ f ≫ F) hv)).mp h

/-- 完全関手は元の任意の有限形状の全極限錐を保つ。 -/
theorem isExactFunctor_map_isLimit_finite (F : X ⟶ Y) [IsExactFunctor F]
    {K : SSet.{u}} [K.Finite] {p : K ⟶ X} (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone F c) := by
  letI : HasFiniteLimits X := hasFiniteLimits_of_isStable X
  apply map_isLimit_finite_of_empty_pointCospan F ?_ ?_ c hc
  · intro T q d hd
    have ht := (isLimitCone_iff_terminal_of_initialShape Subcomplex.isInitialBot d).mp hd
    let z := chosenZeroVertex X
    have hz : IsZeroVertex d.vertex := z.isZero.of_vertexIso (terminalVertexIso z.isTerminal ht)
    apply (isLimitCone_iff_terminal_of_initialShape Subcomplex.isInitialBot (mapJoinCone F d)).mpr
    rw [mapJoinCone_vertex]
    exact (IsExactFunctor.preservesZero (F := F) _ hz).2
  · intro q d hd
    let e : (horn 2 2 : SSet.{u}) ≅ pointConeSpan.{u}.op :=
      hornReverseIso 2 0 ≪≫ (SSet.opFunctor.mapIso pointConeSpanIso).symm
    exact map_isLimit_of_shapeIso F e
      (fun _ a ha ↦ isExactFunctor_map_isLimit_cospan F a ha) d hd

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
