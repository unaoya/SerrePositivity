module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.InitialTerminalPreservation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.ExactFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LeftAdjointAllColimitPreservation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.AdjunctionLimits
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SquareConePostcomp

/-!
概要：安定な準圏の間の随伴の両関手は、零頂点と cofiber/fiber 列を保つ。
方針：始終対象と零対象の一意比較、同じ随伴による元の全錐の保存を使う。
使われ方：HA §1.1.4、HTT 5.2.3.5、Kerodon §6.2（Tag 02EH）の随伴の保存則。
規約：左関手の極限保存を一般には主張しない。安定な両圏で完全性を導く。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open ZeroObjects

/-- 点付きの標的への左随伴は、始対象の一意比較によって零頂点を保つ。 -/
lemma adjunction_left_preservesZeroVertices {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [HasZeroVertex Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) : PreservesZeroVertices F := by
  intro x hx
  let z := chosenZeroVertex Y
  exact z.isZero.of_vertexIso (initialVertexIso z.isInitial (a.left_preservesInitialVertex x hx.1))

/-- 点付きの標的への右随伴は、終対象の一意比較によって零頂点を保つ。 -/
lemma adjunction_right_preservesZeroVertices {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [HasZeroVertex X]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) : PreservesZeroVertices G := by
  intro y hy
  let z := chosenZeroVertex X
  exact z.isZero.of_vertexIso (terminalVertexIso z.isTerminal (a.right_preservesTerminalVertex y hy.2))

/-- 安定な両準圏の間の左随伴は、元の cofiber 列を保つ完全関手である。 -/
theorem isExactFunctor_leftAdjoint {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [IsStable X] [IsStable Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) : IsExactFunctor F where
  preservesZero := adjunction_left_preservesZeroVertices a
  preservesCofiber t ht :=
    (isColimitCone_post_pushoutCocone_iff F t.square).mp
      (mapJoinCocone_isColimit_of_adjunction a (pushoutCocone t.square) ht)

/-- 安定な両準圏の間の右随伴は、元の fiber 列を保つことから完全である。 -/
theorem isExactFunctor_rightAdjoint {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [IsStable X] [IsStable Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) : IsExactFunctor G := by
  apply isExactFunctor_of_preservesFiber G (adjunction_right_preservesZeroVertices a)
  intro t ht
  exact (isLimitCone_map_pullbackCone_iff G t.square).mp
    (mapJoinCone_isLimit_of_adjunction a (pullbackCone t.square) ht)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
