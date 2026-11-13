module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.ExactFunctor
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.AdjunctionOpposite
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.QCatEquivalenceAdjunction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IntervalMappingContractible
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.AdjunctionLimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceAllLimits

/-!
概要：安定 ∞ 圏の間の左随伴は零対象と cofiber 列を保つ。
方針：始対象性を随伴の写像空間比較で移し、押し出しを反対圏の引き戻しに移す。
使われ方：安定な層圏への反射の完全性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

private def oppositeAdjunction {C E : SSet.{u}} [Quasicategory C] [Quasicategory E]
    {L : C ⟶ E} {R : E ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (opFunctor.map R) (opFunctor.map L) := by
  let c : C.op.op ≅ C := opFunctorCompOpFunctorIso.app C
  let e : E.op.op ≅ E := opFunctorCompOpFunctorIso.app E
  have b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction ((c.hom ≫ L) ≫ e.inv) (e.hom ≫ R ≫ c.inv) :=
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso c).toAdjunction.comp a).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e.symm).toAdjunction
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.qcatAdjunctionOfOpposite
  have hL : opFunctor.map (opFunctor.map L) = (c.hom ≫ L) ≫ e.inv := by ext n x; rfl
  have hR : opFunctor.map (opFunctor.map R) = e.hom ≫ R ≫ c.inv := by ext n x; rfl
  rwa [hL, hR]

/-- 安定な値域で、左随伴による始対象と押し出しの保存は完全性を与える。 -/
lemma isExactFunctor_of_adjunction {C E : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    [Quasicategory E] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable E] {L : C ⟶ E} {R : E ⟶ C}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor L where
  preservesZero x hx := by
    have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (L.app _ x) := by
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_of_intervalMappingSpace_isContractibleKan
      intro y
      exact (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitMappingSpaceCondition_iff_interval a.unitHom).mp
        a.unitMappingSpaceCondition x y).isContractibleKan_iff).mpr
        (hx.1.intervalMappingSpace_isContractibleKan _)
    let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex E
    exact ⟨hi, z.isTerminal.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.initialVertexIso z.isInitial hi)⟩
  preservesCofiber t ht := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (t.square ≫ L)
    rw [_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPushoutSquare_iff_reverseGrid, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid_postcomp]
    let s := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid t.square
    have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare s := (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPushoutSquare_iff_reverseGrid t.square).mp ht
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.mapJoinCone_isLimit_of_adjunction
      (oppositeAdjunction a) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone s) hs
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_of_diagram_eq
      (Category.assoc _ _ _) (Category.assoc _ _ _)).mp h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
