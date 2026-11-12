module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalOpposite
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.WeakContractibleKan
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialMappingSpace

/-!
概要：一般の単体集合の弱可縮性は反転で保たれ、検出できる。
方針：点への右ホーン因子分解で Kan 置換し、anodyne な射の反転と Kan 可縮性を使う。
規約：元の単体集合に Kan 性を要求しない。
使われ方：slice と反転した coslice の Quillen A の条件の比較。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy

/-- 概要：弱可縮な単体集合の反転も弱可縮。
方針：right anodyne な Kan 置換を左 anodyne に反転して弱可縮性を戻す。
規約：Kan 性は置換後の対象だけに導く。
使われ方：Quillen A の弱い条件を反対側へ移す。 -/
lemma IsWeaklyContractible.op {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible K.op := by
  obtain ⟨M, i, p, _, hi, hp, _⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.exists_rightAnodyne_rightFibration_factorization (terminal.from K)
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p := hp
  have : KanComplex M := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_of_rightHornFillers
    intro n j hj a
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := p) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions.intro j hj)
    have hs : CommSq a (horn (n + 1) j).ι p (terminal.from (Δ[n + 1] : SSet.{u})) :=
      ⟨terminal.hom_ext _ _⟩
    exact ⟨hs.lift, hs.fac_left⟩
  have hiweak := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_rightAnodyne i hi).isWeakHomotopyEquivalence
  have hM := hiweak.weaklyContractible_iff.mp hK
  have hMop : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible M.op := hM.isContractibleKan.op.isWeaklyContractible
  have hiop := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_leftAnodyne _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalLeftAnodyne_op_of_rightAnodyne i hi)).isWeakHomotopyEquivalence
  exact hiop.weaklyContractible_iff.mpr hMop

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible export _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.IsWeaklyContractible (op)


/-- 概要：反転後の弱可縮性から元の弱可縮性が従う。
方針：もう一度反転し、二重反転の同型で移す。
規約：元の単体集合は任意。
使われ方：反対側の Quillen A の条件を元へ戻す。 -/
lemma isWeaklyContractible_of_op {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible K.op) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible K := by
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso (SSet.opFunctorCompOpFunctorIso.app K).hom
  exact hi.isWeakHomotopyEquivalence.weaklyContractible_iff.mp hK.op

/-- 概要：弱可縮性は反転で検出できる。
方針：Kan 置換による保存と二重反転による反映を合わせる。
規約：Kan 性を条件へ加えない。
使われ方：left 側の Quillen A の slice 条件の整形。 -/
lemma isWeaklyContractible_op_iff (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible K.op ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible K :=
  ⟨isWeaklyContractible_of_op, IsWeaklyContractible.op⟩

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
