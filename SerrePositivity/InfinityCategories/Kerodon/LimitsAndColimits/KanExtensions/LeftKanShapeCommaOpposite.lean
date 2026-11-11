module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanShapeCommaEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.QCatEquivalenceOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenASliceOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaFiber

/-!
概要：左 Kan の局所添字と oriented comma の fiber の比較を反転から構成する。
方針：slice の反転同型、coslice の比較、comma の fiber の反転同型を合成する。
規約：比較射の定義に充填性は不要。同値性には K と C の quasicategory 性を使う。
使われ方：任意の関手に沿う点ごとの余極限から Kan 拡張を作るための添字の変更。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：左 Kan の局所添字の反転は反転した関手の右 Kan の局所添字と同型。
方針：slice の反転後、引き戻しの二因子を交換する。
規約：頂点も opObjEquiv で反転する。
使われ方：coslice の比較を左側へ移す始域の同型。 -/
def kanLeftKanShapeOpIso {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c).op ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape (SSet.opFunctor.map δ) (SSet.opObjEquiv.symm c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalSlicePullbackOpIso δ c ≪≫ pullbackSymmetry _ _

/-- 概要：反転を通じた左 Kan の局所添字から oriented comma の fiber への比較。
方針：二重反転を戻す同型と、反転した右側の比較、fiber の同型を合成する。
規約：元の slice の余錐から直接作る比較との等式は主張しない。
使われ方：局所添字と cocartesian な置き換えの fiber の同値。 -/
def kanLeftKanShapeToCommaFiberViaOpposite {K C : SSet.{u}}
    (δ : K ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) c :=
  (SSet.opFunctorCompOpFunctorIso.app (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c)).inv ≫
    SSet.opFunctor.map (kanLeftKanShapeOpIso δ c).hom ≫
      SSet.opFunctor.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightKanShapeToUnitCommaFiber (SSet.opFunctor.map δ) (SSet.opObjEquiv.symm c)) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaFiberIso δ c).hom

/-- 概要：反転を通じた局所添字の比較は前合成同値。
方針：右側の比較の quasicategory 同値を反転し、両端の厳密な同型と合成する。
規約：K と C は quasicategory、δ に fibration 性は不要。
使われ方：comma の fiber の余極限を元の局所 Kan 添字へ移す。 -/
lemma kanLeftKanShapeToCommaFiberViaOpposite_isPrecompositionEquivalence
    {K C : SSet.{u}} [Quasicategory K] [Quasicategory C]
    (δ : K ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (kanLeftKanShapeToCommaFiberViaOpposite δ c) := by
  let G := SSet.opFunctor.map δ
  let x := SSet.opObjEquiv.symm c
  have : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape G x) :=
    quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection G x)
  have : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) :=
    quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_op
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightKanShapeToUnitCommaFiber_isPrecompositionEquivalence G x).isQCatEquivalence
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (SSet.opFunctorCompOpFunctorIso.app (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c)).symm).comp
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
        (SSet.opFunctor.mapIso (kanLeftKanShapeOpIso δ c))).comp
          (h.isPrecompositionEquivalence.comp
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaFiberIso δ c))))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
