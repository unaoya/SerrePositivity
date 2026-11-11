module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeCellMappingKan
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiniteTotalFibers
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.FibrationDerivedFiberSpan

/-!
概要：指定底上の実乗法的写像模型を、同じ基点の strict fiber と導来 fiber へ比較する。
方針：零単体の実底射を定値射と照合し、既存の頂点 fiber の pullback と path 比較を使う。
規約：同じ q と s を保持し、代数の ∞ 局所化の相対写像空間との比較は別工程とする。
使われ方：全射 q に対する指定底の実 AW 写像模型の相対性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open SSet.modelCategoryQuillen
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

section Fiber
variable {A X B : Mon (Complex R)} (q : X ⟶ B) (s : A ⟶ B)

lemma multiplicativeMappingBase_eq_const :
    multiplicativeMappingBase R s = SSet.const (multiplicativeMappingBasePoint R s) := by
  rw [← SSet.yonedaEquiv_symm_zero]
  exact (SSet.yonedaEquiv.symm_apply_apply (multiplicativeMappingBase R s)).symm

lemma relativeMultiplicativeMapping_vertexFiber_isPullback :
    IsPullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (multiplicativeMappingPostcompose R A q) (multiplicativeMappingBasePoint R s))
      (stdSimplex.isTerminalObj₀.from _)
      (multiplicativeMappingPostcompose R A q) (multiplicativeMappingBase R s) := by
  rw [multiplicativeMappingBase_eq_const]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiber_isPullback _ _

def relativeMultiplicativeMappingFiberIso :
    relativeMultiplicativeMappingSimplices R q s ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (multiplicativeMappingPostcompose R A q) (multiplicativeMappingBasePoint R s) :=
  (relativeMultiplicativeMapping_vertexFiber_isPullback R q s).isoPullback.symm

lemma relativeMultiplicativeMappingFiberIso_projection :
    (relativeMultiplicativeMappingFiberIso R q s).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (multiplicativeMappingPostcompose R A q) (multiplicativeMappingBasePoint R s) =
        relativeMultiplicativeMappingProjection R q s :=
  (relativeMultiplicativeMapping_vertexFiber_isPullback R q s).isoPullback_inv_fst

end Fiber

section Derived
variable (A : Mon (Complex R)) {X B : Mon (Complex R)} (q : X ⟶ B)
  (hq : EInfinity.projectiveFibrations R q.hom) (s : cellResolution R A ⟶ B)

def relativeMultiplicativeCellMappingDerivedFiberMap :
    relativeMultiplicativeMappingSimplices R q s ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (multiplicativeMappingPostcompose R (cellResolution R A) q)
        (multiplicativeMappingBasePoint R s) := by
  have := multiplicativeCellMapping_fibration R A q hq
  exact (relativeMultiplicativeMappingFiberIso R q s).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.fibrationStrictDerivedFiberEquivalence
      (multiplicativeMappingPostcompose R (cellResolution R A) q)
      (multiplicativeMappingBasePoint R s)).hom

lemma relativeMultiplicativeCellMappingDerivedFiberMap_isQCatEquivalence :
    let := multiplicativeCellMapping_fibration R A q hq
    let := relativeMultiplicativeCellMapping_kanComplex R A q hq s
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (relativeMultiplicativeCellMappingDerivedFiberMap R A q hq s) := by
  have := multiplicativeCellMapping_fibration R A q hq
  have := relativeMultiplicativeCellMapping_kanComplex R A q hq s
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (relativeMultiplicativeMappingFiberIso R q s)).isQCatEquivalence.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.fibrationStrictDerivedFiberEquivalence
      (multiplicativeMappingPostcompose R (cellResolution R A) q)
      (multiplicativeMappingBasePoint R s)).isQCatEquivalence

end Derived
end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
