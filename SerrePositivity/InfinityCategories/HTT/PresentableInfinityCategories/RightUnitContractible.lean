module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialVerticesContractible

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.RightUnitInitialCriterion
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：固定した元の右関手に対する随伴実単位の全空間の可縮性。
方針：指定単位条件を coslice の始対象性と同定し、始対象の全部分複体で境界を充填する。
規約：全関手圏の core における高次単体を保持する。
使われ方：元の右射影のファイバーと比較する可縮な単位空間。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
open _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.InfinityCategories.F2 _root_.SerrePositivity.InfinityCategories.F2.Presentable _root_.SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：固定した元の右関手に対する随伴実単位の全部分複体。
方針：全関手圏の coslice の頂点に、同じ実単位の随伴条件を課す。
規約：左関手の保存条件は追加仮定にしない。
使われ方：元の右射影のファイバーの比較先。 -/
def RightAdjointUnitSubspace (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) : SSet.{u + 1} :=
  (fullSubcomplexOnVertices (RightUnitCoslice C D w) (fun v ↦
    UnitMappingSpaceCondition (F := rightUnitLeftFunctor v)
      (G := rightVertexFunctor w) (rightUnitHom v)) : SSet.{u + 1})

/-- 概要：固定した元の右関手に対する随伴実単位の全部分複体は可縮。
方針：指定単位条件と始対象性の同値で頂点条件を置き換え、全境界を充填する。
規約：元の全関手圏の高次単体を保つ可縮性。
使われ方：随伴単位の選択に関する高次の一意性。 -/
lemma rightAdjointUnitSubspace_isContractibleKan (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) : IsContractibleKan (RightAdjointUnitSubspace C D w) := by
  have hP : (fun v : RightUnitCoslice C D w _⦋0⦌ ↦
      UnitMappingSpaceCondition (F := rightUnitLeftFunctor v)
        (G := rightVertexFunctor w) (rightUnitHom v)) = IsInitialVertex :=
    funext (fun v ↦ propext (rightUnit_condition_iff_isInitial v))
  unfold RightAdjointUnitSubspace
  rw [hP]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.initialVertices_isContractibleKan (rightUnitCoslice_hasInitial C D w)

instance rightAdjointUnitSubspace_kanComplex (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) : KanComplex (RightAdjointUnitSubspace C D w) :=
  (rightAdjointUnitSubspace_isContractibleKan C D w).kanComplex

/-- 概要：固定した元の右関手に対する随伴実単位の Kan 空間。
方針：同じ随伴単位の全部分複体の core を取る。
規約：元の実単位の core であり、随伴の証拠の離散集合ではない。
使われ方：両関手の写像空間の右射影の固定ファイバーとの比較。 -/
def RightAdjointUnitSpace (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) : SSet.{u + 1} :=
  quasicategoryCore (RightAdjointUnitSubspace C D w)

/-- 概要：元の右関手を固定した随伴単位の core は可縮。
方針：全部分複体の Kan 性による core の厳密同型で可縮性を移す。
規約：モデル構造や同値の存在の追加仮定は使わない。
使われ方：元の右射影の高次ファイバーの可縮性を検証する比較先。 -/
lemma rightAdjointUnitSpace_isContractibleKan (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) : IsContractibleKan (RightAdjointUnitSpace C D w) :=
  isContractibleKan_of_iso (quasicategoryCoreIsoOfKan _).symm
    (rightAdjointUnitSubspace_isContractibleKan C D w)

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
