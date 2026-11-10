module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.LeftUnitInitialCriterion
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.RightUnitContractible

/-!
概要：固定した元の左関手に対する随伴実単位の全空間の可縮性。
方針：指定単位条件を coslice の始対象性と同定し、始対象の全部分複体で境界を充填する。
規約：全関手圏の core における高次単体を保持する。
使われ方：元の左射影のファイバーと比較する可縮な単位空間。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：固定した元の左関手に対する随伴実単位の全部分複体。
方針：全関手圏の coslice の頂点に、同じ実単位の随伴条件を課す。
規約：右関手の保存条件は追加仮定にしない。
使われ方：元の左射影のファイバーの比較先。 -/
def LeftAdjointUnitSubspace (C D : PresentableInfinityObject.{u})
    (w : PrLFunctorSpace C D _⦋0⦌) : SSet.{u + 1} :=
  (fullSubcomplexOnVertices (LeftUnitCoslice C D w) (fun v ↦
    UnitMappingSpaceCondition (F := leftVertexFunctor w)
      (G := leftUnitRightFunctor v) (leftUnitHom v)) : SSet.{u + 1})

/-- 概要：固定した元の左関手に対する随伴実単位の全部分複体は可縮。
方針：指定単位条件と始対象性の同値で頂点条件を置き換え、全境界を充填する。
規約：元の全関手圏の高次単体を保つ可縮性。
使われ方：随伴単位の選択に関する高次の一意性。 -/
lemma leftAdjointUnitSubspace_isContractibleKan (C D : PresentableInfinityObject.{u})
    (w : PrLFunctorSpace C D _⦋0⦌) : IsContractibleKan (LeftAdjointUnitSubspace C D w) := by
  have hP : (fun v : LeftUnitCoslice C D w _⦋0⦌ ↦
      UnitMappingSpaceCondition (F := leftVertexFunctor w)
      (G := leftUnitRightFunctor v) (leftUnitHom v)) = IsInitialVertex :=
    funext (fun v ↦ propext (leftUnit_condition_iff_isInitial v))
  unfold LeftAdjointUnitSubspace
  rw [hP]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.initialVertices_isContractibleKan (leftUnitCoslice_hasInitial C D w)

instance leftAdjointUnitSubspace_kanComplex (C D : PresentableInfinityObject.{u})
    (w : PrLFunctorSpace C D _⦋0⦌) : KanComplex (LeftAdjointUnitSubspace C D w) :=
  (leftAdjointUnitSubspace_isContractibleKan C D w).kanComplex

/-- 概要：固定した元の左関手に対する随伴実単位の Kan 空間。
方針：同じ随伴単位の全部分複体の core を取る。
規約：元の実単位の core であり、随伴の証拠の離散集合ではない。
使われ方：両関手の写像空間の左射影の固定ファイバーとの比較。 -/
def LeftAdjointUnitSpace (C D : PresentableInfinityObject.{u})
    (w : PrLFunctorSpace C D _⦋0⦌) : SSet.{u + 1} :=
  quasicategoryCore (LeftAdjointUnitSubspace C D w)

/-- 概要：元の左関手を固定した随伴単位の core は可縮。
方針：全部分複体の Kan 性による core の厳密同型で可縮性を移す。
規約：モデル構造や同値の存在の追加仮定は使わない。
使われ方：元の左射影の高次ファイバーの可縮性を検証する比較先。 -/
lemma leftAdjointUnitSpace_isContractibleKan (C D : PresentableInfinityObject.{u})
    (w : PrLFunctorSpace C D _⦋0⦌) : IsContractibleKan (LeftAdjointUnitSpace C D w) :=
  isContractibleKan_of_iso (quasicategoryCoreIsoOfKan _).symm
    (leftAdjointUnitSubspace_isContractibleKan C D w)

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
