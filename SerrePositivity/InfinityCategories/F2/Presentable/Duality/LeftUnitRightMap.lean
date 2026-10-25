module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.LeftUnitContractible
public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.RightUnitLeftMap

/-!
概要：固定左の随伴単位空間の右関手を、元の Pr^R 写像空間へ回収する。
方針：指定単位から随伴を構成し d の保存判定で全部分複体へ持ち上げ、core に移す。
規約：保存条件や同値の存在を追加仮定にしない。
使われ方：元の左ファイバーとの同型の逆方向。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

instance leftAdjointUnitSpace_kanComplex (C D : PresentableInfinityObject.{u})
    (w : PrLFunctorSpace C D _⦋0⦌) : KanComplex (LeftAdjointUnitSpace C D w) :=
  (leftAdjointUnitSpace_isContractibleKan C D w).kanComplex

/-- 概要：固定左の随伴単位空間から元の実単位の coslice への包含。
方針：core と指定単位条件の全部分複体の包含を合成する。
規約：左右の関手と実単位を全次数で保持する。
使われ方：元の随伴対応の右ファイバーへ戻す。 -/
def leftAdjointUnitUnderlying (C D : PresentableInfinityObject.{u})
    (w : PrLFunctorSpace C D _⦋0⦌) : LeftAdjointUnitSpace C D w ⟶ LeftUnitCoslice C D w :=
  (quasicategoryCore (LeftAdjointUnitSubspace C D w)).ι ≫
    (fullSubcomplexOnVertices (LeftUnitCoslice C D w) (fun v ↦
      UnitMappingSpaceCondition (F := leftVertexFunctor w)
      (G := leftUnitRightFunctor v) (leftUnitHom v))).ι

/-- 概要：固定左の随伴単位空間の元の右関手の全族。
方針：元の coslice への包含の後に右関手への射影を続ける。
規約：標的は元の全関手圏。
使われ方：Pr^R の保存条件への持ち上げ。 -/
def leftAdjointUnitRightUnderlying (C D : PresentableInfinityObject.{u})
    (w : PrLFunctorSpace C D _⦋0⦌) :
    LeftAdjointUnitSpace C D w ⟶ (ihom D.obj).obj C.obj :=
  leftAdjointUnitUnderlying C D w ≫ pullback.snd _ ((pre (leftVertexFunctor w)).app C.obj)

/-- 概要：固定左の随伴単位の右関手はaccessibility と全小極限保存を満たす。
方針：同じ指定単位から随伴を構成し、d の随伴関手定理を使う。
規約：元の presentable 性と指定単位条件だけから導く。
使われ方：元の Pr^R 関手圏への持ち上げの頂点条件。 -/
lemma leftAdjointUnitRight_condition {C D : PresentableInfinityObject.{u}}
    {w : PrLFunctorSpace C D _⦋0⦌} (x : LeftAdjointUnitSpace C D w _⦋0⦌) :
    IsAccessibleFunctor (leftUnitRightFunctor x.val.val) ∧
      PreservesSmallLimits (leftUnitRightFunctor x.val.val) := by
  exact (exists_leftAdjoint_iff_accessible_preservesLimits C.isPresentable D.isPresentable _).mp
    ⟨leftVertexFunctor w, ⟨qcatAdjunctionOfUnitMappingSpaceCondition
      (F := leftVertexFunctor w) (G := leftUnitRightFunctor x.val.val)
      (leftUnitHom x.val.val) (fullSubcomplexOnVertices_vertex x.val)⟩⟩

/-- 概要：固定左の随伴単位の右関手を元の Pr^R 関手圏へ持ち上げる。
方針：d から得たaccessibility と全小極限保存によって元の全部分複体へ持ち上げる。
規約：元の全高次の関手自然変換を保持する。
使われ方：元の Pr^R 写像空間への回収。 -/
def leftAdjointUnitRightFunctorMap (C D : PresentableInfinityObject.{u})
    (w : PrLFunctorSpace C D _⦋0⦌) : LeftAdjointUnitSpace C D w ⟶ PrRFunctorSpace D C :=
  fullSubcomplexLift _ (leftAdjointUnitRightUnderlying C D w)
    (fun x ↦ leftAdjointUnitRight_condition x)

/-- 概要：固定左の随伴単位空間の右関手を元の Pr^R 写像空間に回収する。
方針：Kan 始域から元の保存関手圏の core へ持ち上げる。
規約：e1 の元の写像空間を標的とする単体集合の射。
使われ方：元の左ファイバーとの同型の逆射の左成分。 -/
def leftAdjointUnitRight (C D : PresentableInfinityObject.{u})
    (w : PrLFunctorSpace C D _⦋0⦌) : LeftAdjointUnitSpace C D w ⟶ PrRMappingSpace D C :=
  kanCoreMap (leftAdjointUnitRightFunctorMap C D w)

/-- 概要：回収した右関手を全関手圏へ含めると元の右関手の族。
方針：core と全部分複体への持ち上げの包含を順に相殺する。
規約：全次数での射の厳密な等式。
使われ方：元の実単位の coslice の引き戻しを構成する。 -/
lemma leftAdjointUnitRight_ι (C D : PresentableInfinityObject.{u})
    (w : PrLFunctorSpace C D _⦋0⦌) :
    leftAdjointUnitRight C D w ≫ rightMappingInclusion D C =
      leftAdjointUnitRightUnderlying C D w := by
  change kanCoreMap (leftAdjointUnitRightFunctorMap C D w) ≫
    (quasicategoryCore (PrRFunctorSpace D C)).ι ≫
      (fullSubcomplexOnVertices ((ihom D.obj).obj C.obj) _).ι = _
  rw [← Category.assoc, kanCoreMap_ι]
  exact fullSubcomplexLift_ι _ _ _

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
