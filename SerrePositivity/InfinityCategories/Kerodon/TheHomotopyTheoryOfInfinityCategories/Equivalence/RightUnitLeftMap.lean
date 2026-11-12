module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.RightUnitContractible

/-!
概要：固定右の随伴単位空間の左関手を、元の Pr^L 写像空間へ回収する。
方針：指定単位から随伴を構成し d の保存判定で全部分複体へ持ち上げ、core に移す。
規約：保存条件や同値の存在を追加仮定にしない。
使われ方：元の右ファイバーとの同型の逆方向。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：Kan 始域からの射を標的の core へ持ち上げる。
方針：始域の core の厳密同型と core 上の写像を合成する。
規約：標的の充填性は要求しない。
使われ方：随伴単位空間から元の関手圏の core への射。 -/
def kanCoreMap {A X : SSet.{u}} [KanComplex A] (f : A ⟶ X) :
    A ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X : SSet.{u}) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreIsoOfKan A).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap f

/-- 概要：Kan 始域から core への持ち上げの包含は元の射。
方針：core 上の写像の包含との自然性と同型の逆則を使う。
規約：全単体を厳密に保持する。
使われ方：持ち上げた左関手と元の実単位の照合。 -/
lemma kanCoreMap_ι {A X : SSet.{u}} [KanComplex A] (f : A ⟶ X) :
    kanCoreMap f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).ι = f := by
  unfold kanCoreMap
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι, ← Category.assoc]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreIsoOfKan A).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreIsoOfKan A).hom) ≫ f = f
  rw [Iso.inv_hom_id, Category.id_comp]

instance rightAdjointUnitSpace_kanComplex (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) : KanComplex (_root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.RightAdjointUnitSpace C D w) :=
  (_root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.rightAdjointUnitSpace_isContractibleKan C D w).kanComplex

/-- 概要：固定右の随伴単位空間から元の実単位の coslice への包含。
方針：core と指定単位条件の全部分複体の包含を合成する。
規約：左右の関手と実単位を全次数で保持する。
使われ方：元の随伴対応の右ファイバーへ戻す。 -/
def rightAdjointUnitUnderlying (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.RightAdjointUnitSpace C D w ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RightUnitCoslice C D w :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.RightAdjointUnitSubspace C D w)).ι ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RightUnitCoslice C D w) (fun v ↦
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition (F := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightUnitLeftFunctor v)
        (G := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightUnitHom v))).ι

/-- 概要：固定右の随伴単位空間の元の左関手の全族。
方針：元の coslice への包含の後に左関手への射影を続ける。
規約：標的は元の全関手圏。
使われ方：Pr^L の保存条件への持ち上げ。 -/
def rightAdjointUnitLeftUnderlying (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.RightAdjointUnitSpace C D w ⟶ (ihom C.obj).obj D.obj :=
  rightAdjointUnitUnderlying C D w ≫ pullback.snd _ ((ihom C.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w))

/-- 概要：固定右の随伴単位の左関手は全小余極限を保つ。
方針：同じ指定単位から随伴を構成し、d の随伴関手定理を使う。
規約：元の presentable 性と指定単位条件だけから導く。
使われ方：元の Pr^L 関手圏への持ち上げの頂点条件。 -/
lemma rightAdjointUnitLeft_preservesSmallColimits {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    {w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌} (x : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.RightAdjointUnitSpace C D w _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightUnitLeftFunctor x.val.val) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits C.isPresentable D.isPresentable _).mp
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatAdjunctionOfUnitMappingSpaceCondition
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightUnitHom x.val.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x.val)⟩⟩

/-- 概要：固定右の随伴単位の左関手を元の Pr^L 関手圏へ持ち上げる。
方針：d から得た全小余極限保存によって元の全部分複体へ持ち上げる。
規約：元の全高次の関手自然変換を保持する。
使われ方：元の Pr^L 写像空間への回収。 -/
def rightAdjointUnitLeftFunctorMap (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.RightAdjointUnitSpace C D w ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (rightAdjointUnitLeftUnderlying C D w)
    (fun x ↦ rightAdjointUnitLeft_preservesSmallColimits x)

/-- 概要：固定右の随伴単位空間の左関手を元の Pr^L 写像空間に回収する。
方針：Kan 始域から元の保存関手圏の core へ持ち上げる。
規約：e1 の元の写像空間を標的とする単体集合の射。
使われ方：元の右ファイバーとの同型の逆射の左成分。 -/
def rightAdjointUnitLeft (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.RightAdjointUnitSpace C D w ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLMappingSpace C D :=
  kanCoreMap (rightAdjointUnitLeftFunctorMap C D w)

/-- 概要：回収した左関手を全関手圏へ含めると元の左関手の族。
方針：core と全部分複体への持ち上げの包含を順に相殺する。
規約：全次数での射の厳密な等式。
使われ方：元の実単位の coslice の引き戻しを構成する。 -/
lemma rightAdjointUnitLeft_ι (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) :
    rightAdjointUnitLeft C D w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftMappingInclusion C D =
      rightAdjointUnitLeftUnderlying C D w := by
  change kanCoreMap (rightAdjointUnitLeftFunctorMap C D w) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D)).ι ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom C.obj).obj D.obj) _).ι = _
  rw [← Category.assoc, kanCoreMap_ι]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
