module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.RightUnitContractible

/-!
概要：固定右の随伴単位空間の左関手を、元の Pr^L 写像空間へ回収する。
方針：指定単位から随伴を構成し d の保存判定で全部分複体へ持ち上げ、core に移す。
規約：保存条件や同値の存在を追加仮定にしない。
使われ方：元の右ファイバーとの同型の逆方向。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：Kan 始域からの射を標的の core へ持ち上げる。
方針：始域の core の厳密同型と core 上の写像を合成する。
規約：標的の充填性は要求しない。
使われ方：随伴単位空間から元の関手圏の core への射。 -/
def kanCoreMap {A X : SSet.{u}} [KanComplex A] (f : A ⟶ X) :
    A ⟶ (quasicategoryCore X : SSet.{u}) :=
  (quasicategoryCoreIsoOfKan A).inv ≫ quasicategoryCoreMap f

/-- 概要：Kan 始域から core への持ち上げの包含は元の射。
方針：core 上の写像の包含との自然性と同型の逆則を使う。
規約：全単体を厳密に保持する。
使われ方：持ち上げた左関手と元の実単位の照合。 -/
lemma kanCoreMap_ι {A X : SSet.{u}} [KanComplex A] (f : A ⟶ X) :
    kanCoreMap f ≫ (quasicategoryCore X).ι = f := by
  unfold kanCoreMap
  rw [Category.assoc, quasicategoryCoreMap_ι, ← Category.assoc]
  change ((quasicategoryCoreIsoOfKan A).inv ≫ (quasicategoryCoreIsoOfKan A).hom) ≫ f = f
  rw [Iso.inv_hom_id, Category.id_comp]

instance rightAdjointUnitSpace_kanComplex (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) : KanComplex (RightAdjointUnitSpace C D w) :=
  (rightAdjointUnitSpace_isContractibleKan C D w).kanComplex

/-- 概要：固定右の随伴単位空間から元の実単位の coslice への包含。
方針：core と指定単位条件の全部分複体の包含を合成する。
規約：左右の関手と実単位を全次数で保持する。
使われ方：元の随伴対応の右ファイバーへ戻す。 -/
def rightAdjointUnitUnderlying (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) : RightAdjointUnitSpace C D w ⟶ RightUnitCoslice C D w :=
  (quasicategoryCore (RightAdjointUnitSubspace C D w)).ι ≫
    (fullSubcomplexOnVertices (RightUnitCoslice C D w) (fun v ↦
      UnitMappingSpaceCondition (F := rightUnitLeftFunctor v)
        (G := rightVertexFunctor w) (rightUnitHom v))).ι

/-- 概要：固定右の随伴単位空間の元の左関手の全族。
方針：元の coslice への包含の後に左関手への射影を続ける。
規約：標的は元の全関手圏。
使われ方：Pr^L の保存条件への持ち上げ。 -/
def rightAdjointUnitLeftUnderlying (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) :
    RightAdjointUnitSpace C D w ⟶ (ihom C.obj).obj D.obj :=
  rightAdjointUnitUnderlying C D w ≫ pullback.snd _ ((ihom C.obj).map (rightVertexFunctor w))

/-- 概要：固定右の随伴単位の左関手は全小余極限を保つ。
方針：同じ指定単位から随伴を構成し、d の随伴関手定理を使う。
規約：元の presentable 性と指定単位条件だけから導く。
使われ方：元の Pr^L 関手圏への持ち上げの頂点条件。 -/
lemma rightAdjointUnitLeft_preservesSmallColimits {C D : PresentableInfinityObject.{u}}
    {w : PrRFunctorSpace D C _⦋0⦌} (x : RightAdjointUnitSpace C D w _⦋0⦌) :
    PreservesSmallColimits (rightUnitLeftFunctor x.val.val) := by
  exact (exists_rightAdjoint_iff_preservesSmallColimits C.isPresentable D.isPresentable _).mp
    ⟨rightVertexFunctor w, ⟨qcatAdjunctionOfUnitMappingSpaceCondition
      (rightUnitHom x.val.val) (fullSubcomplexOnVertices_vertex x.val)⟩⟩

/-- 概要：固定右の随伴単位の左関手を元の Pr^L 関手圏へ持ち上げる。
方針：d から得た全小余極限保存によって元の全部分複体へ持ち上げる。
規約：元の全高次の関手自然変換を保持する。
使われ方：元の Pr^L 写像空間への回収。 -/
def rightAdjointUnitLeftFunctorMap (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) : RightAdjointUnitSpace C D w ⟶ PrLFunctorSpace C D :=
  fullSubcomplexLift _ (rightAdjointUnitLeftUnderlying C D w)
    (fun x ↦ rightAdjointUnitLeft_preservesSmallColimits x)

/-- 概要：固定右の随伴単位空間の左関手を元の Pr^L 写像空間に回収する。
方針：Kan 始域から元の保存関手圏の core へ持ち上げる。
規約：e1 の元の写像空間を標的とする単体集合の射。
使われ方：元の右ファイバーとの同型の逆射の左成分。 -/
def rightAdjointUnitLeft (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) : RightAdjointUnitSpace C D w ⟶ PrLMappingSpace C D :=
  kanCoreMap (rightAdjointUnitLeftFunctorMap C D w)

/-- 概要：回収した左関手を全関手圏へ含めると元の左関手の族。
方針：core と全部分複体への持ち上げの包含を順に相殺する。
規約：全次数での射の厳密な等式。
使われ方：元の実単位の coslice の引き戻しを構成する。 -/
lemma rightAdjointUnitLeft_ι (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) :
    rightAdjointUnitLeft C D w ≫ leftMappingInclusion C D =
      rightAdjointUnitLeftUnderlying C D w := by
  change kanCoreMap (rightAdjointUnitLeftFunctorMap C D w) ≫
    (quasicategoryCore (PrLFunctorSpace C D)).ι ≫
      (fullSubcomplexOnVertices ((ihom C.obj).obj D.obj) _).ι = _
  rw [← Category.assoc, kanCoreMap_ι]
  exact fullSubcomplexLift_ι _ _ _

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
