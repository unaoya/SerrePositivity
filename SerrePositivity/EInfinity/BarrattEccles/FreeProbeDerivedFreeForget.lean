module

public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeUnitLocalTransport
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeDerivedLimits

/-!
概要：既存 CAlg_R と D(R) の間の実自由忘却 ∞ 随伴と U の coherent 極限保存。
方針：P-6 を代入して証明した局所輸送条件で、構成済みの全経路を閉じる。
規約：任意可換環 A のみを入力とし、局所同定・F・大域単位を仮定しない。
使われ方：g2 の完成した自由忘却界面と、既存 CAlg_R 版 G1′ の極限保存入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HomotopyLimits
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma derivedFreeProbeUnitCommaVertex_isInitial
    (x : (derivedInfinityCategory A) _⦋0⦌) :
    IsInitialVertex (derivedFreeProbeUnitCommaVertex A x) :=
  derivedFreeProbeUnitCommaVertex_isInitial_of_transportIso A x
    (freeProbeUnitTransportCondition A x)

lemma cAlgForgetDerived_rightAdjoint_exists :
    ∃ F : derivedInfinityCategory A ⟶ CAlg_R A,
      Nonempty (QCatAdjunction F (cAlgForgetDerived A)) :=
  cAlgForgetDerived_rightAdjoint_exists_of_transport A (freeProbeUnitTransportCondition A)

def cAlgFreeDerived : derivedInfinityCategory A ⟶ CAlg_R A :=
  cAlgFreeDerivedOfTransport A (freeProbeUnitTransportCondition A)

def cAlgFreeForgetDerivedAdjunction :
    QCatAdjunction (cAlgFreeDerived A) (cAlgForgetDerived A) :=
  cAlgFreeForgetDerivedAdjunctionOfTransport A (freeProbeUnitTransportCondition A)

def derivedFreeProbeUnitCommaAdjunctionIso
    (x : (derivedInfinityCategory A) _⦋0⦌) :
    VertexIso (X := unitCommaFiber (cAlgForgetDerived A) x)
      (derivedFreeProbeUnitCommaVertex A x)
      (unitCommaSectionVertex (cAlgFreeForgetDerivedAdjunction A).unitHom x) :=
  derivedFreeProbeUnitCommaAdjunctionIsoOfTransport A (freeProbeUnitTransportCondition A) x

lemma cAlgForgetDerived_mapJoinCone_isLimit
    {K : SSet.{u + 1}} {p : K ⟶ CAlg_R A} (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone (cAlgForgetDerived A) c) :=
  cAlgForgetDerived_mapJoinCone_isLimit_of_transport A (freeProbeUnitTransportCondition A) c hc

lemma cAlgForgetDerived_hasLimit_postcomp
    {K : SSet.{u + 1}} (p : K ⟶ CAlg_R A) (hp : HasLimit p) :
    HasLimit (p ≫ cAlgForgetDerived A) :=
  cAlgForgetDerived_hasLimit_postcomp_of_transport A (freeProbeUnitTransportCondition A) p hp

end SerrePositivity.EInfinity.BarrattEccles
