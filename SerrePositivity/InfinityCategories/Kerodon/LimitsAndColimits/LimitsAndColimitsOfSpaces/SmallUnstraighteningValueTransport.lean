module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SmallKanUnstraighteningUnitValue
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.UnstraighteningValueTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Transport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationTransportNaturality

/-!
概要：元の小さい unstraightening の指定 fiber 値比較は、同じ辺の作用に全自然。
方針：既存の大きい輸送の比較へ持ち上げ、指定順射の持ち上げ公式で元の宇宙へ戻す。
規約：小さい値比較の選択を保つ。使われ方：G8 の宇宙変更と表現可能値の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open IsomorphismsAndIsofibrations Equivalence
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
open SerrePositivity.InfinityCategories.Project.FilteredExchange

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：小さい射影から元の大きい射影への指定 fiber 同型は、同じ辺の輸送に自然。
方針：輸送の宇宙持ち上げと全空間の底上の同型の自然性を合成する。
規約：選んだ輸送を変更しない。使われ方：指定 fiber 値比較の自然性。 -/
def smallLeftUnstraighteningFiberIso_transportIso {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    {a b : B _⦋0⦌} (e : B.Edge a b) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (edgeTransport (smallLeftUnstraighteningProjection F) e) ≫
        (smallLeftUnstraighteningFiberIso F b).hom)
      ((smallLeftUnstraighteningFiberIso F a).hom ≫
        edgeTransport (leftUnstraighteningProjection F) (uliftTruncatedEdge.{u, u + 1} e)) := by
  let p := smallLeftUnstraighteningProjection F
  let q := leftUnstraighteningProjection F
  let J := fun c : B _⦋0⦌ => uliftVertexFiberIso.{u, u + 1} p c
  let K := fun c : B _⦋0⦌ => vertexFiberTotalIso
    ((SSet.uliftFunctor.{u + 1, u}).map p) q (smallLeftUnstraighteningIso F)
      (smallLeftUnstraighteningIso_projection F) (ULift.up c)
  have hu := FunctorIso.precomp (edgeTransport_uliftIso.{u, u + 1} p e).symm (J a).hom
  have hm := leftFibrationMap_transportIso ((SSet.uliftFunctor.{u + 1, u}).map p) q
    (smallLeftUnstraighteningIso F).hom (smallLeftUnstraighteningIso_projection F)
      (SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, u + 1} e))
  have hu' : FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (edgeTransport p e) ≫ (J b).hom)
      ((J a).hom ≫ edgeTransport ((SSet.uliftFunctor.{u + 1, u}).map p)
        (uliftTruncatedEdge.{u, u + 1} e)) := by
    simpa only [J, uliftFiberTransport, Category.assoc, Iso.hom_inv_id_assoc] using hu
  have hm' := FunctorIso.precomp hm (J a).hom
  simpa only [smallLeftUnstraighteningFiberIso, J, K, p, q, vertexFiberTotalIso,
    Iso.trans_hom, Category.assoc, SSet.Edge.ofTruncated, FunctorIso] using
    (FunctorIso.postcomp hu' (K b).hom) ≪≫ hm'

/-- 概要：元の小さい fiber 値比較は、同じ図式の指定辺の値の作用に全自然。
方針：指定順射の持ち上げ公式、大きい値比較の自然性、全関手同型の下降を使う。
規約：同じ小さい値比較の実射を使う。使われ方：G8 の後段の自然性。 -/
def smallUnstraighteningValueTransportIso {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    {a b : B _⦋0⦌} (e : B.Edge a b) :
    FunctorIso
      (edgeTransport (smallLeftUnstraighteningProjection F) e ≫
        (smallLeftUnstraighteningFiberValueEquivalence F b).hom)
      ((smallLeftUnstraighteningFiberValueEquivalence F a).hom ≫
        spaceInfinityEdgeValue ((SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, u + 1} e)).map F)) := by
  have h := FunctorIso.postcomp (smallLeftUnstraighteningFiberIso_transportIso F e)
    (leftUnstraighteningFiberValueEquivalence F (ULift.up b)).hom
  have k := FunctorIso.precomp
    (unstraighteningValueTransportIso F
      (SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, u + 1} e)))
    (smallLeftUnstraighteningFiberIso F a).hom
  simp only [Category.assoc] at h k
  have he := h ≪≫ k
  apply FunctorIso.downOfKan.{u, u + 1}
  simpa only [Functor.map_comp, smallLeftUnstraighteningFiberValueEquivalence_hom_lift,
    Category.assoc, FunctorIso] using he

/-- 概要：同じ底上の射の fiber と元の小さい値比較の合成は、指定辺の作用に全自然。
方針：底上の射の輸送の自然性と小さい値比較の自然性を合成する。
規約：比較射に同値性を仮定しない。使われ方：G8 の宇宙変更と表現可能値の共通部品。 -/
def smallUnstraighteningFiberMapValue_transportIso {E B : SSet.{u}}
    (p : E ⟶ B) [LeftAndRightFibrations.LeftFibration p]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (r : E ⟶ smallLeftUnstraightening F) (hr : r ≫ smallLeftUnstraighteningProjection F = p)
    {a b : B _⦋0⦌} (e : B.Edge a b) :
    FunctorIso
      (edgeTransport p e ≫ vertexFiberMap p (smallLeftUnstraighteningProjection F) r hr b ≫
        (smallLeftUnstraighteningFiberValueEquivalence F b).hom)
      (vertexFiberMap p (smallLeftUnstraighteningProjection F) r hr a ≫
        (smallLeftUnstraighteningFiberValueEquivalence F a).hom ≫
          spaceInfinityEdgeValue ((SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, u + 1} e)).map F)) := by
  have h := FunctorIso.postcomp
    (leftFibrationMap_transportIso p (smallLeftUnstraighteningProjection F) r hr e)
    (smallLeftUnstraighteningFiberValueEquivalence F b).hom
  have k := FunctorIso.precomp (smallUnstraighteningValueTransportIso F e)
    (vertexFiberMap p (smallLeftUnstraighteningProjection F) r hr a)
  simp only [Category.assoc] at h k
  exact h ≪≫ k

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
