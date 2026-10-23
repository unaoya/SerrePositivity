module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitTriangleRawLastLongRestricted

/-!
概要：元の最後辺の指定一点比較の実終点を、同じ raw fiber 輸送の実合成射へ戻す。
方針：元の指定点での全終点を計算し、指定比較の標的表示だけを変更する。
規約：元の指定比較を保持。使われ方：長辺残余の合成消去の同じ中間射。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (b : SSet.Homotopy G J)
local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)
local notation "P" => coherentColimitRawConstantFiberProjection B G
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "s" => lift (𝟙 _) (SSet.const l)
local notation "mb" => Subtype.val (leftUnstraighteningMappingVertexMap _ _
  (coherentVertexOfHomotopy (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b))))

/-- 元の一点比較の実終点は、同じ元の射影後の同じ raw fiber 輸送そのもの。 -/
lemma coherentColimitConstantTransport_raw_point_target :
    s ≫ (P ▷ Δ[0]) ≫ (pointedIntervalTransport A).endpoint =
      P ≫ coherentColimitRawFiberTransport B b := by
  exact pointedIntervalTransportAt_pre A l P

/-- 元の指定一点比較を、同じ raw 輸送を実終点として保持する。 -/
def coherentColimitConstantTransportRawPointIso :
    FunctorIso (mb ≫ coherentColimitRawConstantFiberProjection B J)
      (P ≫ coherentColimitRawFiberTransport B b) :=
  functorIsoOfEq (coherentColimitConstantTransportPointIso B b) rfl
    (coherentColimitConstantTransport_raw_point_target B b)

/-- 同じ実終点への表示変更は、元の指定一点比較の値を保つ。 -/
lemma coherentColimitConstantTransportRawPointIso_heq_point :
    HEq (coherentColimitConstantTransportRawPointIso B b)
      (coherentColimitConstantTransportPointIso B b) :=
  functorIsoOfEq_heq _ _ _

/-- 元の実始域射による前合成も、同じ指定一点比較の値を保つ。 -/
lemma coherentColimitConstantTransportRawPointIso_precomp_heq_point {C : SSet.{u + 1}}
    (r : C ⟶ leftUnstraightening (coherentColimitRawConstantDiagram B G)) :
    HEq ((coherentColimitConstantTransportRawPointIso B b).precomp r)
      ((coherentColimitConstantTransportPointIso B b).precomp r) :=
  functorIso_precomp_heq_of_heq (coherentColimitConstantTransportPointIso B b)
    (coherentColimitConstantTransportRawPointIso B b) rfl
    (coherentColimitConstantTransport_raw_point_target B b)
    (coherentColimitConstantTransportRawPointIso_heq_point B b) r

end SerrePositivity.InfinityCategories.F2
