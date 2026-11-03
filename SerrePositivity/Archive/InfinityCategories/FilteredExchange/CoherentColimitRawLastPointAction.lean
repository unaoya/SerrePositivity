module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTransportRawPoint

/-!
概要：元の最後辺の指定一点比較を第一作用で前合成し、実二合成射を両端として保持する。
方針：元の指定比較の前合成後に、三射の結合だけを明示的に戻す。
規約：比較の値は再選択しない。使われ方：元の長辺残余の厳密な消去式の中間因子。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  (a : SSet.Homotopy F G) (b : SSet.Homotopy G J)
local notation "ma" => Subtype.val (leftUnstraighteningMappingVertexMap _ _
  (coherentVertexOfHomotopy (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B a))))
local notation "mb" => Subtype.val (leftUnstraighteningMappingVertexMap _ _
  (coherentVertexOfHomotopy (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b))))
local notation "PG" => coherentColimitRawConstantFiberProjection B G
local notation "PJ" => coherentColimitRawConstantFiberProjection B J

/-- 同じ第一作用と元の最後辺の指定比較を、実二合成を両端として保持する。 -/
def coherentColimitRawLastPointActionIso :
    FunctorIso ((ma ≫ mb) ≫ PJ) ((ma ≫ PG) ≫ coherentColimitRawFiberTransport B b) :=
  functorIsoOfEq ((coherentColimitConstantTransportRawPointIso B b).precomp ma)
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm

/-- 実両端への結合変更を除くと、元の指定 raw 一点比較の同じ前合成である。 -/
lemma coherentColimitRawLastPointActionIso_heq_point :
    HEq (coherentColimitRawLastPointActionIso B a b)
      ((coherentColimitConstantTransportPointIso B b).precomp ma) :=
  (functorIsoOfEq_heq _ _ _).trans
    (coherentColimitConstantTransportRawPointIso_precomp_heq_point B b ma)

end SerrePositivity.InfinityCategories.F2
