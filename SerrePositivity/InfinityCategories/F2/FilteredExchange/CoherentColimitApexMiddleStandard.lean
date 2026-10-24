module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexLastRawRatio
public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexCoefficientValues
public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedMorphismUniversalActionPrecomp
/-!
概要：元の中間係数を標準 fiber へ戻し、同じ最後辺の比を元の作用比較で読む。
方針：実 fiber の包含で全係数射を照合し、同じ比の全初期値による制限へ代入する。
規約：元の中間係数・第一射の全作用・最後辺の指定値を保持する。
使われ方：Ncomp の標準最後射の値と中間比較の貼り合わせ。
-/

@[expose] public section
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T
local notation "K₁" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 1))
local notation "P" => CategoryTheory.Functor.map SSet.uliftFunctor
  (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 2 s))))
local notation "C" => pointedCoherentFiberComparison K₁ ≫
  eqToHom (congrArg (vertexFiber pointedSpaceProjection)
    (Eq.symm (spaceInfinityVertex_eq_coherent K₁)))
/-- 概要：元の中間係数を標準 fiber に移すと、元の第一射の全係数作用になる。
方針：同じ実 fiber 包含と中間頂点式で照合する。
規約：全係数を保持。使われ方：最後辺の比の標準表示。 -/
lemma coherentColimitApexMiddleCoefficientMap_standard :
    coherentColimitApexMiddleCoefficientMap B T ≫
      eqToHom (congrArg (vertexFiber pointedSpaceProjection)
        (coherentColimitApex_raw_one_vertex B T)) =
      P ≫ C := by
  apply (cancel_mono (vertexFiberι pointedSpaceProjection (spaceInfinityVertex K₁))).mp
  simp only [Category.assoc]
  rw [vertexFiberTransport_ι pointedSpaceProjection (coherentColimitApex_raw_one_vertex B T),
    coherentColimitApexMiddleCoefficientMap_ι]
  rw [vertexFiberTransport_ι pointedSpaceProjection (spaceInfinityVertex_eq_coherent K₁).symm]
  exact spaceTrianglePointedFamily_middle_action s
local notation "g" => coherentEdgeHom (SpaceInfinity.δ 0 s)
/-- 概要：中間係数での元の raw 比は、同じ標準係数での元の作用比較。
方針：実中間係数を標準 fiber へ移して同じ比の比較を制限する。
規約：元の指定値を保持。使われ方：標準最後射の評価値との照合。 -/
lemma coherentColimitApexLastRawValueRatio_middle_heq_standard :
    HEq ((coherentColimitApexLastRawValueRatio B T).precomp
        (coherentColimitApexMiddleCoefficientMap B T))
      ((pointedValueMorphismUniversalActionIso g).precomp (P ≫ C)) := by
  have h := pointedMorphismEdgeValueRatio_precomp_heq_action g (coherentColimitRawSpaceEdge B b)
    (coherentColimitApex_raw_one_vertex B T) (coherentColimitApex_raw_two_vertex B T)
    ((coherentColimitRawSpaceEdge_last B a T).trans
      (pointedRightMorphismEdge_recover (SpaceInfinity.δ 0 s)).symm)
    (coherentColimitApexMiddleCoefficientMap B T)
  exact h.trans (functorIso_precomp_heq_of_map_eq (pointedValueMorphismUniversalActionIso g)
    (coherentColimitApexMiddleCoefficientMap_standard B T))
local notation "K₂" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "Y" => CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj K₂)
/-- 概要：中間係数での同じ raw 比は、元の最後射の作用比較の同じ二段前作用。
方針：標準 fiber 表示と元の第一射の係数作用を合成する。
規約：全係数と指定値を保持。使われ方：最後射の元の評価比較の回収。 -/
lemma coherentColimitApexLastRawValueRatio_middle_heq_pre_action :
    HEq ((coherentColimitApexLastRawValueRatio B T).precomp
        (coherentColimitApexMiddleCoefficientMap B T))
      (VertexIso.map (VertexIso.map (pointedValueHomActionAt g) ((pre C).app Y))
        ((pre P).app Y)) :=
  (coherentColimitApexLastRawValueRatio_middle_heq_standard B T).trans
    (pointedValueMorphismUniversalActionIso_precomp_comp_heq_evaluation g C P)
end
end SerrePositivity.InfinityCategories.F2
