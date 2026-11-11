module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexMiddleStandard
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexZeroValueAt
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedMorphismRatioTargetVertex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalDiagramRestriction
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoSquareIdentity
/-!
概要：元の零面・最後指定対角値と比の三実頂点を、同じ最後射の値で照合する。
方針：同じ中間係数の値と、一般の実辺での native 終点式を使う。
規約：指定同型の HEq から端点を抽出しない。
使われ方：最後射の値比較と作用比較の同じ二因子の合成。
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
local notation "K₂" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "g" => coherentEdgeHom (SpaceInfinity.δ 0 s)
local notation "ug" => CategoryTheory.Functor.map SSet.uliftFunctor g
local notation "P" => CategoryTheory.Functor.map SSet.uliftFunctor
  (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 2 s))))
local notation "Q" => CategoryTheory.Functor.map SSet.uliftFunctor
  (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject g))
local notation "C" => pointedCoherentFiberComparison K₁ ≫
  eqToHom (congrArg (vertexFiber pointedSpaceProjection)
    (Eq.symm (spaceInfinityVertex_eq_coherent K₁)))
local notation "Vcoh" => pointedFiberValueTo (Eq.symm (spaceInfinityVertex_eq_coherent K₂))
local notation "V" => eqToHom (congrArg (vertexFiber pointedSpaceProjection)
  (Eq.symm (spaceInfinityVertex_eq_coherent K₂))) ≫
    QCatEquivalence.hom (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K₂))
local notation "Y" => CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj K₂)
local notation "m" => coherentColimitApexMiddleCoefficientMap B T
local notation "R" => coherentColimitApexLastRawValueRatio B T
/-- 概要：元の零面値の始点は同じ二段係数作用の値。
方針：元の値射の移送と前作用を照合。規約：実頂点を保持。使われ方：最後射の二因子。 -/
lemma coherentColimitApexZeroLastValue_source_vertex :
    functorVertex (((P ≫ Q) ≫ pointedCoherentFiberComparison K₂) ≫ Vcoh) =
      NatTrans.app ((pre P).app Y) (Opposite.op ⦋0⦌)
        (functorVertex ((Q ≫ pointedCoherentFiberComparison K₂) ≫ V)) := by
  rw [functorVertex_precomposition, pointedFiberValueTo_eq_cast]
  rfl
/-- 概要：元の中間の比の終点値は同じ作用比較の終点。
方針：一般実辺の native 値と標準係数を照合。規約：実終点を保持。使われ方：二因子合成。 -/
lemma coherentColimitApexLastMiddleRatio_action_target_vertex :
    functorVertex (m ≫ (R).targetMap) =
      NatTrans.app ((pre P).app Y) (Opposite.op ⦋0⦌)
        (NatTrans.app ((pre C).app Y) (Opposite.op ⦋0⦌)
          ((pointedValueHomTransport K₁ K₂).app (Opposite.op ⦋0⦌)
            (ULift.up (functorVertex g)))) := by
  exact pointedMorphismEdgeValueRatio_target_vertex_of_standard g
    (coherentColimitRawSpaceEdge B b) (coherentColimitApex_raw_one_vertex B T)
    (coherentColimitApex_raw_two_vertex B T)
    ((coherentColimitRawSpaceEdge_last B a T).trans
      (pointedRightMorphismEdge_recover (SpaceInfinity.δ 0 s)).symm) m P
    (coherentColimitApexMiddleCoefficientMap_standard B T)
/-- 概要：元の中間の比の始点値は同じ作用比較の始点。
方針：元の中間係数の値を照合。規約：実始点と全係数を保持。使われ方：二因子合成。 -/
lemma coherentColimitApexLastMiddleRatio_action_source_vertex :
    functorVertex (m ≫ (R).sourceMap) =
      NatTrans.app ((pre P).app Y) (Opposite.op ⦋0⦌)
        (NatTrans.app ((pre C).app Y) (Opposite.op ⦋0⦌)
          (functorVertex
            ((pointedSpaceFiberValueEquivalence (spaceInfinityVertex K₁)).hom ≫ ug))) := by
  rw [functorVertex_precomposition, functorVertex_precomposition]
  apply congrArg functorVertex
  have h := congrArg (fun k => k ≫ ug) (coherentColimitApexMiddleCoefficientMap_value B T)
  convert h using 1 <;> rfl
end
end SerrePositivity.InfinityCategories.F2
