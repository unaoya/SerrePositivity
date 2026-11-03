module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexZeroValueAt
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexCompositeThroughMiddle
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceCompositionZeroLastValueFactor
/-!
概要：元の零面値と中間係数で読んだ最後対角値を、元の最後射値の前作用へ戻す。
方針：同じ実 native 値射で三端点を照合し、元の零面指定正方形へ移す。
規約：全初期係数・実辺・元の零面と対角値を保持する。
使われ方：Ncomp の同じ最後射の評価比較の回収。
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
local notation "K₂" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "m" => coherentColimitApexMiddleCoefficientMap B T
local notation "Vcoh" => pointedFiberValueTo (Eq.symm (spaceInfinityVertex_eq_coherent K₂))
local notation "V₂" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)
local notation "R" => coherentColimitApexLastRawValueRatio B T
local notation "g" => coherentEdgeHom (SpaceInfinity.δ 0 s)
local notation "P" => CategoryTheory.Functor.map SSet.uliftFunctor
  (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 2 s))))
local notation "Y" => CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj K₂)
/-- 概要：元の零面値と最後指定対角値の合成。方針：同じ実終点と中間表示を保持。
規約：元の指定値を保持。使われ方：最後射の値比較。 -/
def coherentColimitApexZeroLastMiddleValue :=
  coherentColimitApexZeroValueAt B T ≪≫ coherentColimitApexLastMiddleDiagonalValue B T
/-- 概要：同じ零面・最後対角値を元の零面正方形へ戻す。
方針：実 native 値射で三頂点を照合。規約：指定値を保持。使われ方：元の最後射値。 -/
lemma coherentColimitApexZeroLastMiddleValue_heq_zero_square :
    HEq (coherentColimitApexZeroLastMiddleValue B T)
      ((pointedOppositeTriangleFunctorIso s).postcomp Vcoh ≪≫
        (spaceCompositionZeroLastDiagonal s).postcomp Vcoh) := by
  have hD : HEq (coherentColimitApexLastMiddleDiagonalValue B T)
      ((spaceCompositionZeroLastDiagonal s).postcomp Vcoh) :=
    (functorIsoOfEq_heq _ _ _).trans
      (coherentColimitApexZeroLastDiagonal_post_value_heq_original B T).symm
  have ht : m ≫ (R).targetMap =
      FunctorIso.targetMap (spaceCompositionZeroLastDiagonal s) ≫ Vcoh :=
    ((coherentColimitApexZeroLastNative_value_eq_original B T).trans
      (coherentColimitApexLastDiagonalValue_target_eq_middle_ratio B T)).symm
  exact vertexIso_trans_heq_of_heq (coherentColimitApexZeroValueAt B T)
    (coherentColimitApexLastMiddleDiagonalValue B T)
    ((pointedOppositeTriangleFunctorIso s).postcomp Vcoh)
    ((spaceCompositionZeroLastDiagonal s).postcomp Vcoh) rfl
    (congrArg functorVertex (coherentColimitApexZeroValue_target_eq_original B T).symm)
    (congrArg functorVertex ht) (coherentColimitApexZeroValueAt_heq_original B T) hD
/-- 概要：同じ零面・最後対角値は元の最後射の値比較の第一射係数作用像。
方針：同じ零面正方形の値照合を合成。規約：全係数を保持。使われ方：最後射評価。 -/
lemma coherentColimitApexZeroLastMiddleValue_heq_morphism_pre_action :
    HEq (coherentColimitApexZeroLastMiddleValue B T)
      (VertexIso.map (pointedHomMorphismValueComparison g) ((pre P).app Y)) :=
  spaceCompositionZeroLastValue_heq_morphism_pre_action_of_heq s _
    (coherentColimitApexZeroLastMiddleValue_heq_zero_square B T)
end
end SerrePositivity.InfinityCategories.F2
