module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionStandardLastMorphismValue
/-!
概要：零面の元の値と最後指定対角値は、同じ最後射の元の値比較の前作用となる。
方針：元の指定正方形を同じ値射へ写し、最大化側の実 prism の値を回収する。
規約：全初期係数・零面の指定値と元の実最後辺を保持する。
使われ方：Ncomp の元の零面値と最後射の評価への接続。
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
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "K₂" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "g" => coherentEdgeHom (SpaceInfinity.δ 0 s)
local notation "P" => CategoryTheory.Functor.map SSet.uliftFunctor
  (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 2 s))))
local notation "V" => pointedFiberValueTo (Eq.symm (spaceInfinityVertex_eq_coherent K₂))
local notation "Y" => CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj K₂)
/-- 概要：元の零面値と最後対角値は同じ最後射の値比較の前作用。
方針：同じ指定正方形を値へ移す。
規約：全係数と指定値を保持。使われ方：最後射の元の評価比較。 -/
lemma spaceCompositionZeroLastValue_heq_morphism_pre_action :
    HEq ((pointedOppositeTriangleFunctorIso s).postcomp V ≪≫
        (spaceCompositionZeroLastDiagonal s).postcomp V)
      (VertexIso.map (pointedHomMorphismValueComparison g) ((pre P).app Y)) := by
  have h := congrArg (fun e => FunctorIso.postcomp e V)
    (spaceCompositionZeroLastSpecified_zero_square s)
  rw [functorIso_postcomp_trans] at h
  exact (heq_of_eq h).trans (spaceCompositionStandardLastValue_heq_morphism_pre_action s)
/-- 概要：同じ零面値と指定対角値の照合を元の最後射の値比較へ続ける。
方針：一般の全単体で同じ指定値照合を先に合成する。
規約：元の合成値を保持。使われ方：Apex の実値表示への代入。 -/
lemma spaceCompositionZeroLastValue_heq_morphism_pre_action_of_heq
    {W : Sort _} (R : W)
    (hR : HEq R ((pointedOppositeTriangleFunctorIso s).postcomp V ≪≫
      (spaceCompositionZeroLastDiagonal s).postcomp V)) :
    HEq R (VertexIso.map (pointedHomMorphismValueComparison g) ((pre P).app Y)) :=
  hR.trans (spaceCompositionZeroLastValue_heq_morphism_pre_action s)
end
end SerrePositivity.InfinityCategories.F2
