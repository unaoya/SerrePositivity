module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexCoefficientValues
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexZeroLastValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceCompositionZeroValueIso
/-!
概要：元の零面値を、元の実終点の値を保つ同じ指定比較として読む。
方針：元の終点係数の値の等式だけで終点表示を移す。
規約：全初期係数・零面の元の値と実終点を保持する。
使われ方：元の raw 二辺値に続く Ncomp の零面値。
-/

@[expose] public section
open CategoryTheory SSet
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
local notation "Vcoh" => pointedFiberValueTo (Eq.symm (spaceInfinityVertex_eq_coherent K₂))
local notation "V₂" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)
local notation "P" => CategoryTheory.Functor.map SSet.uliftFunctor
  (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 2 s))))
local notation "Q" => CategoryTheory.Functor.map SSet.uliftFunctor
  (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 0 s))))
local notation "D" => CategoryTheory.Functor.map SSet.uliftFunctor
  (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 1 s))))
/-- 概要：元の零面値の終点は元の実終点係数の同じ値。
方針：同じ終点係数と値射を照合する。
規約：元の実終点を保持。使われ方：raw 二辺値の始点表示。 -/
lemma coherentColimitApexZeroValue_target_eq_original :
    (D ≫ pointedCoherentFiberComparison K₂) ≫ Vcoh =
      coherentColimitApexTargetCoefficientMap B T ≫ V₂ := by
  rw [pointedFiberValueTo_eq_cast]
  exact (coherentColimitApexTargetCoefficientMap_value B T).symm

/-- 概要：元の実終点の値へ戻した同じ零面の指定比較。
方針：終点表示だけを移す。規約：元の全係数と指定値を保持。
使われ方：Ncomp の元の二辺値への接続。 -/
def coherentColimitApexZeroValueAt :
    FunctorIso (((P ≫ Q) ≫ pointedCoherentFiberComparison K₂) ≫ Vcoh)
      (coherentColimitApexTargetCoefficientMap B T ≫ V₂) :=
  functorIsoOfEq ((pointedOppositeTriangleFunctorIso s).postcomp Vcoh) rfl
    (coherentColimitApexZeroValue_target_eq_original B T)
/-- 概要：元の実終点表示でも同じ零面値を保持する。
方針：終点表示の移送だけを除く。規約：指定値を保持。
使われ方：元の零面の指定正方形への帰還。 -/
lemma coherentColimitApexZeroValueAt_heq_original :
    HEq (coherentColimitApexZeroValueAt B T)
      ((pointedOppositeTriangleFunctorIso s).postcomp Vcoh) :=
  functorIsoOfEq_heq _ _ _
/-- 概要：実終点表示の零面値は元の零面指定値。方針：同じ正規化表示で読む。
規約：元の全係数と指定値を保持。使われ方：Ncomp の元の零面値への帰還。 -/
lemma coherentColimitApexZeroValueAt_heq_zero_value :
    HEq (coherentColimitApexZeroValueAt B T) (spaceCompositionZeroValueIso s Vcoh) :=
  coherentColimitApexZeroValueAt_heq_original B T
end
end SerrePositivity.InfinityCategories.F2
