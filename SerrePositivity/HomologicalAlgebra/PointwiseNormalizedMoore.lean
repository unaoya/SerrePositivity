module
public import SerrePositivity.HomologicalAlgebra.NormalizedMooreMapFunctorNaturality
public import SerrePositivity.HomologicalAlgebra.FunctorComplexExchange
public import Mathlib.CategoryTheory.Functor.Currying
/-!
概要：図式圏のMoore正規化と同じ対象ごとの正規化を比較する。
方針：指定Moore比較を評価関手に適用し、関手・対象の両自然性で束ねる。
規約：IS-W2 A12の正規化照合の証明分割。元のMoore包含と射影を保持する。
使われ方：HA 1.2.4、線形BK重みから指定自由鎖図式への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex AlgebraicTopology
namespace SerrePositivity.HomologicalAlgebra
variable (J : Type*) [Category* J] (C : Type*) [Category* C] [Abelian C]
/-- 図式圏で正規化し、同じ各対象の鎖複体を評価する関手。 -/
def diagramMooreFunctor : SimplicialObject (J ⥤ C) ⥤ J ⥤ ChainComplex C ℕ :=
  normalizedMooreComplex (J ⥤ C) ⋙ complexOfFunctorsToFunctorToComplex
/-- 単体方向と添字方向を交換してから各対象で正規化する関手。 -/
def pointwiseMooreFunctor : SimplicialObject (J ⥤ C) ⥤ J ⥤ ChainComplex C ℕ :=
  flipFunctor SimplexCategoryᵒᵖ J C ⋙
    (Functor.whiskeringRight J (SimplicialObject C) (ChainComplex C ℕ)).obj (normalizedMooreComplex C)
/-- 指定Moore包含・射影による全対象・全図式射の正規化比較。 -/
def pointwiseMooreIso : diagramMooreFunctor J C ≅ pointwiseMooreFunctor J C :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun j => normalizedMooreMapIso ((evaluation J C).obj j) X)
      (by
        intro i j f
        exact normalizedMooreMapHom_functor_naturality ((evaluation J C).map f) X))
    (by
      intro X Y f
      apply NatTrans.ext
      funext j
      exact normalizedMooreMapHom_naturality ((evaluation J C).obj j) f)
end SerrePositivity.HomologicalAlgebra
